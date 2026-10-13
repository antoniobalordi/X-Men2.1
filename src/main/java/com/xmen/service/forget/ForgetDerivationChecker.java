package com.xmen.service.forget;

import com.xmen.model.Derivation;
import com.xmen.model.Function;
import com.xmen.model.InferenceRule;
import com.xmen.model.Message;
import com.xmen.service.derivation.DerivationConfig;
import com.xmen.service.derivation.DolevYaoDeducer;
import com.xmen.service.derivation.NormalDerivationEnumerator;
import com.xmen.service.impl.DerivationServiceImpl;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * ForgetDerivationChecker implements the core derivation checking for Algorithm 1:
 * - Checks if a target is derivable under forgetting: some normal derivation has no blocked
 *   hypothesis (Definition 7) and applies no forgotten rule (Definition 5). This decision is
 *   exact ({@link DolevYaoDeducer}) and does not depend on the enumeration limits.
 * - Enumerates the normal derivations Π (needed for the REPLACE branch and for the report),
 *   reporting when depth/count limits truncated the enumeration.
 */
@Slf4j
@Component
public class ForgetDerivationChecker {

    private static final int DEFAULT_DEPTH_LIMIT = 10;
    private static final int MAX_DERIVATIONS = 50; // Cap derivation enumeration

    @Autowired
    private BlockingChecker blockingChecker;

    @Autowired
    @Qualifier("derivationServiceImpl")
    private DerivationServiceImpl derivationService;

    /** Current user-defined functions (non-decomposable) */
    private Set<String> userDefinedFunctions = new HashSet<>();

    /** Function symbols declared [private] in the loaded theory (cannot be composed). */
    private Set<String> privateFunctions = new HashSet<>();

    /**
     * Active depth / derivation caps. Initialised to the safe defaults; a controller
     * can override these per-request (e.g. when the user selects "Infinite" in the
     * UI) via {@link #overrideLimits(int, int)} and must call {@link #resetLimits()}
     * in a finally block so the next request starts from the defaults again.
     */
    private int depthLimit = DEFAULT_DEPTH_LIMIT;
    private int maxDerivations = MAX_DERIVATIONS;

    /**
     * Lift (or tighten) the derivation caps for the current request. Pass
     * {@link Integer#MAX_VALUE} for both arguments to honor an "Infinite"
     * selection from the UI — the derivation engine will then attempt unbounded
     * exploration, which is allowed to OOM / stack-overflow on self-feeding
     * inputs (that's the whole point of the Infinite mode).
     */
    public void overrideLimits(int newDepth, int newMax) {
        this.depthLimit = newDepth;
        this.maxDerivations = newMax;
        refreshConfig();
        log.info("Derivation limits overridden: depth={}, maxDerivations={}",
                 newDepth, newMax);
    }

    /** Restore the static defaults. Call from controller `finally` blocks. */
    public void resetLimits() {
        this.depthLimit = DEFAULT_DEPTH_LIMIT;
        this.maxDerivations = MAX_DERIVATIONS;
        refreshConfig();
    }

    private void refreshConfig() {
        DerivationConfig config = new DerivationConfig(
            this.userDefinedFunctions,
            this.privateFunctions,
            this.maxDerivations,
            this.depthLimit
        );
        derivationService.setConfig(config);
        if (blockingChecker != null) {
            blockingChecker.setPrivateFunctions(this.privateFunctions);
        }
    }

    /** Function symbols declared {@code [private]} in the theory; they cannot be composed. */
    public void configurePrivateFunctions(Set<String> functions) {
        this.privateFunctions = new HashSet<>();
        if (functions != null) {
            for (String f : functions) {
                if (f != null) this.privateFunctions.add(f.toLowerCase().trim());
            }
        }
        refreshConfig();
    }

    /**
     * Configures the derivation checker with user-defined functions.
     * These functions will NOT be decomposed during derivation to prevent explosion.
     *
     * @param functions List of user-defined Function objects from the model
     */
    public void configureUserDefinedFunctions(List<Function> functions) {
        this.userDefinedFunctions.clear();
        if (functions != null) {
            for (Function f : functions) {
                if (f.getName() != null) {
                    this.userDefinedFunctions.add(f.getName().toLowerCase().trim());
                }
            }
        }

        // Reuse whatever depth/max are currently active (defaults unless a
        // controller has overridden them for this request).
        refreshConfig();

        log.info("Configured derivation checker with {} user-defined functions: {}",
                 userDefinedFunctions.size(), userDefinedFunctions);
    }

    /**
     * Checks if target m2 is derivable under forgetting: there EXISTS a normal derivation whose
     * hypotheses are all unblocked (Definition 7) and which applies no forgotten inference rule
     * (Definition 5, Algorithm 1 lines 16 and 47-48).
     *
     * <p>Equivalently, m2 is derivable from the non-blocked part of K using only non-forgotten
     * rules (removing the cycles of any such derivation yields a normal one with fewer hypotheses
     * and rules). This is decided exactly, independently of the enumeration limits.
     *
     * @param target the target message to derive (m2 - the send message)
     * @param ctx the forget context containing K, Forget and R̄
     * @return true if an unblocked derivation exists, false otherwise
     */
    public boolean derivableUnderForgetting(Message target, ForgetContext ctx) {
        if (target == null || ctx == null) {
            log.warn("Null target or context in derivableUnderForgetting");
            return false;
        }
        return derivable(target, ctx, ctx.getForgottenRules());
    }

    /**
     * Like {@link #derivableUnderForgetting} but with an explicit set of forgotten rules (used to
     * compare the situation before and after a procedural lapse).
     */
    public boolean derivable(Message target, ForgetContext ctx, Set<InferenceRule> forgottenRules) {
        List<Message> usable = new ArrayList<>();
        for (Message h : ctx.getDerivationKnowledge()) {
            if (!blockingChecker.isBlocked(h, ctx)) usable.add(h);
        }
        boolean result = new DolevYaoDeducer(privateFunctions)
            .derivable(target, usable, DolevYaoDeducer.excluding(forgottenRules));
        log.info("Derivable under forgetting: {} -> {} (Forget={}, forgotten rules={})",
                 target.represent(), result,
                 ctx.getForgetSet().stream().map(Message::represent).toList(), forgottenRules);
        return result;
    }

    /**
     * Enumerates the normal derivations of {@code target} from {@code knowledge} with the active
     * limits, reporting truncation.
     */
    public NormalDerivationEnumerator.Result enumerate(Message target, Set<Message> knowledge) {
        if (target == null || knowledge == null) {
            return new NormalDerivationEnumerator.Result(Collections.emptySet(), false);
        }
        NormalDerivationEnumerator.Result r = derivationService.enumerate(target, knowledge, this.depthLimit);
        if (r.derivations().size() > this.maxDerivations) {
            log.warn("Truncating derivations from {} to {}", r.derivations().size(), this.maxDerivations);
            Set<Derivation> truncated = new LinkedHashSet<>();
            for (Derivation d : r.derivations()) {
                if (truncated.size() >= this.maxDerivations) break;
                truncated.add(d);
            }
            return new NormalDerivationEnumerator.Result(truncated, true);
        }
        if (r.truncated()) {
            log.warn("Derivation enumeration for {} hit the depth/count limits; the set of derivations "
                     + "may be incomplete (the derivability decision itself is exact)", target.represent());
        }
        return r;
    }

    /**
     * Gets all derivations for a target from knowledge.
     * Uses the Java derivation service to enumerate derivations.
     */
    public Set<Derivation> getAllDerivations(Message target, Set<Message> knowledge) {
        try {
            return enumerate(target, knowledge).derivations();
        } catch (Exception e) {
            log.error("Error getting derivations for target {}: {}", target == null ? null : target.represent(), e.getMessage());
            return Collections.emptySet();
        }
    }

    /**
     * Visualisation helper: runs the derivation engine for {@code target} from
     * {@code displayKnowledge} purely to render the derivation tree to stdout
     * (which is captured into the forget-mutation ZIP's _DerivationTree.txt by
     * DerivationTreeCaptureService). The returned derivations are discarded —
     * this method must NOT be used to drive mutation analysis. The caller is
     * expected to pass an enriched knowledge set so the printed tree is
     * informative; the mutation pipeline keeps using its own (transition-aware)
     * knowledge via {@link #getAllDerivations}.
     */
    public void printDerivationTree(Message target, Set<Message> displayKnowledge) {
        if (target == null || displayKnowledge == null) {
            return;
        }
        try {
            derivationService.deriveToDepth(target, displayKnowledge, this.depthLimit);
        } catch (Exception e) {
            log.error("Error rendering derivation tree for target {}: {}",
                      target.represent(), e.getMessage());
        }
    }

    /**
     * Finds a specific unblocked derivation if one exists.
     * Used when we need to inspect the derivation structure.
     */
    public Optional<Derivation> findUnblockedDerivation(Message target, ForgetContext ctx) {
        Set<Derivation> derivations = getAllDerivations(target, ctx.getKnowledge());

        for (Derivation derivation : derivations) {
            if (blockingChecker.isUsable(derivation, ctx)) {
                return Optional.of(derivation);
            }
        }

        return Optional.empty();
    }

    /**
     * Gets all derivations that have blocked hypotheses (need mutation).
     */
    public List<Derivation> getDerivationsWithBlockedHypotheses(Message target, ForgetContext ctx) {
        Set<Derivation> derivations = getAllDerivations(target, ctx.getKnowledge());
        List<Derivation> blocked = new ArrayList<>();

        for (Derivation derivation : derivations) {
            if (!blockingChecker.isUsable(derivation, ctx)) {
                blocked.add(derivation);
            }
        }

        return blocked;
    }

    /**
     * Collects all unique blocked hypotheses across all derivations.
     */
    public Set<Message> collectAllBlockedHypotheses(Message target, ForgetContext ctx) {
        Set<Message> allBlocked = new LinkedHashSet<>();
        Set<Derivation> derivations = getAllDerivations(target, ctx.getKnowledge());

        for (Derivation derivation : derivations) {
            allBlocked.addAll(blockingChecker.findBlockedHypotheses(derivation, ctx));
        }

        return allBlocked;
    }
}

