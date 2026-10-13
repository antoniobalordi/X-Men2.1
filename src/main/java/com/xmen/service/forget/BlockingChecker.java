package com.xmen.service.forget;

import com.xmen.model.*;
import com.xmen.service.derivation.DerivationRules;
import com.xmen.service.derivation.DolevYaoDeducer;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

/**
 * BlockingChecker implements the three blocking cases of Definition 6:
 * - Case 1 (weak): h is blocked if h ∈ Forget
 * - Case 2 (medium): h is blocked if Forget ⊢ h using only the pairing rules (r_pair, r_unpair)
 * - Case 3 (strong): h is blocked if Forget ⊢ h using all Dolev-Yao rules
 *
 * The closures of Cases 2 and 3 are decided exactly by {@link DolevYaoDeducer}.
 * Forgotten inference rules (Definition 5) are checked by {@link #forgottenRulesUsed}.
 */
@Slf4j
@Component
public class BlockingChecker {

    /** Function symbols declared [private] in the loaded theory (cannot be composed). */
    private Set<String> privateFunctions = Set.of();

    public void setPrivateFunctions(Set<String> privateFunctions) {
        this.privateFunctions = privateFunctions == null ? Set.of() : Set.copyOf(privateFunctions);
    }

    /**
     * Checks if a hypothesis h is blocked according to the context's blocking mode.
     *
     * @param h the hypothesis to check
     * @param ctx the forget context
     * @return true if h is blocked, false otherwise
     */
    public boolean isBlocked(Message h, ForgetContext ctx) {
        if (h == null || ctx == null) return false;

        return switch (ctx.getBlockingMode()) {
            case CASE1_WEAK -> ctx.getForgetSet().contains(h);
            case CASE2_PAIRING -> deducer().derivable(h, ctx.getForgetSet(), DolevYaoDeducer.PAIRING_RULES);
            case CASE3_FULL_DY -> deducer().derivable(h, ctx.getForgetSet(), DolevYaoDeducer.ALL_RULES);
        };
    }

    private DolevYaoDeducer deducer() {
        return new DolevYaoDeducer(privateFunctions);
    }

    /**
     * Extracts the hypotheses (leaves/initial terms) from a derivation tree.
     * Hypotheses are the terms taken directly from knowledge without further derivation.
     *
     * Per paper: hypotheses are leaf facts/terms used from knowledge.
     * Only "Initial" nodes are true hypotheses. Projection/Decryption nodes
     * now include their source term (pair/ciphertext) as an Initial premise.
     */
    public Set<Message> extractHypotheses(Derivation derivation) {
        Set<Message> hypotheses = new LinkedHashSet<>();
        extractHypothesesRecursive(derivation, hypotheses);
        return hypotheses;
    }

    private void extractHypothesesRecursive(Derivation node, Set<Message> hypotheses) {
        if (node == null) return;

        // "Initial" rule means this is a hypothesis from knowledge
        if ("Initial".equals(node.getRule())) {
            hypotheses.add(node.getGoal());
            return;
        }

        // For empty premises, only treat as hypothesis if rule is Initial
        // (non-Initial nodes with empty premises are unusual but should recurse)
        if (node.getPremises().isEmpty() && !"Initial".equals(node.getRule())) {
            // This shouldn't happen after fixes, but handle gracefully
            // Do NOT add as hypothesis - it's a derivation step, not a leaf
            return;
        }

        // Recurse into premises to find the actual Initial leaves
        for (Derivation premise : node.getPremises()) {
            extractHypothesesRecursive(premise, hypotheses);
        }
    }

    /**
     * Finds all blocked hypotheses in a derivation.
     */
    public Set<Message> findBlockedHypotheses(Derivation derivation, ForgetContext ctx) {
        Set<Message> hypotheses = extractHypotheses(derivation);
        Set<Message> blocked = new LinkedHashSet<>();

        for (Message h : hypotheses) {
            if (isBlocked(h, ctx)) {
                blocked.add(h);
            }
        }

        return blocked;
    }

    /**
     * Checks if a derivation has any blocked hypotheses.
     */
    public boolean hasBlockedHypotheses(Derivation derivation, ForgetContext ctx) {
        return !findBlockedHypotheses(derivation, ctx).isEmpty();
    }

    /** {@code Rules(π) ∩ R̄_H}: the forgotten inference rules a derivation needs (Definition 5). */
    public Set<InferenceRule> forgottenRulesUsed(Derivation derivation, ForgetContext ctx) {
        Set<InferenceRule> used = new TreeSet<>(DerivationRules.rulesOf(derivation));
        used.retainAll(ctx.getForgottenRules());
        return used;
    }

    /**
     * A derivation is usable under forgetting iff none of its hypotheses is blocked
     * (Definition 7) and it applies no forgotten rule (Definition 5).
     */
    public boolean isUsable(Derivation derivation, ForgetContext ctx) {
        return !hasBlockedHypotheses(derivation, ctx) && forgottenRulesUsed(derivation, ctx).isEmpty();
    }
}

