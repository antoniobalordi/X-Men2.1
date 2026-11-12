package com.xmen.service.impl;

import com.xmen.model.*;
import com.xmen.service.DerivationCheckService;
import com.xmen.service.DerivationService;
import com.xmen.service.MutationStrategy;
import com.xmen.service.derivation.DerivationRules;
import com.xmen.service.derivation.NormalDerivationEnumerator;
import com.xmen.service.derivation.TamarinTermPrinter;
import com.xmen.service.forget.BlockingChecker;
import com.xmen.service.forget.ForgetContext;
import com.xmen.service.forget.ForgetContext.BlockingMode;
import com.xmen.service.forget.ForgetDerivationChecker;
import com.xmen.service.forget.ForgetRun;
import com.xmen.service.forget.ReplacementComputer;
import com.xmen.utilities.SetupKnowledgeExtractor;
import com.xmen.utilities.UtilityFunctions;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.*;

/**
 * ForgetMutationStrategy implements Algorithm 1 of the journal manuscript (version of November
 * 2026: Phase 1 updates K, Forget and R̄; Phase 2 applies the effect of every lapse so far):
 * - Maintains K (knowledge) as monotonic (never shrinks)
 * - Tracks the Forget set (forgotten messages) and R̄ (forgotten inference rules) separately
 * - Atomic forgetting: Forget(m) annotations (Definition 4, cases 1-2)
 * - Procedural forgetting: ForgetRule(r) annotations (Definition 4 case 3, Definition 5) —
 *   derivations applying a forgotten rule are unusable
 * - Applied at every human transition after the first lapse: lapses persist and accumulate in
 *   one mutated specification per run (see {@link ForgetRun})
 * - Checks for usable derivations before mutating (exact decision, see ForgetDerivationChecker)
 * - REPLACE: replaces the atomic components of m2 that H cannot derive under forgetting —
 *   forgotten, never added, or obtainable only with a forgotten rule — by admissible values of K
 *   (lines 28-40); a forgotten rule therefore triggers REPLACE when it leaves a component of m2
 *   underivable, and SKIP when it is needed to build m2 itself
 * - Removes send + matching receive when no variants exist
 *
 * Supports three blocking cases:
 * - Case 1 (weak): h blocked if h ∈ Forget
 * - Case 2 (medium): h blocked if derivable from Forget via pairing rules only
 * - Case 3 (strong): h blocked if derivable from Forget via all DY rules
 */
@Slf4j
@Service
public class ForgetMutationStrategy implements MutationStrategy {

  // Override-able set; resolved lazily from the live CeremonyVocabulary on each access
  // so users can re-target X-Men at a different naming convention at runtime.
  private Set<String> nonInternalActionsOverride;

  public Set<String> getNonInternalActions() {
    return Collections.unmodifiableSet(currentNonInternalActions());
  }

  public void setNonInternalActions(Set<String> newSet) {
    this.nonInternalActionsOverride = (newSet == null) ? null : new HashSet<>(newSet);
  }

  public void addWitnessActions(Collection<String> witnessNames) {
    if (witnessNames == null || witnessNames.isEmpty()) return;
    Set<String> base = new HashSet<>(currentNonInternalActions());
    base.addAll(witnessNames);
    this.nonInternalActionsOverride = base;
  }

  /** Live view: the override if set, otherwise the configured vocabulary. */
  private Set<String> currentNonInternalActions() {
    if (nonInternalActionsOverride != null) return nonInternalActionsOverride;
    if (vocabulary != null) return vocabulary.nonInternalActions();
    // Fallback for unit tests or contexts where the bean wasn't injected.
    return new HashSet<>(Set.of(
        "Send", "Receive", "To", "H", "Fr", "Setup", "OnlyOnce", "Neq", "Roles",
        "ChanSndS", "ChanRcvS", "Hfin", "Forget"));
  }

  /* ------------------------------------------------------------------ */
  /* Vocabulary-driven name checks. Every fact / action name match in   */
  /* this strategy must go through one of these so the tool can be      */
  /* re-targeted at any valid Tamarin file via the Settings vocabulary. */
  /* ------------------------------------------------------------------ */

  private boolean isOutboundFact(String name) {
    if (name == null) return false;
    if (vocabulary != null) return vocabulary.isOutboundChannel(name);
    return "Out".equals(name) || "SndS".equals(name);
  }

  private boolean isInboundFact(String name) {
    if (name == null) return false;
    if (vocabulary != null) return vocabulary.isInboundChannel(name);
    return "In".equals(name) || "RcvS".equals(name);
  }

  private boolean isStateFact(String name) {
    if (name == null) return false;
    if (vocabulary != null) return vocabulary.isStateFact(name);
    return "State".equals(name);
  }

  private boolean isSendAction(String name) {
    if (name == null) return false;
    if (vocabulary != null) return vocabulary.isSendAction(name);
    return "Send".equals(name);
  }

  private boolean isReceiveAction(String name) {
    if (name == null) return false;
    if (vocabulary != null) return vocabulary.isReceiveAction(name);
    return "Receive".equals(name);
  }

  private boolean isForgetAction(String name) {
    if (name == null) return false;
    if (vocabulary != null) return vocabulary.isForgetAction(name);
    return "Forget".equals(name);
  }

  @Autowired private DerivationCheckService derivationCheckService;
  @Autowired private SetupKnowledgeExtractor setupKnowledgeExtractor;
  @Autowired private DerivationService derivationService;
  @Autowired private UtilityFunctions utilityFunctions;
  @Autowired private ForgetDerivationChecker forgetDerivationChecker;
  @Autowired private BlockingChecker blockingChecker;
  @Autowired private ReplacementComputer replacementComputer;

  @Autowired(required = false)
  private com.xmen.config.CeremonyVocabulary vocabulary;

  // Default blocking mode - can be configured
  private BlockingMode blockingMode = BlockingMode.CASE1_WEAK;
  private int maxVariantsPerRule = 10;

  public int getMaxVariantsPerRule() {
    return maxVariantsPerRule;
  }

  public void setMaxVariantsPerRule(int maxVariantsPerRule) {
    this.maxVariantsPerRule = maxVariantsPerRule;
  }

  public BlockingMode getBlockingMode() {
    return blockingMode;
  }

  public void setBlockingMode(BlockingMode blockingMode) {
    this.blockingMode = blockingMode;
  }

  /**
   * Applies the FORGET mutation to one human transition, following Algorithm 1 of the journal
   * manuscript (version of November 2026).
   *
   * <p>Lapses are declared by annotations on human rules: {@code Forget(m)} (Definition 4, cases 1
   * and 2) and {@code ForgetRule(r)} (case 3). Before the first lapse only the knowledge is tracked.
   * The first lapse starts a run (one mutated specification and the human's context K, Forget,
   * R̄); from then on Algorithm 1 is applied to <em>every</em> human transition of the run, so an
   * earlier lapse also affects later sends and checks, and all lapses of the input accumulate in
   * the same mutated specification. A REPLACE with several variants branches the run; each run
   * is one output theory.
   *
   * @param rule The human rule of the original specification (its name identifies the transition).
   * @param rules The original specification.
   * @param parametersBundle The parameters bundle; its collections receive the run theories.
   * @return The updated parameters bundle.
   */
  @Override
  public ParametersBundle applyMutation(
      Rule rule, ArrayList<Rule> rules, ParametersBundle parametersBundle) {

    // Configure derivation checker with user-defined functions
    if (parametersBundle.getFunctions() != null && !parametersBundle.getFunctions().isEmpty()) {
      forgetDerivationChecker.configureUserDefinedFunctions(parametersBundle.getFunctions());
    }
    forgetDerivationChecker.configurePrivateFunctions(parametersBundle.getPrivateFunctions());

    // Setup knowledge extraction (type mapping)
    Map<String, String> setup = parametersBundle.getExistingSetupKnowledge();
    if (setup == null || setup.isEmpty()) {
      setup = setupKnowledgeExtractor.processProtocolModel(rules);
      parametersBundle.setExistingSetupKnowledge(setup);
    }

    if (parametersBundle.getCollections() == null) {
      parametersBundle.setCollections(new ArrayList<>());
    }

    // Initialize or reuse transition-aware context
    ForgetContext ctx = parametersBundle.getForgetContext();
    if (ctx == null) {
      ctx = new ForgetContext(Collections.emptySet(), Collections.emptySet(), blockingMode, setup);
      parametersBundle.setForgetContext(ctx);
    } else if (ctx.getTypeMap().isEmpty()) {
      ctx.setTypeMap(setup);
    }

    String name = rule.getRule_name();
    // Forgetting is local to the human who lapses (Sec. "Defining the Forget mutation"): every
    // other agent, even one whose rules are marked H(), keeps all its knowledge and rules.
    String lapsingAgent = lapsingAgent(rules, parametersBundle);
    String agent = agentOf(rule);
    if (lapsingAgent != null && agent != null && !agent.equals(lapsingAgent)) {
      if (!forgottenMessagesAt(name, parametersBundle).isEmpty()
          || !forgottenRulesAt(name, parametersBundle).isEmpty()) {
        throw new IllegalArgumentException("Forget annotations on transitions of two agents ("
            + lapsingAgent + " and " + agent + " in rule " + name + ") are not supported: the "
            + "Forget mutation models the memory lapses of one human.");
      }
      return parametersBundle;
    }
    List<ForgetRun> runs = parametersBundle.getForgetRuns();
    List<ArrayList<Rule>> previousTheories = new ArrayList<>();
    if (runs == null) {
      if (forgottenMessagesAt(name, parametersBundle).isEmpty()
          && forgottenRulesAt(name, parametersBundle).isEmpty()) {
        // No lapse so far: K^{i+1} = K^i ∪ {m1} ∪ fresh (lines 17-19)
        ctx.addAllKnowledge(knowledgeAtState(rule));
        ctx.updateForTransition(extractReceivedMessage(rule), null);
        ctx.addAllKnowledge(freshValues(rule));
        return parametersBundle;
      }
      // The first lapse starts the run from the original specification.
      runs = List.of(new ForgetRun(deepCloneTheory(rules), ctx));
    } else {
      for (ForgetRun run : runs) previousTheories.add(run.theory());
    }

    List<ForgetRun> next = new ArrayList<>();
    for (int k = 0; k < runs.size(); k++) {
      ForgetRun run = runs.get(k);
      Rule current = findCurrentRule(run.theory(), name);
      if (current == null) {
        next.add(run);
        continue;
      }
      next.addAll(applyToTransition(current, name, run, parametersBundle, runs.size() > 1 ? k : -1));
    }

    parametersBundle.setForgetRuns(next);
    if (!next.isEmpty()) parametersBundle.setForgetContext(next.get(0).ctx());
    // Replace this mutation's theories in collections (other strategies' entries are kept).
    parametersBundle.getCollections().removeIf(c -> previousTheories.stream().anyMatch(p -> p == c));
    for (ForgetRun run : next) parametersBundle.getCollections().add(run.theory());
    return parametersBundle;
  }

  /**
   * Algorithm 1 on one transition of one run. {@code current} is the transition's rule in the
   * run's specification (already affected by the earlier mutations and their propagation).
   *
   * <ol>
   *   <li>Phase 1 (lines 2-20): K^i is the knowledge of the run; after a lapse a value of the
   *       pre-State payload belongs to K only if H can still obtain it. Then K^{i+1}, Forget^{i+1}
   *       and R̄^{i+1} are updated for the lapse of this transition, if any.</li>
   *   <li>Phase 2 (lines 21-44), for every lapse up to this transition: NEGLECT each internal
   *       action that the lapses make impossible; preserve the send if m2 is derivable under
   *       forgetting; otherwise REPLACE the underivable components of m2
   *       ({@link #computeComponentVariants}) or, if no variant is derivable, SKIP the send.</li>
   * </ol>
   *
   * <p>On a transition without a lapse of its own, only what the lapses broke is changed: a send
   * that is not derivable even without any lapse is left alone (incomplete knowledge extraction,
   * not an effect of forgetting).
   */
  private List<ForgetRun> applyToTransition(Rule current, String name, ForgetRun run,
                                            ParametersBundle parametersBundle, int runIndex) {
    ForgetContext ctx = run.ctx();
    Set<String> forgetSet = forgottenMessagesAt(name, parametersBundle);
    Set<InferenceRule> rulesForgottenNow = forgottenRulesAt(name, parametersBundle);
    boolean annotated = !forgetSet.isEmpty() || !rulesForgottenNow.isEmpty();
    for (String forgotten : forgetSet) {
      removeForgetMutation(current, canonicalize(forgotten));
    }

    // ===== Phase 1: K^i, then the lapse of this transition (lines 2-20) =====
    Set<Message> payload = statePayloadKnowledge(current);
    Set<Message> premises = premiseKnowledge(current);
    Message receivedMessage = extractReceivedMessage(current);
    Set<Message> fresh = freshValues(current);
    // The knowledge of this transition as if nothing had ever been forgotten.
    Set<Message> noLapseKnowledge = new LinkedHashSet<>(ctx.getDerivationKnowledge());
    noLapseKnowledge.addAll(payload);
    noLapseKnowledge.addAll(premises);
    if (receivedMessage != null) noLapseKnowledge.add(receivedMessage);
    noLapseKnowledge.addAll(fresh);

    ctx.addAllKnowledge(premises);
    Set<Message> unavailable = new LinkedHashSet<>();
    if (!ctx.hasLapsed()) {
      ctx.addAllKnowledge(payload);
    } else {
      for (Message value : payload) {
        if (ctx.getKnowledge().contains(value) || isPublicAtom(value)
            || forgetDerivationChecker.derivableUnderForgetting(value, ctx)) {
          ctx.addKnowledge(value);
        } else {
          unavailable.add(value); // never added (case 1) or obtainable only with a forgotten rule
        }
      }
    }

    List<Message> forgottenMessages = new ArrayList<>();
    for (String forgotten : forgetSet) {
      Message m = resolveForgetMessage(ctx.getKnowledge(), receivedMessage, forgotten);
      forgottenMessages.add(m);
      if (!m.equals(receivedMessage) && !ctx.getKnowledge().contains(m)) {
        log.warn("Forget({}) in rule {}: the message is not in the agent's knowledge K^i; "
                 + "it is recorded in the Forget set but cannot affect current derivations",
                 forgotten, current.getRule_name());
      }
    }
    boolean forgetsReceived = receivedMessage != null && forgottenMessages.contains(receivedMessage);
    // Re-acquisition candidates: Forget^i minus the messages forgotten again at this transition.
    List<Message> relearnCandidates = new ArrayList<>(ctx.getForgetSet());
    relearnCandidates.removeAll(forgottenMessages);
    // K^{i+1} = K^i ∪ {m1} unless H forgets m1; then the lapse of this transition
    ctx.updateForTransition(receivedMessage, forgetsReceived ? receivedMessage : null);
    for (Message m : forgottenMessages) {
      if (!m.equals(receivedMessage)) ctx.addForget(m);
    }
    for (InferenceRule r : rulesForgottenNow) ctx.forgetRule(r);
    // Re-acquisition (Algorithm 1, Phase 1; Example 3): if H takes in m1, every forgotten message
    // that has a normal derivation using m1, judged after the lapse of this transition, leaves the
    // Forget set (m1 itself included, when H receives a forgotten message again).
    if (receivedMessage != null && !forgetsReceived) {
      ctx.relearn(forgetDerivationChecker.relearnedBy(receivedMessage, relearnCandidates, ctx));
    }
    ctx.addAllKnowledge(fresh);
    unavailable.removeIf(v -> forgetDerivationChecker.derivableUnderForgetting(v, ctx));
    if (annotated) ctx.markLapsed();
    ForgetContext noLapse = new ForgetContext(noLapseKnowledge, Collections.emptySet(),
        Collections.emptySet(), ctx.getBlockingMode(), ctx.getTypeMap());

    log.info("Algorithm 1 - rule {}: forgotten messages {}, forgotten rules {}",
             current.getRule_name(), forgetSet, rulesForgottenNow);
    log.info("Knowledge K: {}", ctx.getKnowledge().stream().map(Message::represent).toList());
    log.info("Forget set: {}", ctx.getForgetSet().stream().map(Message::represent).toList());
    log.info("Forgotten rules: {}", ctx.getForgottenRules());
    log.info("Blocking mode: {}", ctx.getBlockingMode());

    // ===== Phase 2: NEGLECT (lines 21-24) =====
    Set<String> nonInternal = new HashSet<>(currentNonInternalActions());
    nonInternal.addAll(lemmaWitnessActions(parametersBundle));
    Set<String> actionsToNeglect = new LinkedHashSet<>();
    if (current.isHuman()) {
      for (Message forgottenMessage : forgottenMessages) {
        for (Fact action : isMessageUsedInInternalAction(current, forgottenMessage, nonInternal)) {
          log.info("Forget triggers Neglect on rule {}: internal action {} uses forgotten message {}",
                   current.getRule_name(), action.getF_name(), forgottenMessage.represent());
          actionsToNeglect.add(factSignature(action));
        }
      }
      for (Fact action : actionsMadeImpossible(current, noLapse, ctx, nonInternal)) {
        log.info("Forget triggers Neglect on rule {}: internal action {} needs forgotten information",
                 current.getRule_name(), action.getF_name());
        actionsToNeglect.add(factSignature(action));
      }
    }

    // Extract target message (m2 - the send message)
    Message target = derivationCheckService.extractTargetFromRule(current);
    if (target != null) {
      ctx.addPublicKnowledge(publicAtoms(target));
      noLapse.addPublicKnowledge(publicAtoms(target));
    }
    boolean preserved = target == null || forgetDerivationChecker.derivableUnderForgetting(target, ctx);
    if (!annotated && preserved && actionsToNeglect.isEmpty()) {
      return List.of(run); // the earlier lapses do not affect this transition
    }

    printAnalysisHeader(current, ctx, forgottenMessages, rulesForgottenNow, target, runIndex, unavailable);
    if (target == null) {
      // No outgoing m2: only Neglect applies.
      System.out.println("Decision: no send in this transition; NEGLECT of "
          + actionsToNeglect.size() + " internal action(s)");
      return List.of(new ForgetRun(withNeglect(run.theory(), current, actionsToNeglect), ctx));
    }
    log.info("Target message m2: {}", target.represent());

    // Report (captured into the zip's _DerivationTree.txt): the derivations Π of m2 from the
    // knowledge actually used by the analysis, and per derivation its blocked hypotheses and
    // forgotten rules.
    NormalDerivationEnumerator.Result enumeration =
        forgetDerivationChecker.enumerate(target, ctx.getDerivationKnowledge());
    forgetDerivationChecker.printDerivationTree(target, ctx.getDerivationKnowledge());
    printDerivationSummary(enumeration, ctx);

    // ===== Phase 2: send m2 (lines 25-27) =====
    if (preserved) {
      System.out.println("Decision: send preserved (some derivation of m2 has no blocked hypothesis "
          + "and uses no forgotten rule)");
      return List.of(new ForgetRun(withNeglect(run.theory(), current, actionsToNeglect), ctx));
    }

    // Π = ∅ even without any lapse: the extracted knowledge cannot reproduce the original send,
    // so Algorithm 1's precondition fails (this is not an effect of forgetting).
    boolean derivableAtAll = forgetDerivationChecker.derivable(target, noLapse, Collections.emptySet());
    if (!derivableAtAll) {
      log.warn("Algorithm 1 precondition violated in rule {}: m2 = {} is not derivable from K at all",
               current.getRule_name(), target.represent());
      System.out.println("WARNING: m2 is not derivable from K even without forgetting (Π = ∅); "
          + "the knowledge extracted from the specification is incomplete for this transition.");
      if (!annotated) {
        System.out.println("Decision: send unchanged (not an effect of the earlier lapses)");
        return List.of(new ForgetRun(withNeglect(run.theory(), current, actionsToNeglect), ctx));
      }
      if (!forgottenMessages.isEmpty() && ctx.getForgottenRules().isEmpty()) {
        return List.of(new ForgetRun(applyTextualFallback(current, run.theory(), ctx,
            forgottenMessages, target, actionsToNeglect), ctx));
      }
    }

    // ===== Phase 2: REPLACE (lines 28-40) =====
    List<VariantInfo> variants = derivableAtAll
        ? computeComponentVariants(target, ctx, parametersBundle, current)
        : new ArrayList<>();

    if (variants.isEmpty()) {
      // ===== SKIP (lines 41-43) =====
      System.out.println("Decision: SKIP the send (no surviving derivation and no admissible "
          + "replacement of the underivable components yields a derivable variant)");
      log.info("No usable derivation and no variant - removing send and matching receive");
      ArrayList<Rule> theoryClone = deepCloneTheory(run.theory());
      Rule startRule = findRuleByName(theoryClone, current.getRule_name());
      removeSendAndMatchingReceive(theoryClone, startRule, target);
      removeNeglectedActions(startRule, actionsToNeglect);
      markMutated(startRule, "_M");
      return List.of(new ForgetRun(theoryClone, ctx));
    }

    // Generate one run per variant
    System.out.println("Decision: REPLACE with " + variants.size() + " variant(s): "
        + variants.stream().map(v -> TamarinTermPrinter.print(v.variant)).toList());
    Set<String> witnesses = lemmaWitnessActions(parametersBundle);
    List<ForgetRun> out = new ArrayList<>();
    for (int i = 0; i < variants.size(); i++) {
      VariantInfo variantInfo = variants.get(i);
      ArrayList<Rule> theoryClone = deepCloneTheory(run.theory());
      Rule startRule = findRuleByName(theoryClone, current.getRule_name());
      applyVariantToRule(startRule, target, variantInfo.variant, variantInfo.replacement, witnesses);
      markMutated(startRule, variants.size() > 1 ? "_M" + i : "_M");
      removeNeglectedActions(startRule, actionsToNeglect);
      // Propagate changes to subsequent rules
      propagateMutationWithVariant(theoryClone, startRule, variantInfo.replacement);
      out.add(new ForgetRun(theoryClone, i == 0 ? ctx : ctx.copy()));
    }
    return out;
  }

  private Set<String> forgottenMessagesAt(String ruleName, ParametersBundle parametersBundle) {
    Set<String> s = parametersBundle.getForgetMutationSet().get(ruleName);
    return s == null ? Collections.emptySet() : s;
  }

  private Set<InferenceRule> forgottenRulesAt(String ruleName, ParametersBundle parametersBundle) {
    Set<InferenceRule> s = parametersBundle.getForgetRuleSet().get(ruleName);
    return s == null ? Collections.emptySet() : s;
  }

  /**
   * The agent of the first annotated human transition (the human whose lapses are modelled), or
   * null if it cannot be determined.
   */
  private String lapsingAgent(ArrayList<Rule> rules, ParametersBundle parametersBundle) {
    for (Rule r : rules) {
      if (!r.isHuman()) continue;
      if (!forgottenMessagesAt(r.getRule_name(), parametersBundle).isEmpty()
          || !forgottenRulesAt(r.getRule_name(), parametersBundle).isEmpty()) {
        return agentOf(r);
      }
    }
    return null;
  }

  /** The agent executing {@code rule}: the first argument of its State fact (premise first). */
  private String agentOf(Rule rule) {
    if (rule == null) return null;
    for (List<Fact> facts : List.of(rule.getPreconditions(), rule.getPostconditions())) {
      if (facts == null) continue;
      for (Fact f : facts) {
        if (isStateFact(f.getF_name()) && f.getParameters() != null && !f.getParameters().isEmpty()) {
          return canonicalize(paramToString(f.getParameters().get(0)).trim());
        }
      }
    }
    return null;
  }

  /** The rule of transition {@code name} in a run: same name, or the name with a mutation suffix. */
  private Rule findCurrentRule(ArrayList<Rule> theory, String name) {
    String mutated = java.util.regex.Pattern.quote(name) + "_M\\d*";
    for (Rule r : theory) {
      if (r.getRule_name().equals(name) || r.getRule_name().matches(mutated)) return r;
    }
    return null;
  }

  /** Marks a rule as mutated; a rule that already carries a mutation suffix keeps its name. */
  private void markMutated(Rule rule, String suffix) {
    if (!rule.getRule_name().matches(".*_M\\d*")) {
      rule.setRule_name(rule.getRule_name() + suffix);
    }
    rule.setTypo(Type.MUTATED);
  }

  /** The run's theory with the neglected internal actions of {@code current} removed. */
  private ArrayList<Rule> withNeglect(ArrayList<Rule> theory, Rule current, Set<String> actionsToNeglect) {
    if (actionsToNeglect.isEmpty()) return theory;
    ArrayList<Rule> theoryClone = deepCloneTheory(theory);
    Rule startRule = findRuleByName(theoryClone, current.getRule_name());
    removeNeglectedActions(startRule, actionsToNeglect);
    markMutated(startRule, "_M");
    return theoryClone;
  }

  private static boolean isPublicAtom(Message m) {
    return m instanceof Atom a && (a.getValue().startsWith("$") || a.getValue().startsWith("'"));
  }

  /**
   * REPLACE variants of Algorithm 1 (November 2026 version), lines 29-40.
   *
   * <p>U is the set of atomic submessages of m2 (Definition 2, {@link
   * ReplacementComputer#atomicSubmessages}) that H cannot derive under forgetting — whether they
   * were never added to K, are forgotten, or can only be obtained with a forgotten rule. Each
   * m̄ ∈ U gets Repl(m̄) (line 31); every combination C yields m2[C] (line 35), which triggers
   * REPLACE only if H can derive it under forgetting (line 36). If U is empty the only combination
   * is m2 itself, which is not derivable here, so no variant exists (e.g. a forgotten rule needed
   * to build m2, or an underivable value inside a key).
   */
  private List<VariantInfo> computeComponentVariants(Message target, ForgetContext ctx,
                                                     ParametersBundle parametersBundle, Rule rule) {
    List<Message> underivable = new ArrayList<>();
    for (Message component : ReplacementComputer.atomicSubmessages(target)) {
      if (!forgetDerivationChecker.derivableUnderForgetting(component, ctx)) {
        underivable.add(component);
      }
    }
    System.out.println("Underivable atomic components U: "
        + underivable.stream().map(TamarinTermPrinter::print).toList());
    List<List<Message>> replacementSets = new ArrayList<>();
    for (Message component : underivable) {
      Set<Message> replacements = replacementComputer.computeReplacementSet(component, ctx);
      System.out.println("Repl(" + TamarinTermPrinter.print(component) + "): "
          + replacements.stream().map(TamarinTermPrinter::print).toList());
      if (replacements.isEmpty()) {
        return new ArrayList<>(); // the product of line 34 is empty
      }
      replacementSets.add(new ArrayList<>(replacements));
    }
    Map<Message, VariantInfo> variants = new LinkedHashMap<>();
    int[] idx = new int[underivable.size()];
    while (true) {
      Map<Message, Message> chosen = new LinkedHashMap<>();
      for (int k = 0; k < idx.length; k++) {
        chosen.put(underivable.get(k), replacementSets.get(k).get(idx[k]));
      }
      Message variant = ReplacementComputer.substituteSubmessages(target, chosen);
      if (!variant.equals(target) && !variants.containsKey(variant)) {
        ctx.addPublicKnowledge(publicAtoms(variant));
        if (forgetDerivationChecker.derivableUnderForgetting(variant, ctx)) {
          if (variants.size() >= maxVariantsPerRule) {
            parametersBundle.setVariantsTruncated(true);
            log.warn("Reached maximum variants per rule ({}) for rule {} - truncating",
                     maxVariantsPerRule, rule.getRule_name());
            break;
          }
          variants.put(variant, new VariantInfo(variant, chosen));
        } else {
          System.out.println("Variant " + TamarinTermPrinter.print(variant)
              + " is not derivable under forgetting - dropped (line 36)");
        }
      }
      int k = idx.length - 1;
      while (k >= 0 && ++idx[k] == replacementSets.get(k).size()) {
        idx[k] = 0;
        k--;
      }
      if (k < 0) break;
    }
    return new ArrayList<>(variants.values());
  }

  /**
   * Legacy behaviour kept for the case where Algorithm 1 cannot be applied: m2 is not derivable
   * from the extracted knowledge at all (Π = ∅ before any forgetting). The forgotten name is
   * substituted textually by a type-compatible replacement, or the send is skipped when there is
   * none. This is not part of Algorithm 1 and is reported as such.
   */
  private ArrayList<Rule> applyTextualFallback(Rule rule, ArrayList<Rule> rules, ForgetContext ctx,
                                              List<Message> forgottenMessages,
                                              Message target, Set<String> actionsToNeglect) {
    Map<String, String> textualSub = new LinkedHashMap<>();
    for (Message forgottenMessage : forgottenMessages) {
      Set<Message> reps = replacementComputer.computeReplacementSet(forgottenMessage, ctx);
      if (reps.isEmpty()) {
        textualSub.clear();
        break; // a forgotten term has no replacement -> genuine skip
      }
      textualSub.put(canonicalize(forgottenMessage.represent()), canonicalize(reps.iterator().next().represent()));
    }
    System.out.println("Decision (legacy textual fallback, outside Algorithm 1): "
        + (textualSub.isEmpty() ? "SKIP" : "substitute " + textualSub));

    ArrayList<Rule> theoryClone = deepCloneTheory(rules);
    Rule startRule = findRuleByName(theoryClone, rule.getRule_name());
    if (startRule != null) {
      if (!textualSub.isEmpty()) {
        for (Fact action : startRule.getActions()) {
          if (!isForgetAction(action.getF_name())) {
            applyStringSubstitutionToFact(action, textualSub);
          }
        }
        for (Fact post : startRule.getPostconditions()) {
          if (!isStateFact(post.getF_name())) {
            applyStringSubstitutionToFact(post, textualSub);
          }
        }
      } else {
        removeSendAndMatchingReceive(theoryClone, startRule, target);
        removeNeglectedActions(startRule, actionsToNeglect);
      }
      markMutated(startRule, "_M");
    }
    return theoryClone;
  }

  /**
   * Internal actions the lapse makes impossible: some argument was derivable without blocked
   * hypotheses and forgotten rules in the successor state without the lapse, but is not derivable
   * after it. This is "m is used in a" (Algorithm 1, line 12) and "r is used in a" (line 44) read
   * as "needed for a" (Sec. 4.3: e.g. the human forgets the key needed to decrypt a message whose
   * content they must check). For forgotten messages the textual test
   * {@link #isMessageUsedInInternalAction} is applied as well.
   */
  private List<Fact> actionsMadeImpossible(Rule rule, ForgetContext withoutLapse, ForgetContext withLapse,
                                           Set<String> nonInternal) {
    List<Fact> out = new ArrayList<>();
    for (Fact action : rule.getActions()) {
      if (action == null || nonInternal.contains(action.getF_name())) continue;
      for (Object param : action.getParameters()) {
        Message arg = paramToMessage(param);
        if (arg == null) continue;
        withoutLapse.addPublicKnowledge(publicAtoms(arg));
        withLapse.addPublicKnowledge(publicAtoms(arg));
        if (forgetDerivationChecker.derivableUnderForgetting(arg, withoutLapse)
            && !forgetDerivationChecker.derivableUnderForgetting(arg, withLapse)) {
          out.add(action);
          break;
        }
      }
    }
    return out;
  }

  /**
   * Action facts used by the lemmas but by no restriction. In Tamarin such facts only label the
   * trace for the security properties (e.g. PasswordAttempt); they are not internal checks of
   * the role script, so NEGLECT does not apply to them, and a REPLACE mirrors the replacement in
   * them. Explicit Witness-Actions headers are handled by {@link #addWitnessActions}.
   */
  private Set<String> lemmaWitnessActions(ParametersBundle parametersBundle) {
    String postamble = parametersBundle.getExtraContent("postamble");
    if (postamble == null || postamble.isBlank()) return Collections.emptySet();
    Set<String> inLemmas = new LinkedHashSet<>();
    Set<String> inRestrictions = new HashSet<>();
    java.util.regex.Matcher block = java.util.regex.Pattern
        .compile("(?s)\\b(lemma|restriction)\\s+\\w+.*?(?=\\blemma\\s+\\w|\\brestriction\\s+\\w|\\z)")
        .matcher(postamble);
    java.util.regex.Pattern factName = java.util.regex.Pattern.compile("\\b([A-Z][A-Za-z0-9_]*)\\s*\\(");
    while (block.find()) {
      java.util.regex.Matcher f = factName.matcher(block.group());
      Set<String> target = block.group(1).equals("lemma") ? inLemmas : inRestrictions;
      while (f.find()) target.add(f.group(1));
    }
    inLemmas.removeAll(inRestrictions);
    inLemmas.remove("K");
    return inLemmas;
  }

  private void printAnalysisHeader(Rule rule, ForgetContext ctx, List<Message> forgottenMessages,
                                   Set<InferenceRule> forgottenRules, Message target, int runIndex,
                                   Set<Message> unavailable) {
    System.out.println();
    System.out.println("==================== Forget analysis: rule " + rule.getRule_name()
        + (runIndex >= 0 ? " (run " + runIndex + ")" : "") + " ====================");
    if (forgottenMessages.isEmpty() && forgottenRules.isEmpty()) {
      System.out.println("No lapse in this transition; effect of the lapses at earlier transitions");
    }
    if (!unavailable.isEmpty()) {
      System.out.println("Not available to H after the earlier lapses: "
          + unavailable.stream().map(TamarinTermPrinter::print).toList());
    }
    System.out.println("Lapse: forgotten messages " + forgottenMessages.stream()
        .map(TamarinTermPrinter::print).toList() + ", forgotten rules " + forgottenRules);
    System.out.println("Blocking case: " + ctx.getBlockingMode());
    System.out.println("K^{i+1}: " + ctx.getKnowledge().stream().map(TamarinTermPrinter::print).toList());
    System.out.println("Forget^{i+1}: " + ctx.getForgetSet().stream().map(TamarinTermPrinter::print).toList());
    System.out.println("R̄^{i+1} (forgotten rules): " + ctx.getForgottenRules());
    if (target != null) {
      System.out.println("m2: " + TamarinTermPrinter.print(target));
    }
  }

  private void printDerivationSummary(NormalDerivationEnumerator.Result enumeration, ForgetContext ctx) {
    System.out.println();
    System.out.println("Per-derivation analysis (" + enumeration.derivations().size() + " normal derivation(s)"
        + (enumeration.truncated() ? ", TRUNCATED by limits" : "") + "):");
    int n = 1;
    for (Derivation d : enumeration.derivations()) {
      System.out.println("  #" + n++ + " Hyp=" + blockingChecker.extractHypotheses(d).stream()
          .map(TamarinTermPrinter::print).toList()
          + " Rules=" + DerivationRules.rulesOf(d)
          + " blocked=" + blockingChecker.findBlockedHypotheses(d, ctx).stream()
              .map(TamarinTermPrinter::print).toList()
          + " forgottenRulesUsed=" + blockingChecker.forgottenRulesUsed(d, ctx));
    }
  }

  /**
   * Helper class to store variant information with its replacement map.
   */
  private static class VariantInfo {
    final Message variant;
    final Map<Message, Message> replacement; // blocked hypothesis -> chosen replacement

    VariantInfo(Message variant, Map<Message, Message> replacement) {
      this.variant = variant;
      this.replacement = replacement;
    }
  }

  /**
   * Builds a ForgetContext from the extracted knowledge, forget set strings, and type map.
   */
  private ForgetContext buildForgetContext(Set<Message> knowledge, Set<String> forgetStrings,
                                           Map<String, String> typeMap) {
    Set<Message> forgetMessages = new LinkedHashSet<>();

    // Convert forget strings to Messages
    for (String forgottenStr : forgetStrings) {
      String canonical = canonicalize(forgottenStr);
      // Try to find matching message in knowledge
      Message found = findMessageByRepresentation(knowledge, canonical);
      if (found != null) {
        forgetMessages.add(found);
      } else {
        // Create as Atom if not found
        forgetMessages.add(new Atom(canonical));
      }
    }

    return new ForgetContext(knowledge, forgetMessages, blockingMode, typeMap);
  }

  /**
   * Finds a message in a set by its string representation.
   */
  private Message findMessageByRepresentation(Set<Message> messages, String repr) {
    for (Message m : messages) {
      String mRepr = m.represent();
      // Check direct match or with ~ prefix
      if (mRepr.equals(repr) || mRepr.equals("~" + repr) ||
          ("~" + mRepr).equals(repr) || mRepr.replace("~", "").equals(repr)) {
        return m;
      }
    }
    return null;
  }

  /**
   * Rewrites the rule so that it sends {@code variant} instead of {@code originalTarget}.
   *
   * <p>Each blocked hypothesis is substituted by the replacement chosen for THIS variant in the
   * outbound facts, the Send action and the witness actions (lemma-only action facts, which record
   * what was actually sent). The rewritten payload is parsed back and compared with the variant;
   * if a textual substitution cannot express the variant (the blocked term also occurs in a
   * position that does not come from the replaced hypothesis), the payload is replaced by the
   * printed variant.
   */
  private void applyVariantToRule(Rule rule, Message originalTarget, Message variant,
                                  Map<Message, Message> replacement, Set<String> witnesses) {
    Map<String, String> stringSubstitution = new LinkedHashMap<>();
    for (Map.Entry<Message, Message> entry : replacement.entrySet()) {
      stringSubstitution.put(canonicalize(TamarinTermPrinter.print(entry.getKey())),
                             canonicalize(TamarinTermPrinter.print(entry.getValue())));
    }

    for (Fact post : rule.getPostconditions()) {
      if (isOutboundFact(post.getF_name())) {
        applyStringSubstitutionToFact(post, stringSubstitution);
      }
    }
    for (Fact action : rule.getActions()) {
      if (isSendAction(action.getF_name()) || witnesses.contains(action.getF_name())) {
        applyStringSubstitutionToFact(action, stringSubstitution);
      }
    }

    Message rewritten = derivationCheckService.extractTargetFromRule(rule);
    if (rewritten != null && !rewritten.equals(variant)) {
      log.warn("Textual substitution {} gives {} instead of the variant {}; writing the variant directly",
               stringSubstitution, rewritten.represent(), variant.represent());
      String printed = TamarinTermPrinter.print(variant);
      String original = TamarinTermPrinter.print(originalTarget);
      for (Fact post : rule.getPostconditions()) {
        if (isOutboundFact(post.getF_name())) replaceLastValue(post, printed);
      }
      for (Fact action : rule.getActions()) {
        if (isSendAction(action.getF_name())) {
          Object last = action.getParameters().isEmpty() ? null
              : action.getParameters().get(action.getParameters().size() - 1);
          if (last instanceof Value v && canonicalize(v.getName()).equals(canonicalize(original))) {
            v.setName(printed);
          }
        }
      }
    }
  }

  private void replaceLastValue(Fact fact, String printed) {
    List<Object> params = fact.getParameters();
    if (params == null || params.isEmpty()) return;
    if (params.get(params.size() - 1) instanceof Value v) {
      v.setName(printed);
    }
  }

  /**
   * Applies string substitutions to a fact's parameters.
   */
  private void applyStringSubstitutionToFact(Fact fact, Map<String, String> substitution) {
    for (Object param : fact.getParameters()) {
      if (param instanceof PSpecial ps) {
        for (Value v : ps.getGroup()) {
          substituteValueName(v, substitution);
        }
      } else if (param instanceof Value v) {
        substituteValueName(v, substitution);
      }
    }
  }

  /**
   * Rewrites a Value's name by substituting the canonical form of each substitution key
   * with its replacement, using a word-boundary regex so occurrences inside complex
   * payloads such as "senc(<$Human,pw1>,k(nH,nB))" are rewritten without affecting
   * unrelated tokens (e.g. "pw10").
   */
  private void substituteValueName(Value v, Map<String, String> substitution) {
    if (v == null || v.getName() == null) return;
    String original = v.getName();
    String result = original;
    for (Map.Entry<String, String> sub : substitution.entrySet()) {
      String from = canonicalize(sub.getKey());
      String to = canonicalize(sub.getValue());
      if (from == null || from.isEmpty() || from.equals(to)) continue;
      String quoted = java.util.regex.Pattern.quote(from);
      // Treat $, ~ and alphanumerics/underscore as word characters so that
      // tokens like "$Human", "~pw1" and "pw1" are matched as whole units.
      String regex = "(?<![A-Za-z0-9_$~])" + quoted + "(?![A-Za-z0-9_$])";
      result = result.replaceAll(regex, java.util.regex.Matcher.quoteReplacement(to));
    }
    if (!result.equals(original)) {
      v.setName(result);
    }
  }

  /**
   * Removes send facts from the rule and ONLY the matching receive facts from subsequent rules.
   * Per Algorithm 1: if no variant exists, remove the send action and the MATCHING receive.
   *
   * Matching is defined by: sender + receiver + label + message payload
   * NOT all receives - only the specific one that would have consumed this send.
   *
   * @param theory The theory (list of rules) to modify
   * @param currentRule The rule where send is being removed
   * @param targetMessage The target message being sent (used for matching)
   */
  private void removeSendAndMatchingReceive(ArrayList<Rule> theory, Rule currentRule, Message targetMessage) {
    // Collect send message patterns to match (with full detail for precise matching)
    Set<SendPattern> sendPatterns = new LinkedHashSet<>();
    Set<String> sentPayloadKeys = new LinkedHashSet<>();

    // Remove outbound-channel postconditions that look like the full send tuple
    // (sender,receiver,labels,values) and collect their full patterns.
    currentRule.getPostconditions().removeIf(f -> {
      if (isOutboundFact(f.getF_name()) && f.getParameters() != null
          && f.getParameters().size() >= 4) {
        SendPattern pattern = extractFullSendPattern(f);
        if (pattern != null) {
          sendPatterns.add(pattern);
          if (pattern.values != null) sentPayloadKeys.add(canonicalize(pattern.values));
          log.info("Removing {}: {}", f.getF_name(), pattern);
        }
        return true;
      }
      return false;
    });

    // Remove single-payload outbound postconditions (In/Out style rules) whose
    // payload matches the target message.
    currentRule.getPostconditions().removeIf(f -> {
      if (isOutboundFact(f.getF_name()) && f.getParameters() != null
          && f.getParameters().size() < 4) {
        String payload = extractOutPayload(f);
        if (payload != null && targetMessage != null) {
          if (sameMessage(payload, targetMessage)) {
            log.info("Removing {} matching target: {}", f.getF_name(), payload);
            sentPayloadKeys.add(canonicalize(payload));
            return true;
          }
        }
      }
      return false;
    });

    // Remove ONLY the matching Send actions (not all Send actions)
    currentRule.getActions().removeIf(f -> {
      if (isSendAction(f.getF_name())) {
        // Check if this Send action's payload matches our target
        String actionPayload = extractActionPayload(f);
        if (actionPayload != null && targetMessage != null) {
          return sameMessage(actionPayload, targetMessage);
        }
        return true; // Remove if we can't determine
      }
      return false;
    });

    if (sendPatterns.isEmpty() && sentPayloadKeys.isEmpty()) {
      log.warn("No send patterns or Out payloads extracted - nothing to match for receive removal");
      return;
    }

    // Find the index of current rule
    int currentIndex = -1;
    for (int i = 0; i < theory.size(); i++) {
      if (theory.get(i).getRule_name().equals(currentRule.getRule_name())) {
        currentIndex = i;
        break;
      }
    }

    if (currentIndex < 0) return;

    // Only look at subsequent rules for matching receives
    for (int i = currentIndex + 1; i < theory.size(); i++) {
      Rule nextRule = theory.get(i);
      boolean removedAnything = false;

      // Remove ONLY matching inbound preconditions whose full tuple matches
      // a removed send pattern (sender,receiver,labels,values).
      removedAnything |= nextRule.getPreconditions().removeIf(f -> {
        if (isInboundFact(f.getF_name()) && f.getParameters() != null
            && f.getParameters().size() >= 4) {
          SendPattern recvPattern = extractFullSendPattern(f);
          if (recvPattern != null) {
            for (SendPattern sendPat : sendPatterns) {
              if (patternsMatch(sendPat, recvPattern)) {
                log.info("Removing matching {} in rule {}: {}",
                    f.getF_name(), nextRule.getRule_name(), recvPattern);
                return true;
              }
            }
          }
        }
        return false;
      });

      // Remove ONLY matching single-payload inbound preconditions
      // (In/Out style rules) whose payload contains a removed-send payload.
      removedAnything |= nextRule.getPreconditions().removeIf(f -> {
        if (isInboundFact(f.getF_name()) && f.getParameters() != null
            && f.getParameters().size() < 4 && !f.getParameters().isEmpty()) {
          List<Object> params = f.getParameters();
          String payload = String.valueOf(params.get(params.size() - 1));
          String key = canonicalize(payload);
          for (String sentKey : sentPayloadKeys) {
            if (sentKey != null && (sentKey.contains(key) || key.contains(sentKey))) {
              log.info("Removing matching {} in rule {}: {}",
                  f.getF_name(), nextRule.getRule_name(), payload);
              return true;
            }
          }
        }
        return false;
      });

      // Remove ONLY the matching Receive actions (based on payload, not all Receive actions)
      removedAnything |= nextRule.getActions().removeIf(f -> {
        if (isReceiveAction(f.getF_name())) {
          String actionPayload = extractActionPayload(f);
          if (actionPayload != null && targetMessage != null) {
            String targetStr = targetMessage.represent();
            // Only remove if payload matches
            boolean matches = actionPayload.contains(canonicalize(targetStr)) ||
                             canonicalize(actionPayload).contains(canonicalize(targetStr));
            if (matches) {
              log.info("Removing matching Receive action in rule {}: {}", nextRule.getRule_name(), actionPayload);
            }
            return matches;
          }
        }
        return false;
      });

      // Only mark as mutated if we actually removed something
      if (removedAnything && !nextRule.getRule_name().endsWith("_M")) {
        nextRule.setRule_name(nextRule.getRule_name() + "_M");
        nextRule.setTypo(Type.MUTATED);
      }
    }
  }

  /**
   * True if the payload text (Tamarin syntax) denotes {@code target}: compared structurally after
   * parsing, or textually against the Tamarin rendering of the target.
   */
  private boolean sameMessage(String payloadText, Message target) {
    if (payloadText == null || target == null) return false;
    String text = payloadText.trim();
    try {
      Message parsed = parseTargetParam(text);
      if (target.equals(parsed)) return true;
    } catch (RuntimeException ignored) {
      // fall back to the textual comparison below
    }
    String printed = TamarinTermPrinter.print(target);
    return canonicalize(text).equals(canonicalize(printed))
        || canonicalize(text).contains(canonicalize(target.represent()));
  }

  private String extractOutPayload(Fact f) {
    if (f == null || f.getParameters() == null || f.getParameters().isEmpty()) return "";
    return String.valueOf(f.getParameters().get(f.getParameters().size() - 1));
  }

  /**
   * Pattern class for matching sends and receives with full detail.
   */
  private static class SendPattern {
    String sender;
    String receiver;
    String labels;
    String values;

    @Override
    public String toString() {
      return sender + "->" + receiver + " [" + labels + "] (" + values + ")";
    }
  }

  /**
   * Extracts a full pattern from SndS/RcvS fact for precise matching.
   */
  private SendPattern extractFullSendPattern(Fact fact) {
    if (fact.getParameters().size() < 4) {
      return null;
    }
    SendPattern pattern = new SendPattern();
    pattern.sender = paramToString(fact.getParameters().get(0));
    pattern.receiver = paramToString(fact.getParameters().get(1));
    pattern.labels = paramToString(fact.getParameters().get(2));
    pattern.values = paramToString(fact.getParameters().get(3));
    return pattern;
  }

  /**
   * Checks if two patterns match (for send/receive matching).
   * Requires: same sender, same receiver, same labels, same values.
   */
  private boolean patternsMatch(SendPattern send, SendPattern recv) {
    // Sender and receiver must match
    if (!canonicalize(send.sender).equals(canonicalize(recv.sender))) return false;
    if (!canonicalize(send.receiver).equals(canonicalize(recv.receiver))) return false;

    // Labels should match (or be compatible)
    if (!labelsMatch(send.labels, recv.labels)) return false;

    // Values should match (or be compatible)
    if (!valuesMatch(send.values, recv.values)) return false;

    return true;
  }

  /**
   * Checks if labels match (exact or compatible).
   */
  private boolean labelsMatch(String sendLabels, String recvLabels) {
    String s = canonicalize(sendLabels).replace("<", "").replace(">", "").replace("'", "");
    String r = canonicalize(recvLabels).replace("<", "").replace(">", "").replace("'", "");
    return s.equals(r);
  }

  /**
   * Checks if values match (exact or compatible).
   */
  private boolean valuesMatch(String sendValues, String recvValues) {
    String s = canonicalize(sendValues).replace("<", "").replace(">", "").replace("~", "");
    String r = canonicalize(recvValues).replace("<", "").replace(">", "").replace("~", "");
    return s.equals(r) || s.contains(r) || r.contains(s);
  }

  /**
   * Converts a parameter to string representation.
   */
  private String paramToString(Object param) {
    if (param instanceof Value v) {
      return v.getName();
    } else if (param instanceof PSpecial ps) {
      StringBuilder sb = new StringBuilder("<");
      for (int i = 0; i < ps.getGroup().size(); i++) {
        if (i > 0) sb.append(",");
        sb.append(ps.getGroup().get(i).getName());
      }
      sb.append(">");
      return sb.toString();
    }
    return String.valueOf(param);
  }

  /**
   * Extracts payload from a Send/Receive action fact.
   */
  private String extractActionPayload(Fact actionFact) {
    // Send/Receive typically have: (principal, label, value) or similar
    List<Object> params = actionFact.getParameters();
    if (params == null || params.isEmpty()) return null;

    // The value/payload is typically the last parameter
    Object lastParam = params.get(params.size() - 1);
    return paramToString(lastParam);
  }

  /**
   * Propagates mutation with variant replacements to subsequent rules.
   *
   * Per the paper (Sec. IV.C): "a mutated send action is matched by mutating
   * the corresponding receive action so that the receiver accepts the modified
   * message ... Propagation updates agents' knowledge according to the messages
   * actually received". So we substitute only in the receive-side of subsequent
   * rules (RcvS/In preconditions, all actions, and postconditions). State
   * preconditions are left intact because they represent each agent's prior,
   * monotonic knowledge. Rules whose content is not touched stay un-tagged.
   */
  private void propagateMutationWithVariant(ArrayList<Rule> theory, Rule startRule,
                                            Map<Message, Message> replacement) {
    Map<String, String> substitution = new HashMap<>();
    for (Map.Entry<Message, Message> entry : replacement.entrySet()) {
      substitution.put(canonicalize(TamarinTermPrinter.print(entry.getKey())),
                       TamarinTermPrinter.print(entry.getValue()));
    }

    if (substitution.isEmpty()) return;

    int startIndex = -1;
    for (int i = 0; i < theory.size(); i++) {
      if (theory.get(i).getRule_name().equals(startRule.getRule_name())) {
        startIndex = i;
        break;
      }
    }
    if (startIndex < 0) return;

    for (int i = startIndex + 1; i < theory.size(); i++) {
      Rule r = theory.get(i);

      boolean changed = false;
      for (Map.Entry<String, String> sub : substitution.entrySet()) {
        if (ruleHasReceiveSideValue(r, sub.getKey())) {
          forwardPropagate(r, sub.getKey(), sub.getValue());
          changed = true;
        }
      }

      if (changed && !r.getRule_name().endsWith("_M")) {
        r.setRule_name(r.getRule_name() + "_M");
        r.setTypo(Type.MUTATED);
      }
    }
  }

  /**
   * True when {@code value} occurs on the receive side of the rule, i.e. in
   * an RcvS/In precondition, in any action, or in any postcondition. State
   * preconditions are excluded because they encode the agent's pre-existing
   * knowledge, which the paper requires to remain monotonic.
   */
  private boolean ruleHasReceiveSideValue(Rule r, String value) {
    for (Fact pre : r.getPreconditions()) {
      if (isInboundFact(pre.getF_name())) {
        if (containsParam(pre, value)) return true;
      }
    }
    for (Fact act : r.getActions()) {
      if (containsParam(act, value)) return true;
    }
    for (Fact post : r.getPostconditions()) {
      if (containsParam(post, value)) return true;
    }
    return false;
  }

  /**
   * Substitute {@code from} -> {@code to} on the receive side of the rule
   * (inbound-channel preconditions, actions, and postconditions). State
   * preconditions are left intact so the receiver's prior knowledge is
   * preserved.
   */
  private void forwardPropagate(Rule r, String from, String to) {
    for (Fact pre : r.getPreconditions()) {
      if (isInboundFact(pre.getF_name())) {
        replaceInFact(pre, from, to);
      }
    }
    for (Fact act : r.getActions()) {
      replaceInFact(act, from, to);
    }
    for (Fact post : r.getPostconditions()) {
      replaceInFact(post, from, to);
    }
  }

  /**
   * Legacy mutation logic for backwards compatibility.
   */
  private void applyLegacyMutation(Rule startRule, ArrayList<Rule> theoryClone,
                                   Set<String> forgetSet, Map<String, String> setup) {
    startRule.setRule_name(startRule.getRule_name() + "_M");
    startRule.setTypo(Type.MUTATED);

    for (String forgottenOriginal : forgetSet) {
      String forgotten = canonicalize(forgottenOriginal);

      removeForgetMutation(startRule, forgotten);
      String replacement = chooseReplacement(forgotten, setup);

      replaceValue(startRule, forgotten, replacement, false, false, false);
      propagateMutation(theoryClone, startRule, forgotten, replacement, setup);
    }
  }

  // Normalize names like "~p1" -> "p1"
  private String canonicalize(String name) {
    return name != null && name.startsWith("~") ? name.substring(1) : name;
  }

  /**
   * Propagates the mutation through the theory.
   */
  private void propagateMutation(
      ArrayList<Rule> theory,
      Rule startRule,
      String forgotten,
      String replacement,
      Map<String, String> setup) {

    int startIndex = -1;
    for (int i = 0; i < theory.size(); i++) {
      if (theory.get(i).getRule_name().equals(startRule.getRule_name())) {
        startIndex = i;
        break;
      }
    }
    if (startIndex < 0) return;

    for (int i = startIndex + 1; i < theory.size(); i++) {
      Rule r = theory.get(i);

      r.setRule_name(r.getRule_name() + "_M");
      r.setTypo(Type.MUTATED);

      if (r.isHuman()) {
        continue;
      }

      replaceValue(r, forgotten, replacement, true, true, true);
    }
  }

  private void removeForgetMutation(Rule rule, String forgotten) {
    rule.getActions().removeIf(f -> isForgetAction(f.getF_name()) && containsParam(f, forgotten));
  }

  private boolean containsParam(Fact fact, String name) {
    for (Object p : fact.getParameters()) {
      if (paramContainsName(p, name)) return true;
    }
    return false;
  }

  private boolean paramContainsName(Object param, String name) {
    if (param instanceof Value v) {
      return canonicalize(v.getName()).equals(name);
    }
    if (param instanceof PSpecial ps) {
      for (Value v : ps.getGroup()) {
        if (canonicalize(v.getName()).equals(name)) return true;
      }
      return canonicalize(ps.toString()).contains(name);
    }
    if (param instanceof FSpecial fs) {
      for (Value v : fs.getGroup()) {
        if (canonicalize(v.getName()).equals(name)) return true;
      }
      return canonicalize(fs.toString()).contains(name);
    }
    if (param instanceof Nary_app na) {
      for (Value v : na.getGroup()) {
        if (canonicalize(v.getName()).equals(name)) return true;
      }
      return canonicalize(na.toString()).contains(name);
    }
    if (param != null) {
      return canonicalize(param.toString()).contains(name);
    }
    return false;
  }

  private List<Fact> isMessageUsedInInternalAction(
      Rule rule, Message forgotten, Set<String> nonInternalActionNames) {
    List<Fact> matches = new ArrayList<>();
    if (rule == null || forgotten == null || rule.getActions() == null) {
      return matches;
    }
    String forgottenName = canonicalize(forgotten.represent());
    for (Fact action : rule.getActions()) {
      if (action == null || nonInternalActionNames.contains(action.getF_name())) {
        continue;
      }
      if (containsParam(action, forgottenName)) {
        matches.add(action);
      }
    }
    return matches;
  }

  private void removeNeglectedActions(Rule rule, Set<String> actionSignatures) {
    if (rule == null || actionSignatures == null || actionSignatures.isEmpty()) {
      return;
    }
    rule.getActions().removeIf(action -> actionSignatures.contains(factSignature(action)));
  }

  private String factSignature(Fact fact) {
    if (fact == null) return "";
    StringBuilder signature = new StringBuilder(fact.getF_name()).append("|");
    for (Object param : fact.getParameters()) {
      signature.append(String.valueOf(param)).append(",");
    }
    return signature.toString();
  }

  private void replaceValue(
      Rule rule,
      String forgotten,
      String replacement,
      boolean mutatePreState,
      boolean mutateRcvS,
      boolean includeStatePost) {

    rule.getPostconditions()
        .forEach(
            f -> {
              if (includeStatePost || !isStateFact(f.getF_name())) {
                replaceInFact(f, forgotten, replacement);
              }
            });

    rule.getActions().forEach(f -> replaceInFact(f, forgotten, replacement));

    if (mutatePreState) {
      rule.getPreconditions()
          .forEach(
              f -> {
                if (!isInboundFact(f.getF_name()) || mutateRcvS)
                  replaceInFact(f, forgotten, replacement);
              });
    }
  }

  private void replaceInFact(Fact fact, String forgotten, String replacement) {
    for (Object param : fact.getParameters()) {
      if (param instanceof PSpecial) {
        deepReplaceInPSpecial((PSpecial) param, forgotten, replacement);
      } else if (param instanceof Value v) {
        if (canonicalize(v.getName()).equals(forgotten)) v.setName(replacement);
      }
    }
  }

  private void deepReplaceInPSpecial(PSpecial ps, String forgotten, String replacement) {
    for (Value v : ps.getGroup()) {
      if (canonicalize(v.getName()).equals(forgotten)) v.setName(replacement);
    }
  }

  private ArrayList<Rule> deepCloneTheory(ArrayList<Rule> src) {
    ArrayList<Rule> out = new ArrayList<>();
    src.forEach(r -> out.add(r.clone()));
    return out;
  }

  private Rule findRuleByName(ArrayList<Rule> rules, String name) {
    return rules.stream().filter(r -> name.equals(r.getRule_name())).findFirst().orElse(null);
  }

  private String chooseReplacement(String forgotten, Map<String, String> setup) {
    String type = setup.get(forgotten);
    return setup.entrySet().stream()
        .filter(e -> Objects.equals(e.getValue(), type) && !Objects.equals(e.getKey(), forgotten))
        .map(Map.Entry::getKey)
        .findFirst()
        .orElse(forgotten + "_rep");
  }

  /**
   * Resolves the term written in Forget(...) to a message of K^i or to the received message m1,
   * comparing terms structurally (so tuples and function applications are recognised) and atoms
   * up to the fresh-name prefix ~.
   */
  private Message resolveForgetMessage(Set<Message> knowledge, Message received, String forgottenStr) {
    String canonical = canonicalize(forgottenStr.trim());
    Message parsed = parseTargetParam(canonical);
    List<Message> candidates = new ArrayList<>();
    if (received != null) candidates.add(received);
    candidates.addAll(knowledge);
    for (Message m : candidates) {
      if (m.equals(parsed)) return m;
    }
    for (Message m : candidates) {
      if (m instanceof Atom a && parsed instanceof Atom p
          && canonicalize(a.getValue()).equals(canonicalize(p.getValue()))) {
        return m;
      }
    }
    Message found = findMessageByRepresentation(knowledge, canonical);
    if (found != null) {
      return found;
    }
    return parsed != null ? parsed : new Atom(canonical);
  }

  /**
   * K^i of the transition: the payload of the State fact the rule starts from (the agent state
   * AgSt(H, i, K^i)), the agent's own name, and the values read from the other premises
   * (persistent facts such as !Ltk, !Pk). The post-State is NOT used: it lists values the agent
   * only obtains by inference from the received message during the transition (Sec. 3.4:
   * K^{i+1} = K^i ∪ {m1} ∪ fresh values).
   */
  private Set<Message> knowledgeAtState(Rule rule) {
    Set<Message> out = statePayloadKnowledge(rule);
    out.addAll(premiseKnowledge(rule));
    return out;
  }

  /** The agent's name and the payload of the State fact the rule starts from. */
  private Set<Message> statePayloadKnowledge(Rule rule) {
    return knowledgeFromPremises(rule, true);
  }

  /** Values read from the other premises (persistent facts such as !Ltk, !Pk). */
  private Set<Message> premiseKnowledge(Rule rule) {
    return knowledgeFromPremises(rule, false);
  }

  private Set<Message> knowledgeFromPremises(Rule rule, boolean stateFacts) {
    Set<Message> out = new LinkedHashSet<>();
    if (rule == null || rule.getPreconditions() == null) return out;
    for (Fact pre : rule.getPreconditions()) {
      String name = pre.getF_name();
      List<Object> params = pre.getParameters();
      if (params == null || params.isEmpty()) continue;
      if (isStateFact(name)) {
        if (!stateFacts) continue;
        addIfKnowledge(out, paramToMessage(params.get(0)));
        if (params.size() >= 3) {
          String payload = payloadToString(params.get(params.size() - 1)).trim();
          if (payload.startsWith("<") && payload.endsWith(">")) {
            payload = payload.substring(1, payload.length() - 1);
          }
          for (String part : splitTopLevelCommas(payload)) {
            if (!part.isBlank()) addIfKnowledge(out, parseStringToMessage(part));
          }
        }
      } else if (!stateFacts && !isInboundFact(name) && !isFreshFact(name)) {
        for (Object p : params) addIfKnowledge(out, paramToMessage(p));
      }
    }
    return out;
  }

  private void addIfKnowledge(Set<Message> out, Message m) {
    // Quoted constants are public values, not part of the agent's own knowledge state.
    if (m != null && !(m instanceof Atom a && a.getValue().startsWith("'"))) out.add(m);
  }

  /** Values generated fresh in Pre_i (Fr facts), added to K^{i+1} (Sec. 3.4). */
  private Set<Message> freshValues(Rule rule) {
    Set<Message> out = new LinkedHashSet<>();
    if (rule == null || rule.getPreconditions() == null) return out;
    for (Fact pre : rule.getPreconditions()) {
      if (isFreshFact(pre.getF_name()) && pre.getParameters() != null) {
        for (Object p : pre.getParameters()) {
          Message m = paramToMessage(p);
          if (m != null) out.add(m);
        }
      }
    }
    return out;
  }

  /** Public names ($A) and public constants ('c') occurring in a term. */
  private static Set<Message> publicAtoms(Message m) {
    Set<Message> out = new LinkedHashSet<>();
    for (Message s : com.xmen.service.derivation.DolevYaoTerms.subterms(List.of(m))) {
      if (s instanceof Atom a && (a.getValue().startsWith("$") || a.getValue().startsWith("'"))) {
        out.add(s);
      }
    }
    return out;
  }

  private Message paramToMessage(Object param) {
    if (param == null) return null;
    String text = param instanceof Value v ? v.getName() : String.valueOf(param);
    if (text == null || text.isBlank()) return null;
    try {
      return parseTargetParam(text.trim());
    } catch (RuntimeException e) {
      return new Atom(text.trim());
    }
  }

  private boolean isFreshFact(String name) {
    if (name == null) return false;
    if (vocabulary != null) return vocabulary.isFreshFact(name);
    return "Fr".equals(name);
  }

  private Message extractReceivedMessage(Rule rule) {
    if (rule == null || rule.getPreconditions() == null) {
      return null;
    }
    // Preferred shape: inbound fact carrying the full (sender,receiver,labels,values)
    // tuple. The payload sits in the last parameter.
    for (Fact fact : rule.getPreconditions()) {
      if (isInboundFact(fact.getF_name())) {
        List<Object> params = fact.getParameters();
        if (params != null && params.size() >= 4) {
          Object valuesParam = params.get(params.size() - 1);
          String paramStr = payloadToString(valuesParam).trim();
          Message received = parseTargetParam(paramStr);
          if (received != null) {
            log.debug("Extracted received message from {}: {}",
                fact.getF_name(), received.represent());
            return received;
          }
        }
      }
    }
    // Fallback shape: single-payload inbound fact (e.g. native Tamarin In(...)).
    for (Fact pre : rule.getPreconditions()) {
      if (isInboundFact(pre.getF_name())) {
        List<Object> params = pre.getParameters();
        if (params != null && !params.isEmpty() && params.size() < 4) {
          Object payloadParam = params.get(params.size() - 1);
          String paramStr = String.valueOf(payloadParam).trim();
          try {
            Message m = parseStringToMessage(paramStr);
            if (m != null) {
              log.debug("Extracted received message from {}: {}",
                  pre.getF_name(), m.represent());
              return m;
            }
          } catch (Throwable t) {
            // fall through to Atom fallback
          }
          return new Atom(paramStr);
        }
      }
    }
    return null;
  }

  private String payloadToString(Object obj) {
    if (obj instanceof Value v) {
      return v.getName();
    }
    return String.valueOf(obj);
  }

  private Message parseTargetParam(String param) {
    String trimmed = param.trim();
    if (trimmed.startsWith("<") && trimmed.endsWith(">")) {
      String inner = trimmed.substring(1, trimmed.length() - 1);
      List<String> parts = splitTopLevelCommas(inner);
      return buildNestedPair(parts);
    }
    return parseStringToMessage(trimmed);
  }

  private Message buildNestedPair(List<String> elements) {
    if (elements.isEmpty()) return null;
    if (elements.size() == 1) return parseStringToMessage(elements.get(0).trim());
    Message first = parseStringToMessage(elements.get(0).trim());
    Message rest = buildNestedPair(elements.subList(1, elements.size()));
    return new Pair(first, rest);
  }

  private Message parseStringToMessage(String raw) {
    String str = raw.trim();

    if (str.startsWith("<") && str.endsWith(">")) {
      String inner = str.substring(1, str.length() - 1).trim();
      if (inner.isEmpty()) return new Atom(str);
      List<String> parts = splitTopLevelCommas(inner);
      return buildNestedPair(parts);
    }

    if (str.startsWith("{") && str.contains("}_")) return parseEncryption(str);
    if (str.startsWith("(") && str.endsWith(")")) return parsePair(str);
    if (str.contains("(") && str.endsWith(")")) return parseFunction(str);
    return new Atom(str);
  }

  private Encrypt parseEncryption(String str) {
    String s = str.trim();
    if (!s.startsWith("{") || !s.endsWith("}")) {
      return new Encrypt(new Atom(str), new Atom("UNKNOWN_KEY"));
    }
    int sep = s.indexOf("}_");
    if (sep < 0) {
      return new Encrypt(new Atom(str), new Atom("UNKNOWN_KEY"));
    }
    String msgPart = s.substring(1, sep).trim();
    int keyStart = sep + 2;
    if (keyStart >= s.length() || s.charAt(keyStart) != '{') {
      return new Encrypt(new Atom(str), new Atom("UNKNOWN_KEY"));
    }
    int depth = 0, i = keyStart;
    for (; i < s.length(); i++) {
      char c = s.charAt(i);
      if (c == '{') depth++;
      else if (c == '}') {
        depth--;
        if (depth == 0) {
          i++;
          break;
        }
      }
    }
    String keyPart = s.substring(keyStart + 1, i - 1).trim();
    Message msg = parseStringToMessage(msgPart);
    Message key = parseStringToMessage(keyPart);
    return new Encrypt(msg, key);
  }

  private Message parsePair(String str) {
    String inner = str.substring(1, str.length() - 1).trim();
    int commaPos = findTopLevelComma(inner);
    if (commaPos < 0) return parseStringToMessage(inner);
    String left = inner.substring(0, commaPos).trim();
    String right = inner.substring(commaPos + 1).trim();
    return new Pair(parseStringToMessage(left), parseStringToMessage(right));
  }

  private Message parseFunction(String str) {
    int idx = str.indexOf('(');
    String name = str.substring(0, idx).trim();
    String inside = str.substring(idx + 1, str.length() - 1).trim();
    if (inside.isEmpty()) return new Atom(name);
    List<String> parts = splitTopLevelCommas(inside);
    List<Message> args = new ArrayList<>();
    for (String p : parts) args.add(parseStringToMessage(p));
    return new PredictiveFunction(name, args);
  }

  private int findTopLevelComma(String s) {
    int depth = 0;
    for (int i = 0; i < s.length(); i++) {
      char c = s.charAt(i);
      if (c == '(' || c == '<') depth++;
      else if (c == ')' || c == '>') depth--;
      else if (c == ',' && depth == 0) return i;
    }
    return -1;
  }

  private List<String> splitTopLevelCommas(String s) {
    List<String> parts = new ArrayList<>();
    int depth = 0;
    int last = 0;
    for (int i = 0; i < s.length(); i++) {
      char c = s.charAt(i);
      if (c == '(' || c == '<') depth++;
      else if (c == ')' || c == '>') depth--;
      else if (c == ',' && depth == 0) {
        parts.add(s.substring(last, i).trim());
        last = i + 1;
      }
    }
    parts.add(s.substring(last).trim());
    return parts;
  }

}
