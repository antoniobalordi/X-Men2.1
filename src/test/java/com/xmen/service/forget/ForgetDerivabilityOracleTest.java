package com.xmen.service.forget;

import static org.assertj.core.api.Assertions.assertThat;

import com.xmen.model.InferenceRule;
import com.xmen.model.Message;
import com.xmen.service.derivation.DerivationConfig;
import com.xmen.service.derivation.reference.RandomInstances;
import com.xmen.service.derivation.reference.ReferenceDerivationOracle;
import com.xmen.service.forget.ForgetContext.BlockingMode;
import com.xmen.service.impl.DerivationServiceImpl;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.springframework.test.util.ReflectionTestUtils;

/**
 * Definition 7 ("derivable under forgetting") against the independent oracle, for the three
 * blocking cases of Definition 6.
 *
 * <p>Expected value: some normal derivation of the target (oracle) has no blocked hypothesis,
 * where a hypothesis h is blocked iff h ∈ Forget (Case 1), Forget ⊢ h with pairing rules
 * (Case 2) or Forget ⊢ h with all Dolev-Yao rules (Case 3); the closures are also computed by
 * the oracle.
 */
@DisplayName("Derivable under forgetting (Def. 7) vs independent oracle")
class ForgetDerivabilityOracleTest {

  private ForgetDerivationChecker checker;
  private final ReferenceDerivationOracle oracle = new ReferenceDerivationOracle();
  private final ReferenceDerivationOracle pairingOracle = ReferenceDerivationOracle.pairingOnly();

  @BeforeEach
  void setUp() {
    DerivationServiceImpl engine = new DerivationServiceImpl();
    engine.setConfig(new DerivationConfig(Set.of(), 1_000_000, 64));
    checker = new ForgetDerivationChecker();
    ReflectionTestUtils.setField(checker, "blockingChecker", new BlockingChecker());
    ReflectionTestUtils.setField(checker, "derivationService", engine);
    checker.overrideLimits(64, 1_000_000);
  }

  private boolean blockedByOracle(Message h, Set<Message> forget, BlockingMode mode) {
    return switch (mode) {
      case CASE1_WEAK -> forget.contains(h);
      case CASE2_PAIRING -> pairingOracle.derivable(h, forget);
      case CASE3_FULL_DY -> oracle.derivable(h, forget);
    };
  }

  private boolean expected(Message target, Set<Message> k, Set<Message> forget, BlockingMode mode) {
    for (ReferenceDerivationOracle.RTree t : oracle.derivations(target, k)) {
      boolean anyBlocked = false;
      for (Message h : t.hypotheses()) {
        if (blockedByOracle(h, forget, mode)) {
          anyBlocked = true;
          break;
        }
      }
      if (!anyBlocked) return true;
    }
    return false;
  }

  @Test
  @DisplayName("Randomised: 3 blocking cases x 200 seeded instances")
  void randomised() {
    RandomInstances gen = new RandomInstances(7L);
    List<String> failures = new ArrayList<>();
    int checked = 0;
    int mismatches = 0;
    for (int i = 0; i < 200; i++) {
      RandomInstances.Instance inst = gen.next();
      Set<Message> forget = gen.subset(inst.knowledge(), 0.4);
      for (BlockingMode mode : BlockingMode.values()) {
        boolean exp;
        try {
          exp = expected(inst.target(), inst.knowledge(), forget, mode);
        } catch (ReferenceDerivationOracle.TooLargeException e) {
          continue;
        }
        checked++;
        ForgetContext ctx = new ForgetContext(inst.knowledge(), forget, mode, Map.of());
        boolean got = checker.derivableUnderForgetting(inst.target(), ctx);
        if (got != exp) {
          mismatches++;
          if (failures.size() < 5) {
            failures.add(mode + " target=" + inst.target().represent()
                + " K=" + inst.knowledge().stream().map(Message::represent).toList()
                + " Forget=" + forget.stream().map(Message::represent).toList()
                + " expected=" + exp + " got=" + got);
          }
        }
      }
    }
    System.out.printf("[oracle] Def. 7: %d checks, %d mismatches%n", checked, mismatches);
    assertThat(failures).as("%d mismatches among %d checks", mismatches, checked).isEmpty();
  }

  private static final List<InferenceRule> RULES = List.of(
      InferenceRule.PAIR, InferenceRule.UNPAIR, InferenceRule.SENC, InferenceRule.SDEC,
      InferenceRule.AENC, InferenceRule.ADEC, InferenceRule.forFunction("h"), InferenceRule.forFunction("pk"));

  @Test
  @DisplayName("Randomised procedural forgetting (Def. 5): forgotten rules x 3 cases x 200 instances")
  void randomisedWithForgottenRules() {
    RandomInstances gen = new RandomInstances(11L);
    List<String> failures = new ArrayList<>();
    int checked = 0;
    int mismatches = 0;
    int rulesMattered = 0;
    for (int i = 0; i < 200; i++) {
      RandomInstances.Instance inst = gen.next();
      Set<Message> forget = gen.subset(inst.knowledge(), 0.25);
      Set<InferenceRule> forgottenRules = new java.util.TreeSet<>();
      for (InferenceRule r : RULES) if (gen.nextInt(4) == 0) forgottenRules.add(r);
      Set<String> forgottenIds = new java.util.HashSet<>();
      forgottenRules.forEach(r -> forgottenIds.add(r.id()));
      for (BlockingMode mode : BlockingMode.values()) {
        boolean exp = false;
        boolean expIgnoringRules = false;
        try {
          for (ReferenceDerivationOracle.RTree t : oracle.derivations(inst.target(), inst.knowledge())) {
            boolean unblocked = t.hypotheses().stream().noneMatch(h -> blockedByOracle(h, forget, mode));
            if (!unblocked) continue;
            expIgnoringRules = true;
            if (t.rules().stream().noneMatch(forgottenIds::contains)) exp = true;
          }
        } catch (ReferenceDerivationOracle.TooLargeException e) {
          continue;
        }
        checked++;
        if (exp != expIgnoringRules) rulesMattered++;
        ForgetContext ctx = new ForgetContext(inst.knowledge(), forget, forgottenRules, mode, Map.of());
        boolean got = checker.derivableUnderForgetting(inst.target(), ctx);
        if (got != exp) {
          mismatches++;
          if (failures.size() < 5) {
            failures.add(mode + " target=" + inst.target().represent()
                + " K=" + inst.knowledge().stream().map(Message::represent).toList()
                + " Forget=" + forget.stream().map(Message::represent).toList()
                + " R̄=" + forgottenRules + " expected=" + exp + " got=" + got);
          }
        }
      }
    }
    System.out.printf("[oracle] Def. 5+7: %d checks, %d mismatches, forgotten rules changed the outcome in %d%n",
        checked, mismatches, rulesMattered);
    assertThat(failures).as("%d mismatches among %d checks", mismatches, checked).isEmpty();
    assertThat(rulesMattered).as("instances where forgotten rules changed the outcome").isGreaterThan(20);
  }
}
