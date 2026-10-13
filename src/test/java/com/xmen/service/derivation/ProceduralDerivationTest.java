package com.xmen.service.derivation;

import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.a;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.aenc;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.fn;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.pair;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.pk;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.senc;
import static org.assertj.core.api.Assertions.assertThat;

import com.xmen.model.Derivation;
import com.xmen.model.InferenceRule;
import com.xmen.model.Message;
import com.xmen.service.forget.BlockingChecker;
import com.xmen.service.forget.ForgetContext;
import com.xmen.service.forget.ForgetContext.BlockingMode;
import com.xmen.service.forget.ForgetDerivationChecker;
import com.xmen.service.impl.DerivationServiceImpl;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.springframework.test.util.ReflectionTestUtils;

/**
 * Procedural forgetting at the derivation level: Rules(π) (Definition 5), derivability with
 * forgotten rules, alternative derivations with shared dependencies, replay of derivations.
 */
@DisplayName("Procedural forgetting: Rules(π) and forgotten rules")
class ProceduralDerivationTest {

  private DerivationServiceImpl engine;
  private ForgetDerivationChecker checker;

  // K = { {|m1|}_m2, <m2,m4>, {|m3|}_m2, {m2}_pk(sk4), sk4 }, target <m1,m3>. The key m2 is
  // needed on both branches (shared dependency) and is obtained either by projection or by
  // asymmetric decryption, so there are 2 x 2 = 4 normal derivations.
  private final Message m1 = a("m1");
  private final Message m2 = a("m2");
  private final Message m3 = a("m3");
  private final Message target = pair(m1, m3);
  private final Set<Message> k = new LinkedHashSet<>(List.of(
      senc(m1, m2), pair(m2, a("m4")), senc(m3, m2), aenc(m2, pk(a("sk4"))), a("sk4")));

  @BeforeEach
  void setUp() {
    engine = new DerivationServiceImpl();
    engine.setConfig(new DerivationConfig(Set.of(), 1000, 64));
    checker = new ForgetDerivationChecker();
    ReflectionTestUtils.setField(checker, "blockingChecker", new BlockingChecker());
    ReflectionTestUtils.setField(checker, "derivationService", engine);
    checker.overrideLimits(64, 1000);
  }

  private boolean derivable(InferenceRule... forgotten) {
    ForgetContext ctx = new ForgetContext(k, Set.of(), Set.of(forgotten), BlockingMode.CASE1_WEAK, Map.of());
    return checker.derivableUnderForgetting(target, ctx);
  }

  @Test
  @DisplayName("Four normal derivations; Rules(π) lists each rule once")
  void rulesOfDerivations() {
    Set<Derivation> pi = engine.deriveToDepthNoPrint(target, k, 64);
    assertThat(pi).hasSize(4);
    Set<Set<InferenceRule>> ruleSets = new java.util.HashSet<>();
    for (Derivation d : pi) ruleSets.add(DerivationRules.rulesOf(d));
    assertThat(ruleSets).containsExactlyInAnyOrder(
        Set.of(InferenceRule.PAIR, InferenceRule.SDEC, InferenceRule.UNPAIR),
        Set.of(InferenceRule.PAIR, InferenceRule.SDEC, InferenceRule.ADEC),
        Set.of(InferenceRule.PAIR, InferenceRule.SDEC, InferenceRule.UNPAIR, InferenceRule.ADEC));
  }

  @Test
  @DisplayName("Forgetting a rule blocks exactly the derivations that use it (Def. 5)")
  void forgottenRulesBlockDerivations() {
    assertThat(derivable()).isTrue();
    assertThat(derivable(InferenceRule.UNPAIR)).as("both keys via r_adec survive").isTrue();
    assertThat(derivable(InferenceRule.ADEC)).as("both keys via r_unpair survive").isTrue();
    assertThat(derivable(InferenceRule.UNPAIR, InferenceRule.ADEC)).as("no way to get m2").isFalse();
    assertThat(derivable(InferenceRule.SDEC)).as("every derivation decrypts").isFalse();
    assertThat(derivable(InferenceRule.PAIR)).as("every derivation pairs at the root").isFalse();
    assertThat(derivable(InferenceRule.AENC)).as("r_aenc is never applied").isTrue();
  }

  @Test
  @DisplayName("A hypothesis taken directly from K needs no rule")
  void hypothesisNeedsNoRule() {
    Set<Message> kk = new LinkedHashSet<>(k);
    kk.add(target);
    ForgetContext ctx = new ForgetContext(kk, Set.of(), Set.copyOf(InferenceRule.PAPER_RULES),
        BlockingMode.CASE1_WEAK, Map.of());
    assertThat(checker.derivableUnderForgetting(target, ctx)).isTrue();
  }

  @Test
  @DisplayName("Forgotten rules and forgotten messages combine (Def. 5 + Def. 7)")
  void rulesAndMessagesCombine() {
    // m2 forgotten as a hypothesis does not block: m2 is not a hypothesis of any derivation.
    ForgetContext ctx1 = new ForgetContext(k, Set.of(m2), Set.of(), BlockingMode.CASE1_WEAK, Map.of());
    assertThat(checker.derivableUnderForgetting(target, ctx1)).isTrue();
    // <m2,m4> forgotten and r_adec forgotten: neither way to obtain m2 remains.
    ForgetContext ctx2 = new ForgetContext(k, Set.of(pair(m2, a("m4"))), Set.of(InferenceRule.ADEC),
        BlockingMode.CASE1_WEAK, Map.of());
    assertThat(checker.derivableUnderForgetting(target, ctx2)).isFalse();
  }

  @Test
  @DisplayName("Cyclic re-derivations are not normal: <a,b> from {<a,b>} has only the direct derivation")
  void cyclesExcluded() {
    Set<Derivation> pi = engine.deriveToDepthNoPrint(pair(a("a"), a("b")), Set.of(pair(a("a"), a("b"))), 64);
    assertThat(pi).hasSize(1);
    assertThat(pi.iterator().next().getRule()).isEqualTo("Initial");
  }

  @Test
  @DisplayName("Private functions cannot be composed")
  void privateFunctions() {
    DerivationServiceImpl priv = new DerivationServiceImpl();
    priv.setConfig(new DerivationConfig(Set.of(), Set.of("f"), 1000, 64));
    assertThat(priv.deriveToDepthNoPrint(fn("f", a("x")), Set.of(a("x")), 64)).isEmpty();
    assertThat(engine.deriveToDepthNoPrint(fn("f", a("x")), Set.of(a("x")), 64)).hasSize(1);
  }

  @Test
  @DisplayName("Limits are reported as truncation, not silently applied")
  void truncationIsReported() {
    DerivationServiceImpl capped = new DerivationServiceImpl();
    capped.setConfig(new DerivationConfig(Set.of(), 1, 64));
    assertThat(capped.enumerate(target, k, 64).truncated()).isTrue();
    assertThat(engine.enumerate(target, k, 2).truncated()).as("depth 2 is too shallow").isTrue();
    assertThat(engine.enumerate(target, k, 64).truncated()).isFalse();
  }

  @Test
  @DisplayName("Replay recomputes the conclusion and rejects a decryption with a replaced key")
  void replay() {
    Message c = senc(pair(a("pw1"), a("u")), a("key"));
    Set<Derivation> pi = engine.deriveToDepthNoPrint(fn("h", a("pw1")), Set.of(c, a("key")), 64);
    Derivation d = pi.iterator().next();
    assertThat(DerivationRules.replay(d, Map.of(c, senc(pair(a("pw2"), a("u")), a("key")))))
        .contains(fn("h", a("pw2")));
    assertThat(DerivationRules.replay(d, Map.of(a("key"), a("other")))).isEqualTo(Optional.empty());
  }
}
