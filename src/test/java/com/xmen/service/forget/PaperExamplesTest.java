package com.xmen.service.forget;

import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.a;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.pair;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.senc;
import static org.assertj.core.api.Assertions.assertThat;

import com.xmen.model.Derivation;
import com.xmen.model.Message;
import com.xmen.service.derivation.DerivationConfig;
import com.xmen.service.forget.ForgetContext.BlockingMode;
import com.xmen.service.impl.DerivationServiceImpl;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.springframework.test.util.ReflectionTestUtils;

/**
 * The worked examples of the journal manuscript, Sec. 4 ("The Forget Mutation"), with the
 * expected results stated in the paper. Encryptions use Tamarin syntax ({@code senc(m,k)}),
 * which is what the parser produces for real .spthy input.
 */
@DisplayName("Journal Sec. 4 worked examples")
class PaperExamplesTest {

  private ForgetDerivationChecker checker;
  private DerivationServiceImpl engine;
  private final BlockingChecker blocking = new BlockingChecker();

  @BeforeEach
  void setUp() {
    engine = new DerivationServiceImpl();
    engine.setConfig(new DerivationConfig(Set.of(), 1_000_000, 64));
    checker = new ForgetDerivationChecker();
    ReflectionTestUtils.setField(checker, "blockingChecker", blocking);
    ReflectionTestUtils.setField(checker, "derivationService", engine);
    checker.overrideLimits(64, 1_000_000);
  }

  private static Set<Message> set(Message... ms) {
    return new LinkedHashSet<>(List.of(ms));
  }

  private boolean derivable(Message t, Set<Message> k, Set<Message> forget, BlockingMode mode) {
    return checker.derivableUnderForgetting(t, new ForgetContext(k, forget, mode, Map.of()));
  }

  @Test
  @DisplayName("Example 1: a forgotten message may occur in a derivation, but not as a hypothesis")
  void example1() {
    Message m = a("m");
    Message mbar = a("mbar");
    // K = { {m}_mbar, mbar }, Forget = { mbar }: the only derivation uses mbar as hypothesis.
    assertThat(derivable(m, set(senc(m, mbar), mbar), set(mbar), BlockingMode.CASE1_WEAK)).isFalse();
    // K = { {m}_mbar, {mbar}_m1, m1 }, Forget = { mbar }: mbar is re-derived, not a hypothesis.
    assertThat(derivable(m, set(senc(m, mbar), senc(mbar, a("m1")), a("m1")), set(mbar), BlockingMode.CASE1_WEAK))
        .isTrue();
  }

  @Test
  @DisplayName("Example 4: forgetting {m1}_m2 leaves the direct derivation of m1 (all cases)")
  void example4() {
    Set<Message> k = set(a("m1"), senc(a("m1"), a("m2")), a("m2"));
    Set<Message> forget = set(senc(a("m1"), a("m2")));
    Set<Derivation> pi = engine.deriveToDepthNoPrint(a("m1"), k, 64);
    assertThat(pi).as("two derivations: direct and via decryption").hasSize(2);
    long blockedCount = pi.stream()
        .filter(d -> blocking.hasBlockedHypotheses(d, new ForgetContext(k, forget, BlockingMode.CASE1_WEAK, Map.of())))
        .count();
    assertThat(blockedCount).as("the decryption derivation is blocked in Case 1").isEqualTo(1);
    for (BlockingMode mode : BlockingMode.values()) {
      assertThat(derivable(a("m1"), k, forget, mode)).as(mode.name()).isTrue();
    }
  }

  @Test
  @DisplayName("Example 5: Forget={{m1}_m2, m2}: derivable in Case 1, not in Case 3")
  void example5() {
    Set<Message> k = set(a("m1"), senc(a("m1"), a("m2")), a("m2"));
    Set<Message> forget = set(senc(a("m1"), a("m2")), a("m2"));
    assertThat(derivable(a("m1"), k, forget, BlockingMode.CASE1_WEAK)).isTrue();
    // Case 2: Forget ⊬_pairing m1, so the direct hypothesis m1 is not blocked.
    assertThat(derivable(a("m1"), k, forget, BlockingMode.CASE2_PAIRING)).isTrue();
    assertThat(derivable(a("m1"), k, forget, BlockingMode.CASE3_FULL_DY)).isFalse();
  }

  @Test
  @DisplayName("Example 6: forgotten pair: components usable in Case 1, unusable in Cases 2 and 3")
  void example6() {
    Set<Message> k = set(pair(a("m1"), a("m2")), a("m1"), a("m2"));
    Set<Message> forget = set(pair(a("m1"), a("m2")));
    assertThat(derivable(a("m1"), k, forget, BlockingMode.CASE1_WEAK)).isTrue();
    assertThat(derivable(a("m1"), k, forget, BlockingMode.CASE2_PAIRING)).isFalse();
    assertThat(derivable(a("m1"), k, forget, BlockingMode.CASE3_FULL_DY)).isFalse();
    assertThat(derivable(a("m2"), k, forget, BlockingMode.CASE2_PAIRING)).isFalse();
  }

  @Test
  @DisplayName("Forgotten ciphertext blocks the decryption derivation when m1 is not known directly")
  void forgottenCiphertextBlocksDecryption() {
    Set<Message> k = set(senc(a("m1"), a("m2")), a("m2"));
    assertThat(derivable(a("m1"), k, set(senc(a("m1"), a("m2"))), BlockingMode.CASE1_WEAK)).isFalse();
  }

  @Test
  @DisplayName("Example 2: forgetting the just-received message leaves K and Forget unchanged")
  void example2() {
    ForgetContext ctx = new ForgetContext(set(a("m2"), a("m4")), Set.of(), BlockingMode.CASE1_WEAK, Map.of());
    ctx.updateForTransition(a("m1"), a("m1"));
    assertThat(ctx.getKnowledge()).containsExactlyInAnyOrder(a("m2"), a("m4"));
    assertThat(ctx.getForgetSet()).isEmpty();
  }

  @Test
  @DisplayName("Alg. 1 l.5: forgetting the received m1 keeps an earlier forgotten m1 in Forget")
  void forgetJustReceivedKeepsForgetSet() {
    ForgetContext ctx = new ForgetContext(set(a("x")), set(a("x")), BlockingMode.CASE1_WEAK, Map.of());
    ctx.updateForTransition(a("x"), a("x"));
    assertThat(ctx.getForgetSet()).containsExactly(a("x"));
  }

  @Test
  @DisplayName("Example 3: forgetting a known message, then re-receiving it")
  void example3() {
    Message c = senc(pair(a("m2"), a("m4")), a("m5"));
    ForgetContext ctx = new ForgetContext(set(c, a("m2"), a("m4")), Set.of(), BlockingMode.CASE1_WEAK, Map.of());
    ctx.updateForTransition(a("m1"), a("m2"));
    assertThat(ctx.getKnowledge()).containsExactlyInAnyOrder(c, a("m2"), a("m4"), a("m1"));
    assertThat(ctx.getForgetSet()).containsExactly(a("m2"));
    ctx.updateForTransition(a("m2"), null);
    assertThat(ctx.getForgetSet()).isEmpty();
  }
}
