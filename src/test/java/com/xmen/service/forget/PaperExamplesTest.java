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
    assertThat(receive(ctx, a("m2"))).containsExactly(a("m2"));
    assertThat(ctx.getForgetSet()).isEmpty();
  }

  /** Example 3 after H forgets m2: K = { {|m2,m4|}m5, m2, m4, m1 }, Forget = { m2 }. */
  private static ForgetContext example3AfterLapse() {
    Message c = senc(pair(a("m2"), a("m4")), a("m5"));
    ForgetContext ctx = new ForgetContext(set(c, a("m2"), a("m4")), Set.of(), BlockingMode.CASE1_WEAK, Map.of());
    ctx.updateForTransition(a("m1"), a("m2"));
    return ctx;
  }

  /** Phase 1 for a transition that receives {@code m1} and forgets nothing (Algorithm 1). */
  private Set<Message> receive(ForgetContext ctx, Message m1) {
    List<Message> candidates = List.copyOf(ctx.getForgetSet());
    ctx.updateForTransition(m1, null);
    Set<Message> relearned = checker.relearnedBy(m1, candidates, ctx);
    ctx.relearn(relearned);
    return relearned;
  }

  @Test
  @DisplayName("Example 3: receiving m5 makes m2 derivable again, so m2 leaves Forget")
  void example3ReceiveKey() {
    ForgetContext ctx = example3AfterLapse();
    assertThat(checker.derivableUnderForgetting(a("m2"), ctx)).isFalse();
    assertThat(receive(ctx, a("m5"))).containsExactly(a("m2"));
    assertThat(ctx.getForgetSet()).isEmpty();
    assertThat(checker.derivableUnderForgetting(a("m2"), ctx)).isTrue();
  }

  @Test
  @DisplayName("Example 3: receiving {|m5|}m1 (m1 known) makes m2 derivable again")
  void example3ReceiveWrappedKey() {
    ForgetContext ctx = example3AfterLapse();
    assertThat(receive(ctx, senc(a("m5"), a("m1")))).containsExactly(a("m2"));
    assertThat(ctx.getForgetSet()).isEmpty();
  }

  @Test
  @DisplayName("Re-acquisition: a received message that does not give back m2 leaves Forget unchanged")
  void unrelatedReceiveKeepsForget() {
    ForgetContext ctx = example3AfterLapse();
    assertThat(receive(ctx, a("m6"))).isEmpty();
    assertThat(receive(ctx, senc(a("m5"), a("m7")))).isEmpty();
    assertThat(ctx.getForgetSet()).containsExactly(a("m2"));
  }

  /** Example 1: K = { {m}_mbar, {mbar}_m1, m1, mbar }, Forget = { mbar }; mbar is derivable via m1. */
  private static ForgetContext example1Knowledge() {
    Message mbar = a("mbar");
    return new ForgetContext(set(senc(a("m"), mbar), senc(mbar, a("m1")), a("m1"), mbar),
        set(mbar), BlockingMode.CASE1_WEAK, Map.of());
  }

  @Test
  @DisplayName("Re-acquisition: receiving m1 again releases mbar, whose normal derivation uses m1")
  void releasedWhenADerivationUsesTheReceivedMessage() {
    ForgetContext ctx = example1Knowledge();
    assertThat(receive(ctx, a("m1"))).containsExactly(a("mbar"));
    assertThat(ctx.getForgetSet()).isEmpty();
  }

  @Test
  @DisplayName("Re-acquisition: a message no normal derivation of mbar uses does not release it")
  void notReleasedWhenNoDerivationUsesTheReceivedMessage() {
    ForgetContext ctx = example1Knowledge();
    // mbar stays derivable (from {mbar}_m1 and m1), but no normal derivation of it uses m6.
    assertThat(receive(ctx, a("m6"))).isEmpty();
    assertThat(ctx.getForgetSet()).containsExactly(a("mbar"));
  }

  @Test
  @DisplayName("Re-acquisition: closure case (ii), receiving the key <a,b> gives back a, b and x in one pass")
  void receivedCopyIsNeverBlocked() {
    // Forget = { a, b, x }; the pairing closure of { a, b } blocks <a,b>, but the new copy is usable.
    Message ab = pair(a("a"), a("b"));
    ForgetContext ctx = new ForgetContext(set(senc(a("x"), ab), a("a"), a("b"), a("x")),
        set(a("a"), a("b"), a("x")), BlockingMode.CASE2_PAIRING, Map.of());
    assertThat(receive(ctx, ab)).containsExactlyInAnyOrder(a("a"), a("b"), a("x"));
    assertThat(ctx.getForgetSet()).isEmpty();
  }

  @Test
  @DisplayName("Re-acquisition: the new copy is usable even if the blocking closure blocks the old one")
  void receivedCopyIsUsableUnderClosure() {
    // Case 2: Forget = { a, b } blocks the pair <a,b>; receiving <a,b> again gives a and b back.
    Message ab = pair(a("a"), a("b"));
    ForgetContext ctx = new ForgetContext(set(ab, a("a"), a("b")), set(a("a"), a("b")),
        BlockingMode.CASE2_PAIRING, Map.of());
    assertThat(receive(ctx, ab)).containsExactlyInAnyOrder(a("a"), a("b"));
    assertThat(ctx.getForgetSet()).isEmpty();
  }

  @Test
  @DisplayName("Re-acquisition: a rule forgotten at this or an earlier step blocks it, and is never released")
  void forgottenRuleIsNotReleased() {
    ForgetContext ctx = example3AfterLapse();
    ctx.forgetRule(com.xmen.model.InferenceRule.SDEC);
    assertThat(receive(ctx, a("m5"))).as("m2 needs sdec, which H has forgotten").isEmpty();
    assertThat(ctx.getForgetSet()).containsExactly(a("m2"));
    assertThat(ctx.getForgottenRules()).containsExactly(com.xmen.model.InferenceRule.SDEC);
  }
}
