package com.xmen.service.derivation;

import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.a;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.aenc;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.fn;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.pair;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.pk;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.senc;
import static org.assertj.core.api.Assertions.assertThat;

import com.xmen.model.Derivation;
import com.xmen.model.Encrypt;
import com.xmen.model.Message;
import com.xmen.service.derivation.reference.RandomInstances;
import com.xmen.service.derivation.reference.ReferenceDerivationOracle;
import com.xmen.service.impl.DerivationServiceImpl;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

/**
 * Soundness and completeness of the derivation enumeration (Phase 4 audit).
 *
 * <p>The production enumeration ({@link DerivationServiceImpl#deriveToDepthNoPrint}) must return
 * exactly the set of normal derivations computed by the independent forward oracle: no missing
 * derivation (completeness), no invalid, duplicated or merged derivation (soundness).
 */
@DisplayName("Derivation enumeration vs independent oracle")
class DerivationEnumerationOracleTest {

  private DerivationServiceImpl engine;
  private final ReferenceDerivationOracle oracle = new ReferenceDerivationOracle();

  @BeforeEach
  void setUp() {
    engine = new DerivationServiceImpl();
    engine.setConfig(new DerivationConfig(Set.of(), 1_000_000, 64));
  }

  private void assertSameDerivations(Message target, Set<Message> knowledge) {
    Set<Derivation> produced = engine.deriveToDepthNoPrint(target, knowledge, 64);
    Set<String> expected = ReferenceDerivationOracle.canonicalTrees(oracle.derivations(target, knowledge));
    assertThat(ReferenceDerivationOracle.canonicalSet(produced))
        .as("derivations of %s from %s", target.represent(), knowledge.stream().map(Message::represent).toList())
        .isEqualTo(expected);
    assertThat(produced).as("no duplicate derivations").hasSize(expected.size());
  }

  private static Set<Message> k(Message... ms) {
    return new LinkedHashSet<>(List.of(ms));
  }

  @Test
  @DisplayName("Paper Ex.4: m1 has a direct and a decryption derivation; decryption lists ciphertext and key")
  void example4TwoDerivations() {
    assertSameDerivations(a("m1"), k(a("m1"), senc(a("m1"), a("m2")), a("m2")));
  }

  @Test
  @DisplayName("Legacy {m}_{k} notation: decryption premises are ciphertext and key")
  void legacyEncryptPremises() {
    assertSameDerivations(a("m1"), k(a("m1"), new Encrypt(a("m1"), a("m2")), a("m2")));
  }

  @Test
  @DisplayName("Tamarin senc(...) is decrypted with its key")
  void symmetricDecryptionOfTamarinTerm() {
    assertSameDerivations(a("m"), k(senc(a("m"), a("k")), a("k")));
  }

  @Test
  @DisplayName("aenc(m, pk(sk)) is decrypted with sk, never with pk(sk)")
  void asymmetricDecryption() {
    assertSameDerivations(a("m"), k(aenc(a("m"), pk(a("sk"))), a("sk")));
    assertSameDerivations(a("m"), k(aenc(a("m"), pk(a("sk"))), pk(a("sk"))));
  }

  @Test
  @DisplayName("Nested tuple <a,<b,c>>: c needs two projections")
  void nestedProjection() {
    assertSameDerivations(a("c"), k(pair(a("a"), pair(a("b"), a("c")))));
  }

  @Test
  @DisplayName("Projection of a decrypted pair and decryption of a projected ciphertext")
  void decompositionChains() {
    assertSameDerivations(a("x"), k(senc(pair(a("x"), a("y")), a("k")), a("k")));
    assertSameDerivations(a("x"), k(pair(senc(a("x"), a("k")), a("k"))));
  }

  @Test
  @DisplayName("Public user function k(nH,nB) is composed from its arguments")
  void userFunctionComposition() {
    assertSameDerivations(fn("k", a("nH"), a("nB")), k(a("nH"), a("nB")));
  }

  @Test
  @DisplayName("Bank Login m3 = senc(<H,pw>, k(nH,nB)) with nB inside the received challenge")
  void bankLoginCredentialMessage() {
    Message challenge = aenc(pair(a("nH"), a("nB")), pk(a("ltkH")));
    assertSameDerivations(
        senc(pair(a("$Human"), a("pw1")), fn("k", a("nH"), a("nB"))),
        k(a("$Human"), a("pw1"), a("pw2"), a("nH"), a("ltkH"), challenge));
  }

  @Test
  @DisplayName("Composite key: decryption with a key that must itself be composed")
  void composedKey() {
    assertSameDerivations(a("m"), k(senc(a("m"), fn("h", a("x"))), a("x")));
  }

  @Test
  @DisplayName("Shared dependency: the same hypothesis feeds two branches")
  void sharedDependency() {
    assertSameDerivations(pair(a("x"), a("x")), k(senc(a("x"), a("k")), a("k"), a("x")));
  }

  @Test
  @DisplayName("Randomised differential test against the oracle (seeded, 300 instances)")
  void randomisedDifferential() {
    RandomInstances gen = new RandomInstances(20261013L);
    int checked = 0;
    int skipped = 0;
    List<String> failures = new ArrayList<>();
    for (int i = 0; i < 300; i++) {
      RandomInstances.Instance inst = gen.next();
      Set<String> expected;
      try {
        expected = ReferenceDerivationOracle.canonicalTrees(oracle.derivations(inst.target(), inst.knowledge()));
      } catch (ReferenceDerivationOracle.TooLargeException e) {
        skipped++;
        continue;
      }
      checked++;
      Set<String> produced =
          ReferenceDerivationOracle.canonicalSet(engine.deriveToDepthNoPrint(inst.target(), inst.knowledge(), 64));
      if (!produced.equals(expected) && failures.size() < 5) {
        failures.add(
            "target=" + inst.target().represent()
                + " K=" + inst.knowledge().stream().map(Message::represent).toList()
                + " expected=" + expected.size() + " produced=" + produced.size());
      }
    }
    System.out.printf("[oracle] enumeration: %d instances checked, %d skipped as too large%n", checked, skipped);
    assertThat(skipped).as("instances too large for the oracle").isLessThan(30);
    assertThat(failures).as("mismatches among %d checked instances", checked).isEmpty();
  }
}
