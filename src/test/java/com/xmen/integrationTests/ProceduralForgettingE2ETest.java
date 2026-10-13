package com.xmen.integrationTests;

import static com.xmen.integrationTests.ForgetEndpointHarness.ruleText;
import static org.assertj.core.api.Assertions.assertThat;

import com.xmen.config.CeremonyVocabulary;
import com.xmen.service.impl.ForgetMutationStrategy;
import com.xmen.utilities.MutationWorkspace;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Stream;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.test.context.ActiveProfiles;
import org.springframework.test.web.servlet.setup.MockMvcBuilders;
import org.springframework.web.context.WebApplicationContext;

/**
 * End-to-end tests of procedural forgetting (ForgetRule) and of the atomic-forgetting
 * behaviours affected by the derivation fixes, through the same endpoints the UI uses.
 *
 * <p>Expected outcomes are derived by hand from Algorithm 1 (journal) for each fixture:
 * see the comments of every test.
 */
@SpringBootTest
@ActiveProfiles("test")
@DisplayName("Procedural forgetting end-to-end")
class ProceduralForgettingE2ETest {

  private static final String FORGET = "/api/forget/mutations";

  @Autowired private WebApplicationContext context;
  @Autowired private MutationWorkspace workspace;
  @Autowired private CeremonyVocabulary vocabulary;
  @Autowired private ForgetMutationStrategy strategy;

  private ForgetEndpointHarness harness;
  private CeremonyVocabulary savedVocabulary;
  private String bank;
  private String procedural;

  @BeforeEach
  void setUp() throws IOException {
    harness = new ForgetEndpointHarness(MockMvcBuilders.webAppContextSetup(context).build());
    savedVocabulary = new CeremonyVocabulary();
    savedVocabulary.copyFrom(vocabulary);
    vocabulary.copyFrom(new CeremonyVocabulary());
    strategy.setNonInternalActions(null);
    bank = Files.readString(Paths.get("src/test/resources/Forget_Bank_Input.spthy"));
    procedural = Files.readString(Paths.get("src/test/resources/Forget_Procedural.spthy"));
  }

  @AfterEach
  void tearDown() throws IOException {
    vocabulary.copyFrom(savedVocabulary);
    try (Stream<Path> s = Files.list(workspace.root())) {
      for (Path p : s.toList()) {
        String n = p.getFileName().toString();
        if (n.matches("(Bank|Procedural|FreshK)_M\\d+\\.m")) Files.deleteIfExists(p);
      }
    }
  }

  private ForgetEndpointHarness.Outcome postBank(String annotation) throws Exception {
    return harness.post(FORGET, "Bank.spthy", bank.replace("Forget(pw1)", annotation));
  }

  // ---------------------------------------------------------------------------------------------
  // Bank Login (paper case study) with procedural lapses in H_2
  // ---------------------------------------------------------------------------------------------

  @Test
  @DisplayName("ForgetRule(r_adec) in H_2: nB is only reachable by asymmetric decryption -> SKIP")
  void bankForgetAdecSkipsSend() throws Exception {
    ForgetEndpointHarness.Outcome o = postBank("ForgetRule('r_adec')");
    assertThat(o.status()).isEqualTo(200);
    String h2 = ruleText(o.onlyMutant(), "H_2_M");
    assertThat(h2).isNotNull();
    assertThat(h2).doesNotContain("Out(senc(").doesNotContain("Send($Human,'m3'");
    assertThat(h2).doesNotContain("ForgetRule");
    assertThat(o.report()).contains("forgottenRulesUsed=[r_adec]").contains("Decision: SKIP");
  }

  @Test
  @DisplayName("ForgetRule(r_unpair), r_pair or r_k in H_2: every derivation needs the rule -> SKIP")
  void bankForgetOtherNeededRulesSkip() throws Exception {
    for (String r : List.of("'r_unpair'", "'r_pair'", "'r_k'")) {
      ForgetEndpointHarness.Outcome o = postBank("ForgetRule(" + r + ")");
      assertThat(o.status()).as(r).isEqualTo(200);
      assertThat(ruleText(o.onlyMutant(), "H_2_M")).as(r).doesNotContain("Out(senc(");
    }
  }

  @Test
  @DisplayName("ForgetRule(r_sdec) in H_2: symmetric decryption is not needed -> send preserved")
  void bankForgetUnneededRulePreservesSend() throws Exception {
    ForgetEndpointHarness.Outcome o = postBank("ForgetRule('r_sdec')");
    assertThat(o.status()).isEqualTo(200);
    String h2 = ruleText(o.onlyMutant(), "H_2");
    assertThat(h2).startsWith("rule H_2:").contains("Out(senc(<$Human,pw1>,k(nH,nB)))");
    assertThat(o.report()).contains("Decision: send preserved");
  }

  @Test
  @DisplayName("A rule that does not exist in the theory cannot be forgotten (HTTP 400)")
  void unknownRuleRejected() throws Exception {
    ForgetEndpointHarness.Outcome o = postBank("ForgetRule('r_h')");
    assertThat(o.status()).isEqualTo(400);
    assertThat(o.body()).contains("unknown inference rule 'r_h'").contains("r_adec");
    ForgetEndpointHarness.Outcome bad = postBank("ForgetRule('1x')");
    assertThat(bad.status()).isEqualTo(400);
    assertThat(bad.body()).contains("not an inference rule name");
  }

  @Test
  @DisplayName("Forget(pw1) + ForgetRule(r_k): REPLACE cannot repair a forgotten rule -> SKIP")
  void combinedLapseSkips() throws Exception {
    ForgetEndpointHarness.Outcome o = postBank("Forget(pw1)\n\t  , ForgetRule('r_k')");
    assertThat(o.status()).isEqualTo(200);
    String h2 = ruleText(o.onlyMutant(), "H_2_M");
    assertThat(h2).doesNotContain("Out(senc(");
    assertThat(o.report()).contains("Decision: SKIP");
  }

  @Test
  @DisplayName("The combined /api/generateMutations endpoint accepts ForgetRule too")
  void combinedEndpoint() throws Exception {
    ForgetEndpointHarness.Outcome o = harness.post("/api/generateMutations", "Bank.spthy",
        bank.replace("Forget(pw1)", "ForgetRule('r_adec')"), "Forget-Mutation", "true");
    assertThat(o.status()).isEqualTo(200);
    List<Path> out;
    try (Stream<Path> s = Files.list(workspace.root())) {
      out = s.filter(p -> p.getFileName().toString().matches("Bank_M\\d+\\.m")).toList();
    }
    assertThat(out).hasSize(1);
    assertThat(ruleText(Files.readString(out.get(0)), "H_2_M")).doesNotContain("Out(senc(");
  }

  // ---------------------------------------------------------------------------------------------
  // Procedural fixture: decrypt (r_sdec), project (r_unpair), hash (r_h)
  // ---------------------------------------------------------------------------------------------

  @Test
  @DisplayName("r_sdec forgotten in User_1: send skipped, CheckSecret neglected, matching receive removed; "
      + "R̄ persists so User_2 (which must decrypt) is skipped too")
  void proceduralDefault() throws Exception {
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Procedural.spthy", procedural);
    assertThat(o.status()).isEqualTo(200);
    assertThat(o.mutants()).hasSize(2);
    String m0 = o.mutants().get("Procedural_M0.m");
    String m1 = o.mutants().get("Procedural_M1.m");
    String u1 = ruleText(m0, "User_1_M");
    assertThat(u1).doesNotContain("Out(h(x))").doesNotContain("CheckSecret(").contains("Receive($User,'c1'");
    assertThat(ruleText(m0, "Server_2_M")).doesNotContain("In(h(x))");
    // User_2: ForgetRule('r_pair') alone would not matter, but r_sdec (forgotten in User_1) does.
    assertThat(ruleText(m1, "User_2_M")).doesNotContain("Out(h(z))");
    assertThat(o.report()).contains("R̄^{i+1} (forgotten rules): [r_pair, r_sdec]");
  }

  @Test
  @DisplayName("Without the earlier lapse, forgetting r_pair in User_2 has no effect")
  void proceduralNoPersistence() throws Exception {
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Procedural.spthy",
        procedural.replace("\t  , ForgetRule('r_sdec')\n", ""));
    assertThat(o.status()).isEqualTo(200);
    String u2 = ruleText(o.onlyMutant(), "User_2");
    assertThat(u2).startsWith("rule User_2:").contains("Out(h(z))");
  }

  @Test
  @DisplayName("Alternative derivation: if x is also known directly, forgetting r_sdec keeps the send")
  void proceduralAlternativeDerivation() throws Exception {
    String spec = procedural.replace("State($User,'1',<$Server,k,n>)", "State($User,'1',<$Server,k,n,x>)");
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Procedural.spthy", spec);
    assertThat(o.status()).isEqualTo(200);
    String u1 = ruleText(o.mutants().get("Procedural_M0.m"), "User_1");
    assertThat(u1).startsWith("rule User_1:").contains("Out(h(x))").contains("CheckSecret(x)");
  }

  @Test
  @DisplayName("r_h forgotten: the hash cannot be built (SKIP) but x is still known, so no NEGLECT")
  void proceduralHashForgotten() throws Exception {
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Procedural.spthy",
        procedural.replace("ForgetRule('r_sdec')", "ForgetRule('r_h')"));
    String u1 = ruleText(o.mutants().get("Procedural_M0.m"), "User_1_M");
    assertThat(u1).doesNotContain("Out(h(x))").contains("CheckSecret(x)");
  }

  @Test
  @DisplayName("Atomic: forgetting the key needed to decrypt makes the content check impossible (NEGLECT)")
  void forgottenKeyNeglectsCheck() throws Exception {
    String spec = procedural.replace("ForgetRule('r_sdec')", "Forget(k)").replace("\t  , ForgetRule('r_pair')\n", "");
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Procedural.spthy", spec);
    assertThat(o.status()).isEqualTo(200);
    String u1 = ruleText(o.onlyMutant(), "User_1_M");
    assertThat(u1).doesNotContain("CheckSecret(").doesNotContain("Out(h(x))");
  }

  // ---------------------------------------------------------------------------------------------
  // Atomic forgetting regressions and general properties
  // ---------------------------------------------------------------------------------------------

  @Test
  @DisplayName("Bank Forget(pw1): REPLACE by pw2 is now obtained from a real derivation (no fallback)")
  void atomicBankUsesDerivations() throws Exception {
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Bank.spthy", bank);
    String h2 = ruleText(o.onlyMutant(), "H_2_M");
    assertThat(h2).contains("Out(senc(<$Human,pw2>,k(nH,nB)))")
        .contains("Send($Human,'m3',senc(<$Human,pw2>,k(nH,nB)))")
        .contains("PasswordAttempt($Human,$B1,pw2,nH,nB)");
    assertThat(o.report()).contains("Decision: REPLACE").doesNotContain("legacy textual fallback");
  }

  @Test
  @DisplayName("Fresh values generated in the transition belong to K^{i+1} (Sec. 3.4)")
  void freshValuesAreKnowledge() throws Exception {
    String spec = Files.readString(Paths.get("src/test/resources/Forget_FreshKnowledge.spthy"));
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "FreshK.spthy", spec);
    assertThat(o.status()).isEqualTo(200);
    // n is not needed for senc(~r,k): the send is preserved.
    String u2 = ruleText(o.onlyMutant(), "User_2");
    assertThat(u2).startsWith("rule User_2:").contains("Out(senc(~r,k))");
    assertThat(o.report()).contains("Decision: send preserved");
  }

  @Test
  @DisplayName("Repeated execution on identical input gives identical mutants and report")
  void deterministic() throws Exception {
    ForgetEndpointHarness.Outcome a = harness.post(FORGET, "Procedural.spthy", procedural);
    ForgetEndpointHarness.Outcome b = harness.post(FORGET, "Procedural.spthy", procedural);
    assertThat(b.mutants()).isEqualTo(a.mutants());
    assertThat(b.report()).isEqualTo(a.report());
  }

  @Test
  @DisplayName("No Forget/ForgetRule annotation: HTTP 400 with the message the UI recognises")
  void missingAnnotation() throws Exception {
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Bank.spthy", bank.replace("\t  , Forget(pw1)\n", ""));
    assertThat(o.status()).isEqualTo(400);
    assertThat(o.body()).contains("Forget function not found");
  }
}
