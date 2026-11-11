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
import java.util.Map;
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
 * Algorithm 1 (journal version of November 2026) is applied at every human transition after the
 * first lapse: a lapse at the account-change notice (H_2) takes effect at the payment order (H_3).
 * Both forms of the Invoice-Payment lapse of the paper are covered: case (1), H does not add
 * accNew to the knowledge; case (3), H forgets symmetric decryption and cannot read the notice.
 *
 * <p>Set {@code -Dxmen.forget.dump=<dir>} to keep the generated mutants and reports (e.g. to
 * analyse them with Tamarin).
 */
@SpringBootTest
@ActiveProfiles("test")
@DisplayName("Forget: lapses persist across transitions (Invoice-Payment)")
class ForgetLapsePersistenceE2ETest {

  private static final String FORGET = "/api/forget/mutations";

  @Autowired private WebApplicationContext context;
  @Autowired private MutationWorkspace workspace;
  @Autowired private CeremonyVocabulary vocabulary;
  @Autowired private ForgetMutationStrategy strategy;

  private ForgetEndpointHarness harness;
  private CeremonyVocabulary savedVocabulary;

  @BeforeEach
  void setUp() {
    harness = new ForgetEndpointHarness(MockMvcBuilders.webAppContextSetup(context).build());
    savedVocabulary = new CeremonyVocabulary();
    savedVocabulary.copyFrom(vocabulary);
    vocabulary.copyFrom(new CeremonyVocabulary());
    strategy.setNonInternalActions(null);
  }

  @AfterEach
  void tearDown() throws IOException {
    vocabulary.copyFrom(savedVocabulary);
    try (Stream<Path> s = Files.list(workspace.root())) {
      for (Path p : s.toList()) {
        String n = p.getFileName().toString();
        if (n.matches("(InvoiceCase1|InvoiceProcedural|Procedural)_M\\d+\\.m")) Files.deleteIfExists(p);
      }
    }
  }

  /** The committed Invoice input: Forget(accNew) at the notice (H_2), case (1) of Definition 4. */
  private static String invoiceCase1() throws IOException {
    String input = Files.readString(Paths.get("examples/invoice-payment/Forget_Invoice_Input.spthy"));
    assertThat(ruleText(input, "H_2")).contains("Forget(accNew)");
    assertThat(ruleText(input, "H_3")).doesNotContain("Forget(");
    return input;
  }

  private static void dump(String name, ForgetEndpointHarness.Outcome o) throws IOException {
    String dir = System.getProperty("xmen.forget.dump");
    if (dir == null) return;
    Path d = Paths.get(dir, name);
    Files.createDirectories(d);
    for (Map.Entry<String, String> m : o.mutants().entrySet()) {
      Files.writeString(d.resolve(m.getKey()), m.getValue());
    }
    if (o.report() != null) Files.writeString(d.resolve("report.txt"), o.report());
  }

  @Test
  @DisplayName("Case (1) at the notice: accNew never enters K, so the order at H_3 is REPLACEd by accOld")
  void case1AtNoticeReplacesAtPayment() throws Exception {
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "InvoiceCase1.spthy", invoiceCase1());
    dump("case1", o);
    assertThat(o.status()).isEqualTo(200);
    String m = o.onlyMutant();
    // H_2: H does not record what they did not retain (NEGLECT of the internal action).
    assertThat(ruleText(m, "H_2_M")).doesNotContain("RecordAccount(").contains("Receive($Human,'n2',accNew)");
    // H_3 (no annotation): the lapse of H_2 persists; accOld replaces accNew in the order.
    assertThat(ruleText(m, "H_3_M"))
        .contains("PaymentOrder($Human,$B,$S,svc,amt,accOld)")
        .contains("sign(<$Human,$B,$S,svc,amt,accOld>,ltkH)")
        .doesNotContain("PaymentOrder($Human,$B,$S,svc,amt,accNew)");
    // The replacement reaches the confirmation (paper Listing 3 reads H_Confirm).
    assertThat(ruleText(m, "H_4_M")).contains("H_Confirm($Human,$B,$S,svc,amt,accOld)");
    assertThat(o.report())
        .contains("Not available to H after the earlier lapses: [accNew]")
        .contains("Underivable atomic components U: [accNew]")
        .contains("Repl(accNew): [accOld]")
        .contains("Decision: REPLACE with 1 variant(s)");
  }

  @Test
  @DisplayName("Forgetting is local to the lapsing human: another agent's rule marked H() is not affected")
  void lapseIsLocalToTheHumanWhoForgets() throws Exception {
    String procedural = Files.readString(Paths.get("src/test/resources/Forget_Procedural.spthy"));
    String spec = procedural
        .replace("ForgetRule('r_sdec')", "ForgetRule('r_senc')")
        .replace("--[ Accept($Server,x) ]->", "--[ H(), Accept($Server,x) ]->");
    assertThat(spec).contains("H(), Accept($Server,x)").contains("ForgetRule('r_senc')");
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Procedural.spthy", spec);
    assertThat(o.status()).isEqualTo(200);
    // $User forgot symmetric encryption; $Server still encrypts its reply.
    assertThat(ruleText(o.onlyMutant(), "Server_2")).startsWith("rule Server_2:").contains("Out(senc(z,k))");
  }

  @Test
  @DisplayName("Case (3) at the notice: ForgetRule(r_sdec) leaves accNew underivable, so the order is REPLACEd")
  void proceduralSdecReplacesAtPayment() throws Exception {
    String spec = Files.readString(Paths.get("examples/invoice-payment-procedural/Forget_Invoice_Procedural.spthy"));
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "InvoiceProcedural.spthy", spec);
    dump("procedural", o);
    assertThat(o.status()).isEqualTo(200);
    String m = o.onlyMutant();
    assertThat(ruleText(m, "H_2_M")).doesNotContain("RecordAccount(");
    assertThat(ruleText(m, "H_3_M"))
        .contains("PaymentOrder($Human,$B,$S,svc,amt,accOld)")
        .contains("sign(<$Human,$B,$S,svc,amt,accOld>,ltkH)");
    assertThat(ruleText(m, "H_4_M")).contains("H_Confirm($Human,$B,$S,svc,amt,accOld)");
    assertThat(o.report())
        .contains("R̄^{i+1} (forgotten rules): [r_sdec]")
        .contains("Underivable atomic components U: [accNew]")
        .contains("Repl(accNew): [accOld]")
        .contains("Decision: REPLACE with 1 variant(s)");
  }
}
