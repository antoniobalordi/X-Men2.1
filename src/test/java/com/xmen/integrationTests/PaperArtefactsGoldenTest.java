package com.xmen.integrationTests;

import static org.assertj.core.api.Assertions.assertThat;

import com.xmen.config.CeremonyVocabulary;
import com.xmen.service.impl.ForgetMutationStrategy;
import com.xmen.utilities.MutationWorkspace;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
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
 * Golden tests for the mutated specifications that the paper's case studies are analysed on.
 * The committed mutants are the artefacts reviewers download: X-Men must regenerate them
 * byte for byte from the committed inputs.
 */
@SpringBootTest
@ActiveProfiles("test")
@DisplayName("Paper case studies: committed mutants are regenerated exactly")
class PaperArtefactsGoldenTest {

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
        if (n.matches("(Bank|Forget_Invoice_Input)_M\\d+\\.m")) Files.deleteIfExists(p);
      }
    }
  }

  @Test
  @DisplayName("Invoice-Payment: Forget(accNew) regenerates examples/invoice-payment/Forget_Invoice_Input_M0.m")
  void invoiceMutantIsUnchanged() throws Exception {
    String input = Files.readString(Paths.get("examples/invoice-payment/Forget_Invoice_Input.spthy"));
    String expected = Files.readString(Paths.get("examples/invoice-payment/Forget_Invoice_Input_M0.m"));
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Forget_Invoice_Input.spthy", input);
    assertThat(o.status()).isEqualTo(200);
    assertThat(o.mutants()).containsOnlyKeys("Forget_Invoice_Input_M0.m");
    assertThat(o.onlyMutant()).isEqualTo(expected);
  }

  @Test
  @DisplayName("Bank-Login: Forget(pw1) regenerates src/test/resources/Forget_Bank_Output.m")
  void bankMutantIsUnchanged() throws Exception {
    String input = Files.readString(Paths.get("src/test/resources/Forget_Bank_Input.spthy"));
    String expected = Files.readString(Paths.get("src/test/resources/Forget_Bank_Output.m"));
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, "Bank.spthy", input);
    assertThat(o.status()).isEqualTo(200);
    assertThat(o.onlyMutant()).isEqualTo(expected);
  }
}
