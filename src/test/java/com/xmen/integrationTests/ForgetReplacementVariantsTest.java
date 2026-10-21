package com.xmen.integrationTests;

import static org.assertj.core.api.Assertions.assertThat;
import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.multipart;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.status;

import com.xmen.config.CeremonyVocabulary;
import com.xmen.utilities.MutationWorkspace;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
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
import org.springframework.http.MediaType;
import org.springframework.mock.web.MockMultipartFile;
import org.springframework.test.context.ActiveProfiles;
import org.springframework.test.web.servlet.MockMvc;
import org.springframework.test.web.servlet.setup.MockMvcBuilders;
import org.springframework.web.context.WebApplicationContext;

/**
 * Algorithm 1, lines 26-30: every combination of admissible replacements yields a distinct
 * REPLACE variant. With three passwords of label 'password', forgetting pw1 admits pw2 and pw3,
 * so two distinct mutants are expected.
 */
@SpringBootTest
@ActiveProfiles("test")
@DisplayName("Forget: one distinct mutant per admissible replacement")
class ForgetReplacementVariantsTest {

  @Autowired private WebApplicationContext context;
  @Autowired private MutationWorkspace workspace;
  @Autowired private CeremonyVocabulary vocabulary;
  private MockMvc mockMvc;
  private CeremonyVocabulary savedVocabulary;

  @BeforeEach
  void setUp() {
    mockMvc = MockMvcBuilders.webAppContextSetup(context).build();
    // The vocabulary bean is hydrated from ~/.xmen/settings.json; run on the built-in defaults.
    savedVocabulary = new CeremonyVocabulary();
    savedVocabulary.copyFrom(vocabulary);
    vocabulary.copyFrom(new CeremonyVocabulary());
  }

  @AfterEach
  void cleanUp() throws IOException {
    vocabulary.copyFrom(savedVocabulary);
    for (Path p : outputs()) Files.deleteIfExists(p);
  }

  private List<Path> outputs() throws IOException {
    try (Stream<Path> s = Files.list(workspace.root())) {
      return s.filter(p -> p.getFileName().toString().startsWith("BankThree_M")).sorted().toList();
    }
  }

  @Test
  @DisplayName("Forget(pw1) with pw2 and pw3 available: two distinct REPLACE mutants")
  void twoDistinctReplacements() throws Exception {
    MockMultipartFile file = new MockMultipartFile(
        "file", "BankThree.spthy", MediaType.TEXT_PLAIN_VALUE,
        Files.readAllBytes(Paths.get("src/test/resources/Forget_Bank_ThreePasswords.spthy")));
    mockMvc.perform(multipart("/api/forget/mutations").file(file)).andExpect(status().isOk());

    List<Path> out = outputs();
    assertThat(out).hasSize(2);
    String m0 = Files.readString(out.get(0), StandardCharsets.UTF_8);
    String m1 = Files.readString(out.get(1), StandardCharsets.UTF_8);
    assertThat(m0).isNotEqualTo(m1);
    String both = m0 + m1;
    assertThat(both).contains("Out(senc(<$Human,pw2>,k(nH,nB)))");
    assertThat(both).contains("Out(senc(<$Human,pw3>,k(nH,nB)))");
    assertThat(m0).doesNotContain("Out(senc(<$Human,pw1>,k(nH,nB)))");
    assertThat(m1).doesNotContain("Out(senc(<$Human,pw1>,k(nH,nB)))");
  }
}
