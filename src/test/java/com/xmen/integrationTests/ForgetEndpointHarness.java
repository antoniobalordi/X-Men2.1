package com.xmen.integrationTests;

import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.multipart;

import java.io.ByteArrayInputStream;
import java.nio.charset.StandardCharsets;
import java.util.Map;
import java.util.TreeMap;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import org.springframework.http.MediaType;
import org.springframework.mock.web.MockMultipartFile;
import org.springframework.mock.web.MockHttpServletResponse;
import org.springframework.test.web.servlet.MockMvc;
import org.springframework.test.web.servlet.request.MockMultipartHttpServletRequestBuilder;

/** Posts a .spthy file to a Forget endpoint and unpacks the returned zip. */
final class ForgetEndpointHarness {

  /** Outcome of one request: HTTP status, raw body text, mutant files and derivation report. */
  record Outcome(int status, String body, Map<String, String> mutants, String report) {
    String onlyMutant() {
      if (mutants.size() != 1) {
        throw new AssertionError("expected exactly one mutant but got " + mutants.keySet());
      }
      return mutants.values().iterator().next();
    }
  }

  private final MockMvc mockMvc;

  ForgetEndpointHarness(MockMvc mockMvc) {
    this.mockMvc = mockMvc;
  }

  Outcome post(String endpoint, String fileName, String spec, String... headers) throws Exception {
    MockMultipartFile file = new MockMultipartFile(
        "file", fileName, MediaType.TEXT_PLAIN_VALUE, spec.getBytes(StandardCharsets.UTF_8));
    MockMultipartHttpServletRequestBuilder req = multipart(endpoint).file(file);
    for (int i = 0; i + 1 < headers.length; i += 2) req.header(headers[i], headers[i + 1]);
    MockHttpServletResponse resp = mockMvc.perform(req).andReturn().getResponse();
    Map<String, String> mutants = new TreeMap<>();
    String report = "";
    byte[] body = resp.getContentAsByteArray();
    if (resp.getStatus() == 200 && body.length > 0) {
      try (ZipInputStream zin = new ZipInputStream(new ByteArrayInputStream(body))) {
        ZipEntry e;
        while ((e = zin.getNextEntry()) != null) {
          String text = new String(zin.readAllBytes(), StandardCharsets.UTF_8);
          if (e.getName().endsWith("_DerivationTree.txt")) report = text;
          else if (e.getName().endsWith(".m")) mutants.put(e.getName(), text);
        }
      }
    }
    String text = resp.getStatus() == 200 ? "" : resp.getContentAsString();
    return new Outcome(resp.getStatus(), text, mutants, report);
  }

  /** Extracts the text of one rule (from "rule NAME" to the next "rule " or end). */
  static String ruleText(String model, String ruleName) {
    int i = model.indexOf("rule " + ruleName + ":");
    if (i < 0) return null;
    int j = model.indexOf("\nrule ", i + 1);
    return j < 0 ? model.substring(i) : model.substring(i, j);
  }
}
