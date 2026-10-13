package com.xmen.service.derivation;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import com.xmen.model.InferenceRule;
import com.xmen.utilities.ForgetMutationParser;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

@DisplayName("Inference rule names and ForgetRule targets")
class InferenceRuleAndParserTest {

  @Test
  @DisplayName("Paper names, bare operator names and quotes are accepted")
  void parsesRuleNames() {
    assertThat(InferenceRule.parse("'r_sdec'")).isEqualTo(InferenceRule.SDEC);
    assertThat(InferenceRule.parse("r_sdec")).isEqualTo(InferenceRule.SDEC);
    assertThat(InferenceRule.parse("sdec")).isEqualTo(InferenceRule.SDEC);
    assertThat(InferenceRule.parse("\"R_ADEC\"")).isEqualTo(InferenceRule.ADEC);
    assertThat(InferenceRule.parse("'r_unpair'")).isEqualTo(InferenceRule.UNPAIR);
    assertThat(InferenceRule.parse("fst")).isEqualTo(InferenceRule.UNPAIR);
    assertThat(InferenceRule.parse("snd")).isEqualTo(InferenceRule.UNPAIR);
    assertThat(InferenceRule.parse("pairing")).isEqualTo(InferenceRule.PAIR);
    assertThat(InferenceRule.parse("'r_h'")).isEqualTo(new InferenceRule("r_h"));
  }

  @Test
  @DisplayName("Both projections are the single rule r_unpair (paper Sec. 3.2)")
  void projectionsAreOneRule() {
    assertThat(InferenceRule.forFunction("fst")).isEqualTo(InferenceRule.forFunction("snd"));
    assertThat(InferenceRule.PAPER_RULES).hasSize(6);
  }

  @Test
  @DisplayName("Malformed names are rejected")
  void rejectsMalformedNames() {
    assertThatThrownBy(() -> InferenceRule.parse("'1x'")).isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> InferenceRule.parse("''")).isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> InferenceRule.parse("r_s-dec")).isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  @DisplayName("Known rules = R of the paper + r_f for declared and builtin function symbols")
  void knownRulesFromTheory() {
    String theory = "theory T\nbegin\nbuiltins: hashing, signing\nfunctions: k/2, f/1 [private]\nrule A: [] --[]-> []\nend";
    assertThat(ForgetMutationParser.knownRules(theory))
        .containsAll(InferenceRule.PAPER_RULES)
        .contains(new InferenceRule("r_k"), new InferenceRule("r_f"), new InferenceRule("r_h"),
                  new InferenceRule("r_sign"), new InferenceRule("r_verify"), new InferenceRule("r_pk"))
        .doesNotContain(new InferenceRule("r_xor"));
    assertThat(ForgetMutationParser.privateFunctions(theory)).containsExactly("f");
  }
}
