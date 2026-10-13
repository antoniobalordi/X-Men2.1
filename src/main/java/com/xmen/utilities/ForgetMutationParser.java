package com.xmen.utilities;

import com.xmen.config.CeremonyVocabulary;
import com.xmen.config.VocabularyHolder;
import com.xmen.model.*;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * ForgetMutationParser class is responsible for parsing rules to extract Forget facts. It processes
 * each rule to find Forget(...) facts, extracts the values, and stores them in a LinkedHashSet.
 *
 * <p>Two annotations are recognised in human rules:
 *
 * <ul>
 *   <li>{@code Forget(m)} — atomic forgetting of a message (Definition 4, cases 1 and 2);</li>
 *   <li>{@code ForgetRule(r)} — procedural forgetting of a Dolev-Yao inference rule
 *       (Definition 4 case 3, Definition 5), e.g. {@code ForgetRule('r_sdec')}.</li>
 * </ul>
 *
 * Both are removed from the rule so they never reach the generated models.
 */
@Component
@Slf4j
public class ForgetMutationParser {

  // Pattern to match rule names: rule RuleName:
  private static final Pattern RULE_PATTERN = Pattern.compile("rule\\s+(\\w+)\\s*:");

  // Pattern to match Forget facts: Forget(value)
  private static final Pattern FORGET_PATTERN = Pattern.compile("Forget\\s*\\(([^)]+)\\)");

  // Pattern to match ForgetRule facts: ForgetRule('r_sdec')
  private static final Pattern FORGET_RULE_PATTERN = Pattern.compile("ForgetRule\\s*\\(([^)]+)\\)");

  // "functions: k/2, f/1 [private], ..." (one declaration list per line)
  private static final Pattern FUNCTIONS_LINE = Pattern.compile("(?m)^\\s*functions\\s*:(.*)$");
  private static final Pattern FUNCTION_DECL =
      Pattern.compile("([A-Za-z_][A-Za-z0-9_]*)\\s*/\\s*\\d+\\s*(\\[[^\\]]*\\])?");
  private static final Pattern BUILTINS_LINE = Pattern.compile("(?m)^\\s*builtins\\s*:(.*)$");

  /** Function symbols each Tamarin builtin theory adds (besides pairs, senc/sdec, aenc/adec). */
  private static final Map<String, List<String>> BUILTIN_FUNCTIONS = Map.of(
      "hashing", List.of("h"),
      "asymmetric-encryption", List.of("pk"),
      "signing", List.of("sign", "verify", "pk", "true"),
      "revealing-signing", List.of("revealsign", "revealverify", "getmessage", "pk", "true"),
      "symmetric-encryption", List.of());

  /**
   * Parses Forget mutations from a list of rules and adds them to the provided ParametersBundle.
   * First tries grammar-based parsing, then falls back to regex-based parsing if needed.
   *
   * @param rules The list of rules to parse.
   * @param parametersBundle The ParametersBundle to add Forget mutations to.
   * @param rawFileContent The raw file content for regex fallback (can be null).
   * @return The updated ParametersBundle with Forget mutations.
   */
  public static ParametersBundle parseForgetMutations(
      List<Rule> rules, ParametersBundle parametersBundle, String rawFileContent) {

    boolean foundForget = false;
    String forgetRuleName = forgetRuleActionName();
    Set<InferenceRule> knownRules = knownRules(rawFileContent);
    parametersBundle.setPrivateFunctions(privateFunctions(rawFileContent));

    // First try grammar-based parsing
    for (Rule rule : rules) {
      if (rule.isHuman()) {
        LinkedHashSet<String> forgetSet = new LinkedHashSet<>();
        LinkedHashSet<InferenceRule> ruleSet = new LinkedHashSet<>();

        List<Fact> actions = rule.getActions();
        Iterator<Fact> iterator = actions.iterator();
        while (iterator.hasNext()) {
          Fact fact = iterator.next();
          if ("Forget".equals(fact.getF_name())) {
            if (fact.getParameters() != null && !fact.getParameters().isEmpty()) {
              for (Object param : fact.getParameters()) {
                String forgetVal = extractParameterValue(param);
                if (forgetVal != null && !forgetVal.isEmpty()) {
                  forgetSet.add(forgetVal);
                  log.debug("Extracted Forget value: {}", forgetVal);
                }
              }
            }
            iterator.remove();
          } else if (forgetRuleName.equals(fact.getF_name())) {
            if (fact.getParameters() == null || fact.getParameters().isEmpty()) {
              throw new IllegalArgumentException(
                  forgetRuleName + "() in rule " + rule.getRule_name() + " names no inference rule.");
            }
            for (Object param : fact.getParameters()) {
              ruleSet.add(parseRule(extractParameterValue(param), rule.getRule_name(), knownRules));
            }
            iterator.remove();
          }
        }
        if (!forgetSet.isEmpty()) {
          parametersBundle.getForgetMutationSet().put(rule.getRule_name(), forgetSet);
          log.info("Found Forget values for rule {}: {}", rule.getRule_name(), forgetSet);
          foundForget = true;
        }
        if (!ruleSet.isEmpty()) {
          parametersBundle.getForgetRuleSet().put(rule.getRule_name(), ruleSet);
          log.info("Found ForgetRule targets for rule {}: {}", rule.getRule_name(), ruleSet);
          foundForget = true;
        }
      }
    }

    // If no Forget found via grammar parsing and we have raw content, try regex fallback
    if (!foundForget && rawFileContent != null && !rawFileContent.isEmpty()) {
      log.info("Grammar-based parsing found no Forget facts, trying regex fallback");
      foundForget = parseForgetWithRegex(rawFileContent, parametersBundle, knownRules);
    }

    if (!foundForget
        && parametersBundle.getForgetMutationSet().isEmpty()
        && parametersBundle.getForgetRuleSet().isEmpty()) {
      throw new IllegalArgumentException(
          "Forget function not found in any rule in the given input file. "
              + "Annotate a human rule with Forget(<message>) or ForgetRule(<inference rule>).");
    }

    return parametersBundle;
  }

  /**
   * Legacy method for backward compatibility.
   */
  public static ParametersBundle parseForgetMutations(
      List<Rule> rules, ParametersBundle parametersBundle) {
    return parseForgetMutations(rules, parametersBundle, null);
  }

  /**
   * Parses Forget facts using regex from raw file content.
   * This is a fallback when grammar-based parsing fails due to complex syntax.
   */
  private static boolean parseForgetWithRegex(
      String content, ParametersBundle parametersBundle, Set<InferenceRule> knownRules) {
    boolean foundAny = false;
    String currentRule = null;

    // Split by lines and process
    String[] lines = content.split("\\r?\\n");
    for (String line : lines) {
      // Check for rule start
      Matcher ruleMatcher = RULE_PATTERN.matcher(line);
      if (ruleMatcher.find()) {
        currentRule = ruleMatcher.group(1);
        log.debug("Found rule via regex: {}", currentRule);
      }

      // Check for Forget fact
      Matcher forgetMatcher = FORGET_PATTERN.matcher(line);
      while (forgetMatcher.find()) {
        String forgetValue = forgetMatcher.group(1).trim();
        if (forgetValue != null && !forgetValue.isEmpty()) {
          String ruleName = currentRule != null ? currentRule : "UnknownRule";

          // Get or create the forgetSet for this rule
          LinkedHashSet<String> forgetSet = parametersBundle.getForgetMutationSet()
              .computeIfAbsent(ruleName, k -> new LinkedHashSet<>());
          forgetSet.add(forgetValue);

          log.info("Found Forget value via regex in rule {}: {}", ruleName, forgetValue);
          foundAny = true;
        }
      }

      Matcher ruleForgetMatcher = FORGET_RULE_PATTERN.matcher(line);
      while (ruleForgetMatcher.find()) {
        String ruleName = currentRule != null ? currentRule : "UnknownRule";
        for (String part : ruleForgetMatcher.group(1).split(",")) {
          InferenceRule r = parseRule(part, ruleName, knownRules);
          parametersBundle.getForgetRuleSet().computeIfAbsent(ruleName, k -> new LinkedHashSet<>()).add(r);
          log.info("Found ForgetRule target via regex in rule {}: {}", ruleName, r);
          foundAny = true;
        }
      }
    }

    return foundAny;
  }

  private static String forgetRuleActionName() {
    CeremonyVocabulary v = VocabularyHolder.get();
    if (v != null && v.getActions() != null && v.getActions().getForgetRule() != null) {
      return v.getActions().getForgetRule();
    }
    return "ForgetRule";
  }

  /**
   * Parses and validates the target of a ForgetRule annotation. A rule that does not exist in the
   * theory cannot be forgotten: the request is rejected instead of silently doing nothing.
   */
  private static InferenceRule parseRule(String raw, String ruleName, Set<InferenceRule> knownRules) {
    InferenceRule r;
    try {
      r = InferenceRule.parse(raw);
    } catch (IllegalArgumentException e) {
      throw new IllegalArgumentException(
          "ForgetRule in rule " + ruleName + ": '" + raw + "' is not an inference rule name. "
              + "Supported rules for this theory: " + new TreeSet<>(knownRules) + ".");
    }
    if (!knownRules.contains(r)) {
      throw new IllegalArgumentException(
          "ForgetRule in rule " + ruleName + ": unknown inference rule '" + r + "'. "
              + "Supported rules for this theory: " + new TreeSet<>(knownRules) + ".");
    }
    return r;
  }

  /**
   * The inference rules that exist for the theory: the paper's R plus the composition rule r_f of
   * every function symbol declared with {@code functions:} or provided by a {@code builtins:}
   * theory.
   */
  public static Set<InferenceRule> knownRules(String rawFileContent) {
    Set<InferenceRule> out = new TreeSet<>(InferenceRule.PAPER_RULES);
    if (rawFileContent == null) return out;
    Matcher fl = FUNCTIONS_LINE.matcher(rawFileContent);
    while (fl.find()) {
      Matcher d = FUNCTION_DECL.matcher(fl.group(1));
      while (d.find()) out.add(InferenceRule.forFunction(d.group(1)));
    }
    Matcher bl = BUILTINS_LINE.matcher(rawFileContent);
    while (bl.find()) {
      for (String b : bl.group(1).split(",")) {
        for (String f : BUILTIN_FUNCTIONS.getOrDefault(b.trim().toLowerCase(Locale.ROOT), List.of())) {
          out.add(InferenceRule.forFunction(f));
        }
      }
    }
    return out;
  }

  /** Function symbols declared with the {@code [private]} attribute. */
  public static Set<String> privateFunctions(String rawFileContent) {
    Set<String> out = new TreeSet<>();
    if (rawFileContent == null) return out;
    Matcher fl = FUNCTIONS_LINE.matcher(rawFileContent);
    while (fl.find()) {
      Matcher d = FUNCTION_DECL.matcher(fl.group(1));
      while (d.find()) {
        String attrs = d.group(2);
        if (attrs != null && attrs.toLowerCase(Locale.ROOT).contains("private")) {
          out.add(d.group(1).toLowerCase(Locale.ROOT));
        }
      }
    }
    return out;
  }

  /**
   * Extracts the string value from a parameter of any supported type.
   * Handles Value, FSpecial, PSpecial, Nary_app, and String types.
   *
   * @param param The parameter object to extract the value from.
   * @return The string representation of the value, or null if not supported.
   */
  private static String extractParameterValue(Object param) {
    if (param == null) {
      return null;
    }

    if (param instanceof Value) {
      return ((Value) param).getName();
    } else if (param instanceof FSpecial) {
      // FSpecial represents function applications like senc{x}k
      return param.toString();
    } else if (param instanceof PSpecial) {
      // PSpecial represents tuple/group like <x, y>
      return param.toString();
    } else if (param instanceof Nary_app) {
      // Nary_app represents function calls like func(args)
      return param.toString();
    } else if (param instanceof String) {
      return (String) param;
    } else {
      // Fallback: use toString() representation
      log.debug("Unknown parameter type in Forget: {}, using toString()", param.getClass().getSimpleName());
      return param.toString();
    }
  }
}
