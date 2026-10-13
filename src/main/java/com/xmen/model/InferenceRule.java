package com.xmen.model;

import java.util.Locale;
import java.util.Set;
import java.util.regex.Pattern;

/**
 * Name of a Dolev-Yao inference rule, i.e. an element of the rule set {@code R} of the paper
 * (journal Sec. 3.2): {@code r_pair}, {@code r_unpair}, {@code r_senc}, {@code r_sdec},
 * {@code r_aenc}, {@code r_adec}. The two projections are one rule ({@code r_unpair}), as in the
 * paper.
 *
 * <p>Tamarin specifications also use other operators ({@code pk}, {@code h}, {@code sign},
 * user-declared functions such as {@code k/2}). Following Definition 1 ("other operators ... are
 * handled in the standard way"), every such public function symbol {@code f} has its own
 * composition rule {@code r_f} (e.g. {@code r_h}, {@code r_sign}, {@code r_k}).
 *
 * <p>Rule names are the targets of procedural forgetting ({@code ForgetRule(r)}, Definition 4
 * case 3 and Definition 5).
 */
public record InferenceRule(String id) implements Comparable<InferenceRule> {

  // Must be initialised before the constants below, which are validated against it.
  private static final Pattern ID = Pattern.compile("r_[a-z][a-z0-9_]*");

  public static final InferenceRule PAIR = new InferenceRule("r_pair");
  public static final InferenceRule UNPAIR = new InferenceRule("r_unpair");
  public static final InferenceRule SENC = new InferenceRule("r_senc");
  public static final InferenceRule SDEC = new InferenceRule("r_sdec");
  public static final InferenceRule AENC = new InferenceRule("r_aenc");
  public static final InferenceRule ADEC = new InferenceRule("r_adec");

  /** The rule set R of the paper (Sec. 3.2). */
  public static final Set<InferenceRule> PAPER_RULES = Set.of(PAIR, UNPAIR, SENC, SDEC, AENC, ADEC);

  public InferenceRule {
    if (id == null || !ID.matcher(id).matches()) {
      throw new IllegalArgumentException("Invalid inference rule name: " + id);
    }
  }

  /** The rule that applies (composes) the function symbol {@code f}. */
  public static InferenceRule forFunction(String f) {
    String name = f.trim().toLowerCase(Locale.ROOT);
    return switch (name) {
      case "pair" -> PAIR;
      case "fst", "snd" -> UNPAIR;
      case "senc" -> SENC;
      case "sdec" -> SDEC;
      case "aenc" -> AENC;
      case "adec" -> ADEC;
      default -> new InferenceRule("r_" + name);
    };
  }

  /**
   * Parses a rule name written by the user in a {@code ForgetRule(...)} annotation. Accepts the
   * paper's names ({@code r_sdec}), the bare operator names ({@code sdec}, {@code pair},
   * {@code unpair}, {@code fst}, {@code snd}, {@code h}, ...), optionally quoted.
   *
   * @throws IllegalArgumentException if the text is not a syntactically valid rule name
   */
  public static InferenceRule parse(String raw) {
    if (raw == null) throw new IllegalArgumentException("Missing inference rule name");
    String s = raw.trim();
    if (s.length() >= 2
        && ((s.startsWith("'") && s.endsWith("'")) || (s.startsWith("\"") && s.endsWith("\"")))) {
      s = s.substring(1, s.length() - 1).trim();
    }
    s = s.toLowerCase(Locale.ROOT);
    if (s.startsWith("r_")) s = s.substring(2);
    if (s.equals("projection") || s.equals("proj")) s = "unpair";
    if (s.equals("pairing")) s = "pair";
    if (s.isEmpty()) throw new IllegalArgumentException("Invalid inference rule name: " + raw);
    if (s.equals("unpair")) return UNPAIR;
    try {
      return forFunction(s);
    } catch (IllegalArgumentException e) {
      throw new IllegalArgumentException("Invalid inference rule name: " + raw, e);
    }
  }

  public boolean isPaperRule() {
    return PAPER_RULES.contains(this);
  }

  @Override
  public int compareTo(InferenceRule o) {
    return id.compareTo(o.id);
  }

  @Override
  public String toString() {
    return id;
  }
}
