package com.xmen.model;

import java.util.List;
import java.util.Objects;

/**
 * A derivation tree node: {@code goal} is obtained by applying {@code rule} to the conclusions of
 * {@code premises}. Leaves carry the label {@code "Initial"} and are the hypotheses of the
 * derivation ({@code Hyp_π}).
 *
 * <p>Premise order is fixed per rule: {@code Pairing} [left, right]; {@code Projection-First} /
 * {@code Projection-Second} [pair]; {@code Decryption(c)} / {@code AsymDecryption(c)} [ciphertext,
 * decryption key]; {@code Encryption} [plaintext, key]; {@code PredictiveFunction(f)} [arguments].
 */
public class Derivation {

  private final Message goal;
  private final String rule; // e.g., "Initial", "Pairing", "Decryption(..)", "Projection-First", ...
  private final List<Derivation> premises;
  private final InferenceRule inferenceRule; // null for hypotheses ("Initial")

  public Derivation(Message goal, String rule, List<Derivation> premises) {
    this(goal, rule, premises, inferRule(rule));
  }

  public Derivation(Message goal, String rule, List<Derivation> premises, InferenceRule inferenceRule) {
    this.goal = goal;
    this.rule = rule;
    this.premises = premises;
    this.inferenceRule = inferenceRule;
  }

  public Message getGoal() {
    return goal;
  }

  public String getRule() {
    return rule;
  }

  public List<Derivation> getPremises() {
    return premises;
  }

  /** The Dolev-Yao rule applied at this node, or {@code null} for a hypothesis leaf. */
  public InferenceRule getInferenceRule() {
    return inferenceRule;
  }

  /** Maps the textual node labels used throughout X-Men to the rule of the paper. */
  static InferenceRule inferRule(String label) {
    if (label == null || label.equals("Initial")) return null;
    if (label.equals("Pairing")) return InferenceRule.PAIR;
    if (label.startsWith("Projection")) return InferenceRule.UNPAIR;
    if (label.startsWith("AsymDecryption")) return InferenceRule.ADEC;
    if (label.startsWith("Decryption")) return InferenceRule.SDEC;
    if (label.equals("Encryption")) return InferenceRule.SENC;
    if (label.startsWith("PredictiveFunction(") && label.endsWith(")")) {
      return InferenceRule.forFunction(label.substring("PredictiveFunction(".length(), label.length() - 1));
    }
    return null;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof Derivation that)) return false;
    return goal.equals(that.goal) && rule.equals(that.rule) && premises.equals(that.premises);
  }

  @Override
  public int hashCode() {
    return Objects.hash(goal, rule, premises);
  }
}
