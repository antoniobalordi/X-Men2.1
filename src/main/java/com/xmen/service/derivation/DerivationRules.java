package com.xmen.service.derivation;

import com.xmen.model.Derivation;
import com.xmen.model.Encrypt;
import com.xmen.model.InferenceRule;
import com.xmen.model.Message;
import com.xmen.model.Pair;
import com.xmen.model.PredictiveFunction;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

/** Operations on derivation trees needed by the Forget mutation. */
public final class DerivationRules {

  private DerivationRules() {}

  /**
   * {@code Rules(π)} of Definition 5: the distinct inference rules applied in {@code π}. A rule
   * applied several times appears once.
   */
  public static Set<InferenceRule> rulesOf(Derivation pi) {
    Set<InferenceRule> out = new TreeSet<>();
    collect(pi, out);
    return out;
  }

  private static void collect(Derivation d, Set<InferenceRule> out) {
    if (d == null) return;
    if (d.getInferenceRule() != null) out.add(d.getInferenceRule());
    for (Derivation p : d.getPremises()) collect(p, out);
  }

  /**
   * Recomputes the conclusion of {@code pi} after replacing hypotheses (leaves) according to
   * {@code leafSubstitution}. This is how Algorithm 1 (line 28) builds the variant {@code [[m2]]}:
   * the replaced hypotheses flow through the same rule applications.
   *
   * @return the new conclusion, or empty if some rule application is no longer valid (e.g. a
   *     ciphertext is decrypted with a substituted key that does not match)
   */
  public static Optional<Message> replay(Derivation pi, Map<Message, Message> leafSubstitution) {
    return Optional.ofNullable(replayNode(pi, leafSubstitution));
  }

  private static Message replayNode(Derivation d, Map<Message, Message> sub) {
    List<Derivation> ps = d.getPremises();
    InferenceRule rule = d.getInferenceRule();
    if (rule == null) {
      return sub.getOrDefault(d.getGoal(), d.getGoal());
    }
    List<Message> in = new ArrayList<>(ps.size());
    for (Derivation p : ps) {
      Message m = replayNode(p, sub);
      if (m == null) return null;
      in.add(m);
    }
    String label = d.getRule();
    if (label.startsWith("Projection-")) {
      if (!(in.get(0) instanceof Pair p)) return null;
      return label.equals("Projection-First") ? p.getLeft() : p.getRight();
    }
    if (label.startsWith("Decryption") || label.startsWith("AsymDecryption")) {
      Optional<DolevYaoTerms.Cipher> c = DolevYaoTerms.asCipher(in.get(0));
      if (c.isEmpty() || !c.get().rule().equals(rule) || !c.get().key().equals(in.get(1))) return null;
      return c.get().plaintext();
    }
    Message goal = d.getGoal();
    if (goal instanceof Pair) return new Pair(in.get(0), in.get(1));
    if (goal instanceof Encrypt) return new Encrypt(in.get(0), in.get(1));
    if (goal instanceof PredictiveFunction f) return new PredictiveFunction(f.getName(), List.copyOf(in));
    return null;
  }
}
