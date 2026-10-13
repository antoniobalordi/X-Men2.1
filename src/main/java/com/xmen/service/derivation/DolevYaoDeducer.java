package com.xmen.service.derivation;

import com.xmen.model.InferenceRule;
import com.xmen.model.Message;
import com.xmen.model.Pair;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Exact decision procedure for "is {@code t} derivable from the hypotheses {@code H} using only
 * the allowed inference rules?".
 *
 * <p>Standard Dolev-Yao deduction with free constructors: first close {@code H} under the allowed
 * decomposition rules (projection, decryption whose key is synthesisable), then check whether
 * {@code t} can be synthesised from that closure with the allowed composition rules. Composing a
 * term and then decomposing it never yields anything new, so this is complete; it is sound because
 * every step is an application of an allowed rule. The closure only contains subterms of {@code H},
 * so the procedure terminates.
 *
 * <p>Used wherever the paper only asks whether <em>some</em> derivation exists: Definition 7 (an
 * unblocked derivation exists iff {@code t} is derivable from the non-blocked hypotheses with the
 * non-forgotten rules), the Case 2 / Case 3 closures of Definition 6, and the Neglect test of
 * Algorithm 1. Unlike the enumeration, it is not subject to depth or count limits.
 */
public final class DolevYaoDeducer {

  /** Every rule allowed. */
  public static final Predicate<InferenceRule> ALL_RULES = r -> true;

  /** Only the pairing rules (Definition 6, Case 2). */
  public static final Predicate<InferenceRule> PAIRING_RULES =
      r -> r.equals(InferenceRule.PAIR) || r.equals(InferenceRule.UNPAIR);

  private final Set<String> privateFunctions;

  public DolevYaoDeducer(Set<String> privateFunctions) {
    this.privateFunctions = privateFunctions == null ? Set.of() : privateFunctions;
  }

  /** All rules except {@code forbidden}. */
  public static Predicate<InferenceRule> excluding(Set<InferenceRule> forbidden) {
    if (forbidden == null || forbidden.isEmpty()) return ALL_RULES;
    return r -> !forbidden.contains(r);
  }

  public boolean derivable(Message target, Collection<Message> hypotheses, Predicate<InferenceRule> allowed) {
    if (target == null || hypotheses == null) return false;
    return synthesisable(target, analyse(hypotheses, allowed), allowed);
  }

  /** Closure of {@code hypotheses} under the allowed decomposition rules. */
  public Set<Message> analyse(Collection<Message> hypotheses, Predicate<InferenceRule> allowed) {
    Set<Message> known = new LinkedHashSet<>(hypotheses);
    boolean changed = true;
    while (changed) {
      changed = false;
      for (Message m : new ArrayList<>(known)) {
        if (m instanceof Pair p && allowed.test(InferenceRule.UNPAIR)) {
          changed |= known.add(p.getLeft());
          changed |= known.add(p.getRight());
        }
        Optional<DolevYaoTerms.Cipher> c = DolevYaoTerms.asCipher(m);
        if (c.isPresent()
            && allowed.test(c.get().rule())
            && !known.contains(c.get().plaintext())
            && synthesisable(c.get().key(), known, allowed)) {
          known.add(c.get().plaintext());
          changed = true;
        }
      }
    }
    return known;
  }

  /** Can {@code t} be built from {@code known} by composition rules only? */
  public boolean synthesisable(Message t, Set<Message> known, Predicate<InferenceRule> allowed) {
    if (known.contains(t)) return true;
    InferenceRule rule = DolevYaoTerms.compositionRule(t, privateFunctions);
    if (rule == null || !allowed.test(rule)) return false;
    for (Message arg : DolevYaoTerms.compositionArgs(t)) {
      if (!synthesisable(arg, known, allowed)) return false;
    }
    return true;
  }
}
