package com.xmen.service.derivation;

import com.xmen.model.Derivation;
import com.xmen.model.InferenceRule;
import com.xmen.model.Message;
import com.xmen.model.Pair;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Enumerates the normal derivations {@code Π_m} of a target from a knowledge set (journal Sec. 3.2).
 *
 * <p>A derivation is normal iff no term occurs twice on any root-to-leaf path. This forbids the
 * paper's "rule application immediately undone by its inverse" (e.g. {@code fst(<a,b>)} repeats
 * {@code a}, {@code senc(sdec(c,k),k)} repeats {@code c}) and every longer detour, and makes the
 * set finite (see IMPLEMENTATION_PLAN.md, B.1 item 1).
 *
 * <p>Search is backwards from the target. A node may be:
 *
 * <ul>
 *   <li>a hypothesis ({@code Initial}) if the term is in the knowledge;</li>
 *   <li>a composition from its immediate arguments ({@code Pairing}, {@code Encryption},
 *       {@code PredictiveFunction(f)});</li>
 *   <li>a projection of a derivable pair, or a decryption of a derivable ciphertext together with
 *       a derivation of its decryption key. In a normal derivation such a pair / ciphertext is a
 *       subterm of the knowledge (composing it would repeat the target on the path), so candidates
 *       are taken from {@code St(K)}.</li>
 * </ul>
 *
 * <p>Every rule application lists all its premises, so the leaves are exactly {@code Hyp_π}.
 * When a depth or count limit cuts the enumeration, {@link Result#truncated()} is set; callers
 * must not treat a truncated result as the complete set {@code Π_m}.
 */
public final class NormalDerivationEnumerator {

  /** Enumeration outcome. */
  public record Result(Set<Derivation> derivations, boolean truncated) {}

  private final Set<String> privateFunctions;
  private final int maxPerNode;
  private final DolevYaoDeducer deducer;

  /**
   * @param privateFunctions function symbols that cannot be composed
   * @param maxPerNode maximum number of alternative derivations kept for one node
   */
  public NormalDerivationEnumerator(Set<String> privateFunctions, int maxPerNode) {
    this.privateFunctions = privateFunctions == null ? Set.of() : privateFunctions;
    this.maxPerNode = Math.max(1, maxPerNode);
    this.deducer = new DolevYaoDeducer(this.privateFunctions);
  }

  /**
   * @param depthLimit maximal height of a derivation tree; {@link Integer#MAX_VALUE} for no limit
   */
  public Result enumerate(Message target, Collection<Message> knowledge, int depthLimit) {
    if (target == null || knowledge == null) return new Result(Collections.emptySet(), false);
    return new Run(knowledge).run(target, depthLimit);
  }

  private final class Run {
    private final Set<Message> knowledge;
    private final Map<Message, List<Pair>> pairsByComponent = new LinkedHashMap<>();
    private final Map<Message, List<DolevYaoTerms.Cipher>> ciphersByPlaintext = new LinkedHashMap<>();
    private Set<Message> derivableClosure; // lazily computed, only to qualify truncation
    private boolean truncated;

    Run(Collection<Message> knowledge) {
      this.knowledge = new LinkedHashSet<>(knowledge);
      for (Message s : DolevYaoTerms.subterms(this.knowledge)) {
        if (s instanceof Pair p) {
          pairsByComponent.computeIfAbsent(p.getLeft(), x -> new ArrayList<>()).add(p);
          if (!p.getRight().equals(p.getLeft())) {
            pairsByComponent.computeIfAbsent(p.getRight(), x -> new ArrayList<>()).add(p);
          }
        }
        DolevYaoTerms.asCipher(s).ifPresent(
            c -> ciphersByPlaintext.computeIfAbsent(c.plaintext(), x -> new ArrayList<>()).add(c));
      }
    }

    Result run(Message target, int depthLimit) {
      List<Derivation> ds = derive(target, new HashSet<>(), depthLimit);
      return new Result(Collections.unmodifiableSet(new LinkedHashSet<>(ds)), truncated);
    }

    private List<Derivation> derive(Message t, Set<Message> path, int depthLeft) {
      if (path.contains(t)) return List.of();
      if (depthLeft < 0) {
        if (isDerivable(t)) truncated = true;
        return List.of();
      }
      int next = depthLeft == Integer.MAX_VALUE ? depthLeft : depthLeft - 1;
      path.add(t);
      try {
        Set<Derivation> out = new LinkedHashSet<>();

        if (knowledge.contains(t)) {
          out.add(new Derivation(t, "Initial", List.of(), null));
        }

        InferenceRule composition = DolevYaoTerms.compositionRule(t, privateFunctions);
        if (composition != null) {
          List<List<Derivation>> options = new ArrayList<>();
          for (Message arg : DolevYaoTerms.compositionArgs(t)) {
            List<Derivation> ds = derive(arg, path, next);
            if (ds.isEmpty()) {
              options = null;
              break;
            }
            options.add(ds);
          }
          if (options != null) {
            addProducts(out, t, DolevYaoTerms.compositionLabel(t), composition, options);
          }
        }

        for (Pair p : pairsByComponent.getOrDefault(t, List.of())) {
          List<Derivation> sources = derive(p, path, next);
          for (Derivation src : sources) {
            if (p.getLeft().equals(t)) {
              add(out, new Derivation(t, "Projection-First", List.of(src), InferenceRule.UNPAIR));
            }
            if (p.getRight().equals(t)) {
              add(out, new Derivation(t, "Projection-Second", List.of(src), InferenceRule.UNPAIR));
            }
          }
        }

        for (DolevYaoTerms.Cipher c : ciphersByPlaintext.getOrDefault(t, List.of())) {
          List<Derivation> cts = derive(c.ciphertext(), path, next);
          if (cts.isEmpty()) continue;
          List<Derivation> keys = derive(c.key(), path, next);
          if (keys.isEmpty()) continue;
          String label = (c.rule().equals(InferenceRule.ADEC) ? "AsymDecryption(" : "Decryption(")
              + c.ciphertext().represent() + ")";
          addProducts(out, t, label, c.rule(), List.of(cts, keys));
        }

        return new ArrayList<>(out);
      } finally {
        path.remove(t);
      }
    }

    private void addProducts(Set<Derivation> out, Message t, String label, InferenceRule rule,
                             List<List<Derivation>> options) {
      int[] idx = new int[options.size()];
      while (true) {
        if (out.size() >= maxPerNode) {
          truncated = true;
          return;
        }
        List<Derivation> premises = new ArrayList<>(options.size());
        for (int i = 0; i < idx.length; i++) premises.add(options.get(i).get(idx[i]));
        out.add(new Derivation(t, label, List.copyOf(premises), rule));
        int i = idx.length - 1;
        while (i >= 0 && ++idx[i] == options.get(i).size()) {
          idx[i] = 0;
          i--;
        }
        if (i < 0) return;
      }
    }

    private void add(Set<Derivation> out, Derivation d) {
      if (out.size() >= maxPerNode) {
        truncated = true;
        return;
      }
      out.add(d);
    }

    private boolean isDerivable(Message t) {
      if (derivableClosure == null) {
        derivableClosure = deducer.analyse(knowledge, DolevYaoDeducer.ALL_RULES);
      }
      return deducer.synthesisable(t, derivableClosure, DolevYaoDeducer.ALL_RULES);
    }
  }
}
