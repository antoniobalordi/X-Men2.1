package com.xmen.service.derivation;

import com.xmen.model.Encrypt;
import com.xmen.model.InferenceRule;
import com.xmen.model.Message;
import com.xmen.model.Pair;
import com.xmen.model.PredictiveFunction;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;

/**
 * Classification of message terms for the Dolev-Yao inference rules (journal Sec. 3.2).
 *
 * <ul>
 *   <li>Composition: every non-atomic term is built from its immediate arguments by one rule —
 *       pairs by {@code r_pair}, {@code senc}/{@code {m}_{k}} by {@code r_senc}, {@code aenc} by
 *       {@code r_aenc}, any other public function symbol {@code f} by {@code r_f}. Functions
 *       declared {@code [private]} cannot be composed.</li>
 *   <li>Decomposition: pairs are projected by {@code r_unpair}; {@code senc(m,k)} (and the legacy
 *       {@code Encrypt}) is decrypted with {@code k} by {@code r_sdec}; {@code aenc(m,pk(sk))} is
 *       decrypted with {@code sk} by {@code r_adec}. No other term can be decomposed.</li>
 * </ul>
 */
public final class DolevYaoTerms {

  private DolevYaoTerms() {}

  /** A decomposable ciphertext: decrypting {@code ciphertext} with {@code key} yields {@code plaintext}. */
  public record Cipher(Message ciphertext, Message plaintext, Message key, InferenceRule rule) {}

  /** Returns the ciphertext view of {@code m}, if it can be decrypted at all. */
  public static Optional<Cipher> asCipher(Message m) {
    if (m instanceof Encrypt e) {
      return Optional.of(new Cipher(m, e.getMsg(), e.getKey(), InferenceRule.SDEC));
    }
    if (m instanceof PredictiveFunction f && f.getArgs().size() == 2) {
      String name = f.getName().toLowerCase(Locale.ROOT);
      if (name.equals("senc")) {
        return Optional.of(new Cipher(m, f.getArgs().get(0), f.getArgs().get(1), InferenceRule.SDEC));
      }
      if (name.equals("aenc")
          && f.getArgs().get(1) instanceof PredictiveFunction pk
          && pk.getName().equalsIgnoreCase("pk")
          && pk.getArgs().size() == 1) {
        return Optional.of(new Cipher(m, f.getArgs().get(0), pk.getArgs().get(0), InferenceRule.ADEC));
      }
    }
    return Optional.empty();
  }

  /**
   * The rule composing {@code m} from {@link #compositionArgs(Message)}, or {@code null} if
   * {@code m} is atomic or uses a private function symbol.
   */
  public static InferenceRule compositionRule(Message m, Set<String> privateFunctions) {
    if (m instanceof Pair) return InferenceRule.PAIR;
    if (m instanceof Encrypt) return InferenceRule.SENC;
    if (m instanceof PredictiveFunction f) {
      if (isPrivate(f.getName(), privateFunctions)) return null;
      return InferenceRule.forFunction(f.getName());
    }
    return null;
  }

  /** Immediate arguments of a composite term (empty for atoms). */
  public static List<Message> compositionArgs(Message m) {
    if (m instanceof Pair p) return List.of(p.getLeft(), p.getRight());
    if (m instanceof Encrypt e) return List.of(e.getMsg(), e.getKey());
    if (m instanceof PredictiveFunction f) return f.getArgs();
    return List.of();
  }

  /** Label used in {@link com.xmen.model.Derivation} for the composition of {@code m}. */
  public static String compositionLabel(Message m) {
    if (m instanceof Pair) return "Pairing";
    if (m instanceof Encrypt) return "Encryption";
    if (m instanceof PredictiveFunction f) return "PredictiveFunction(" + f.getName() + ")";
    return "Initial";
  }

  /** All subterms {@code St(ms)} (every term is a subterm of itself). */
  public static Set<Message> subterms(Collection<Message> ms) {
    Set<Message> out = new LinkedHashSet<>();
    for (Message m : ms) addSubterms(m, out);
    return out;
  }

  private static void addSubterms(Message m, Set<Message> out) {
    if (m == null || !out.add(m)) return;
    for (Message a : compositionArgs(m)) addSubterms(a, out);
  }

  public static boolean isPrivate(String functionName, Set<String> privateFunctions) {
    return functionName != null
        && privateFunctions != null
        && privateFunctions.contains(functionName.toLowerCase(Locale.ROOT).trim());
  }
}
