package com.xmen.service.derivation.reference;

import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.a;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.aenc;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.fn;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.pair;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.pk;
import static com.xmen.service.derivation.reference.ReferenceDerivationOracle.senc;

import com.xmen.model.Message;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

/** Seeded generator of small Dolev-Yao instances (knowledge, target) for differential tests. */
public final class RandomInstances {

  public record Instance(Set<Message> knowledge, Message target) {}

  private static final List<Message> ATOMS = List.of(a("a"), a("b"), a("c"), a("k"));

  private final Random rnd;

  public RandomInstances(long seed) {
    this.rnd = new Random(seed);
  }

  public Instance next() {
    Set<Message> k = new LinkedHashSet<>();
    int n = 2 + rnd.nextInt(3);
    for (int i = 0; i < n; i++) k.add(term(2));
    int atoms = rnd.nextInt(3);
    for (int i = 0; i < atoms; i++) k.add(atom());
    Message target;
    List<Message> sub = new ArrayList<>(subterms(k));
    if (rnd.nextBoolean()) {
      target = sub.get(rnd.nextInt(sub.size()));
    } else {
      Message x = sub.get(rnd.nextInt(sub.size()));
      Message y = sub.get(rnd.nextInt(sub.size()));
      target = switch (rnd.nextInt(4)) {
        case 0 -> pair(x, y);
        case 1 -> senc(x, y);
        case 2 -> fn("h", x);
        default -> x;
      };
    }
    return new Instance(k, target);
  }

  /** A random subset of {@code from}. */
  public Set<Message> subset(Set<Message> from, double p) {
    Set<Message> out = new LinkedHashSet<>();
    for (Message m : from) if (rnd.nextDouble() < p) out.add(m);
    return out;
  }

  public int nextInt(int bound) {
    return rnd.nextInt(bound);
  }

  private Message atom() {
    return ATOMS.get(rnd.nextInt(ATOMS.size()));
  }

  private Message term(int depth) {
    if (depth == 0 || rnd.nextInt(3) == 0) return atom();
    return switch (rnd.nextInt(5)) {
      case 0, 1 -> pair(term(depth - 1), term(depth - 1));
      case 2 -> senc(term(depth - 1), rnd.nextBoolean() ? atom() : term(depth - 1));
      case 3 -> aenc(term(depth - 1), pk(atom()));
      default -> fn("h", term(depth - 1));
    };
  }

  public static Set<Message> subterms(Set<Message> ms) {
    Set<Message> out = new LinkedHashSet<>();
    for (Message m : ms) ReferenceDerivationOracle.subterms(m, out);
    return out;
  }
}
