package com.xmen.service.derivation.reference;

import com.xmen.model.Atom;
import com.xmen.model.Derivation;
import com.xmen.model.Encrypt;
import com.xmen.model.Message;
import com.xmen.model.Pair;
import com.xmen.model.PredictiveFunction;

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
 * Independent reference oracle for the derivation audit (test code only).
 *
 * <p>It shares no code with the production derivation engine. Where the production engine
 * searches backwards from the target, this oracle generates derivation trees FORWARDS,
 * bottom-up, until a fixpoint is reached:
 *
 * <ul>
 *   <li>round 0: one leaf {@code K} per hypothesis in the knowledge;</li>
 *   <li>round n+1: every rule application whose premises are trees of earlier rounds.</li>
 * </ul>
 *
 * <p>The rules are the Dolev-Yao rules of the paper (Sec. 3.2) extended to Tamarin operators:
 * pair composition / both projections, composition of every public function symbol (incl.
 * {@code senc}, {@code aenc}, {@code pk}, {@code h} and user functions), symmetric decryption of
 * {@code senc(m,k)} (and of the legacy {@code Encrypt} class) with {@code k}, asymmetric decryption
 * of {@code aenc(m,pk(sk))} with {@code sk}.
 *
 * <p>A derivation is <em>normal</em> iff no term occurs twice on any root-to-leaf path (see
 * IMPLEMENTATION_PLAN.md, B.1 item 1). Because a normal derivation only contains subterms of
 * {@code K ∪ {t}} (locality, Rusinowitch-Turuani), generation is restricted to that universe and
 * terminates.
 *
 * <p>Trees are compared with the production engine through a canonical string (see
 * {@link #canonical(Derivation)}).
 */
public final class ReferenceDerivationOracle {

  /** Thrown when an instance is too large to enumerate exhaustively. */
  public static final class TooLargeException extends RuntimeException {
    public TooLargeException(String msg) {
      super(msg);
    }
  }

  /** A derivation tree built by the oracle. */
  public static final class RTree {
    final Message term;
    final String kind; // K, pair, fst, snd, sdec, adec, senc, app:f
    final List<RTree> children;
    final Set<Message> terms; // all terms occurring in the tree
    final String canon;

    RTree(Message term, String kind, List<RTree> children) {
      this.term = term;
      this.kind = kind;
      this.children = children;
      Set<Message> ts = new HashSet<>();
      ts.add(term);
      StringBuilder sb = new StringBuilder();
      sb.append(term.represent()).append('{').append(kind).append("}(");
      for (int i = 0; i < children.size(); i++) {
        RTree c = children.get(i);
        ts.addAll(c.terms);
        if (i > 0) sb.append(';');
        sb.append(c.canon);
      }
      sb.append(')');
      this.terms = ts;
      this.canon = sb.toString();
    }

    public Message term() {
      return term;
    }

    public String canon() {
      return canon;
    }

    /** Leaves (hypotheses) of the tree. */
    public Set<Message> hypotheses() {
      Set<Message> out = new LinkedHashSet<>();
      collectLeaves(this, out);
      return out;
    }

    /** Paper rule names (r_pair, r_unpair, ...) used in the tree. */
    public Set<String> rules() {
      Set<String> out = new LinkedHashSet<>();
      collectRules(this, out);
      return out;
    }

    private static void collectLeaves(RTree t, Set<Message> out) {
      if (t.kind.equals("K")) {
        out.add(t.term);
        return;
      }
      for (RTree c : t.children) collectLeaves(c, out);
    }

    private static void collectRules(RTree t, Set<String> out) {
      switch (t.kind) {
        case "K" -> {}
        case "pair" -> out.add("r_pair");
        case "fst", "snd" -> out.add("r_unpair");
        case "sdec" -> out.add("r_sdec");
        case "adec" -> out.add("r_adec");
        case "senc" -> out.add("r_senc");
        default -> {
          String f = t.kind.substring("app:".length()).toLowerCase();
          switch (f) {
            case "senc" -> out.add("r_senc");
            case "aenc" -> out.add("r_aenc");
            default -> out.add("r_" + f);
          }
        }
      }
      for (RTree c : t.children) collectRules(c, out);
    }
  }

  private final Set<String> privateFunctions;
  private final Set<String> allowedKinds; // null = all
  private final int maxTrees;

  public ReferenceDerivationOracle() {
    this(Set.of(), null, 20000);
  }

  /**
   * @param privateFunctions function symbols that cannot be composed
   * @param allowedKinds restrict the rules used ("pair","fst","snd",...,"app:*"), null = all
   * @param maxTrees abort with {@link TooLargeException} beyond this many trees
   */
  public ReferenceDerivationOracle(Set<String> privateFunctions, Set<String> allowedKinds, int maxTrees) {
    this.privateFunctions = privateFunctions;
    this.allowedKinds = allowedKinds;
    this.maxTrees = maxTrees;
  }

  /** Oracle restricted to the pairing rules (Definition 6, Case 2). */
  public static ReferenceDerivationOracle pairingOnly() {
    return new ReferenceDerivationOracle(Set.of(), Set.of("pair", "fst", "snd"), 20000);
  }

  // ---------------------------------------------------------------------------------------------
  // Enumeration
  // ---------------------------------------------------------------------------------------------

  /** All normal derivation trees of {@code target} from {@code knowledge}. */
  public List<RTree> derivations(Message target, Collection<Message> knowledge) {
    Set<Message> universe = new LinkedHashSet<>();
    for (Message k : knowledge) subterms(k, universe);
    subterms(target, universe);

    Map<String, RTree> all = new LinkedHashMap<>();
    Map<Message, List<RTree>> byTerm = new LinkedHashMap<>();
    for (Message k : knowledge) add(new RTree(k, "K", List.of()), all, byTerm);

    boolean changed = true;
    while (changed) {
      changed = false;
      Map<Message, List<RTree>> snapshot = new LinkedHashMap<>();
      byTerm.forEach((k, v) -> snapshot.put(k, new ArrayList<>(v)));
      List<RTree> fresh = new ArrayList<>();

      // Composition of every composite term of the universe.
      for (Message u : universe) {
        String kind = compositionKind(u);
        if (kind == null || !allowed(kind)) continue;
        List<Message> args = args(u);
        List<List<RTree>> options = new ArrayList<>();
        boolean possible = true;
        for (Message a : args) {
          List<RTree> opts = snapshot.getOrDefault(a, List.of());
          if (opts.isEmpty()) {
            possible = false;
            break;
          }
          options.add(opts);
        }
        if (!possible) continue;
        for (List<RTree> combo : product(options)) {
          if (combo.stream().noneMatch(c -> c.terms.contains(u))) {
            fresh.add(new RTree(u, kind, combo));
          }
        }
      }

      // Decomposition.
      for (List<RTree> trees : snapshot.values()) {
        for (RTree src : trees) {
          Message s = src.term;
          if (s instanceof Pair p) {
            if (allowed("fst") && !src.terms.contains(p.getLeft())) {
              fresh.add(new RTree(p.getLeft(), "fst", List.of(src)));
            }
            if (allowed("snd") && !src.terms.contains(p.getRight())) {
              fresh.add(new RTree(p.getRight(), "snd", List.of(src)));
            }
          }
          Message[] sym = symmetric(s);
          if (sym != null && allowed("sdec")) {
            for (RTree key : snapshot.getOrDefault(sym[1], List.of())) {
              if (!src.terms.contains(sym[0]) && !key.terms.contains(sym[0])) {
                fresh.add(new RTree(sym[0], "sdec", List.of(src, key)));
              }
            }
          }
          Message[] asym = asymmetric(s);
          if (asym != null && allowed("adec")) {
            for (RTree key : snapshot.getOrDefault(asym[1], List.of())) {
              if (!src.terms.contains(asym[0]) && !key.terms.contains(asym[0])) {
                fresh.add(new RTree(asym[0], "adec", List.of(src, key)));
              }
            }
          }
        }
      }

      for (RTree t : fresh) {
        if (add(t, all, byTerm)) {
          changed = true;
          if (all.size() > maxTrees) {
            throw new TooLargeException("more than " + maxTrees + " trees");
          }
        }
      }
    }
    return Collections.unmodifiableList(byTerm.getOrDefault(target, List.of()));
  }

  /** True iff {@code target} has at least one derivation from {@code knowledge}. */
  public boolean derivable(Message target, Collection<Message> knowledge) {
    return !derivations(target, knowledge).isEmpty();
  }

  // ---------------------------------------------------------------------------------------------
  // Canonical comparison with the production engine
  // ---------------------------------------------------------------------------------------------

  /** Canonical string of a production {@link Derivation}, in the oracle's vocabulary. */
  public static String canonical(Derivation d) {
    String rule = d.getRule();
    String kind;
    if (rule.equals("Initial")) kind = "K";
    else if (rule.equals("Pairing")) kind = "pair";
    else if (rule.startsWith("Projection-First")) kind = "fst";
    else if (rule.startsWith("Projection-Second")) kind = "snd";
    else if (rule.startsWith("AsymDecryption")) kind = "adec";
    else if (rule.startsWith("Decryption")) kind = "sdec";
    else if (rule.equals("Encryption")) kind = "senc";
    else if (rule.startsWith("PredictiveFunction(")) {
      kind = "app:" + rule.substring("PredictiveFunction(".length(), rule.length() - 1);
    } else {
      kind = "?" + rule;
    }
    StringBuilder sb = new StringBuilder();
    sb.append(d.getGoal().represent()).append('{').append(kind).append("}(");
    List<Derivation> ps = d.getPremises();
    for (int i = 0; i < ps.size(); i++) {
      if (i > 0) sb.append(';');
      sb.append(canonical(ps.get(i)));
    }
    sb.append(')');
    return sb.toString();
  }

  public static Set<String> canonicalSet(Collection<Derivation> ds) {
    Set<String> out = new java.util.TreeSet<>();
    for (Derivation d : ds) out.add(canonical(d));
    return out;
  }

  public static Set<String> canonicalTrees(Collection<RTree> ts) {
    Set<String> out = new java.util.TreeSet<>();
    for (RTree t : ts) out.add(t.canon);
    return out;
  }

  // ---------------------------------------------------------------------------------------------
  // Term helpers (deliberately independent from production code)
  // ---------------------------------------------------------------------------------------------

  private boolean allowed(String kind) {
    if (allowedKinds == null) return true;
    if (kind.startsWith("app:")) return allowedKinds.contains("app:*") || allowedKinds.contains(kind);
    return allowedKinds.contains(kind);
  }

  private String compositionKind(Message u) {
    if (u instanceof Pair) return "pair";
    if (u instanceof Encrypt) return "senc";
    if (u instanceof PredictiveFunction f) {
      if (privateFunctions.contains(f.getName().toLowerCase())) return null;
      return "app:" + f.getName();
    }
    return null;
  }

  private static List<Message> args(Message u) {
    if (u instanceof Pair p) return List.of(p.getLeft(), p.getRight());
    if (u instanceof Encrypt e) return List.of(e.getMsg(), e.getKey());
    if (u instanceof PredictiveFunction f) return f.getArgs();
    return List.of();
  }

  private static Message[] symmetric(Message s) {
    if (s instanceof Encrypt e) return new Message[] {e.getMsg(), e.getKey()};
    if (s instanceof PredictiveFunction f && f.getName().equalsIgnoreCase("senc") && f.getArgs().size() == 2) {
      return new Message[] {f.getArgs().get(0), f.getArgs().get(1)};
    }
    return null;
  }

  private static Message[] asymmetric(Message s) {
    if (s instanceof PredictiveFunction f && f.getName().equalsIgnoreCase("aenc") && f.getArgs().size() == 2) {
      Message key = f.getArgs().get(1);
      if (key instanceof PredictiveFunction pk && pk.getName().equalsIgnoreCase("pk") && pk.getArgs().size() == 1) {
        return new Message[] {f.getArgs().get(0), pk.getArgs().get(0)};
      }
    }
    return null;
  }

  public static void subterms(Message m, Set<Message> out) {
    if (m == null || !out.add(m)) return;
    for (Message a : args(m)) subterms(a, out);
  }

  private static boolean add(RTree t, Map<String, RTree> all, Map<Message, List<RTree>> byTerm) {
    if (all.containsKey(t.canon)) return false;
    all.put(t.canon, t);
    byTerm.computeIfAbsent(t.term, k -> new ArrayList<>()).add(t);
    return true;
  }

  private static List<List<RTree>> product(List<List<RTree>> options) {
    List<List<RTree>> out = new ArrayList<>();
    out.add(new ArrayList<>());
    for (List<RTree> opts : options) {
      List<List<RTree>> next = new ArrayList<>();
      for (List<RTree> prefix : out) {
        for (RTree o : opts) {
          List<RTree> l = new ArrayList<>(prefix);
          l.add(o);
          next.add(l);
        }
      }
      out = next;
    }
    return out;
  }

  /** Convenience constructors for tests. */
  public static Message a(String s) {
    return new Atom(s);
  }

  public static Message pair(Message l, Message r) {
    return new Pair(l, r);
  }

  public static Message fn(String f, Message... args) {
    return new PredictiveFunction(f, List.of(args));
  }

  public static Message senc(Message m, Message k) {
    return fn("senc", m, k);
  }

  public static Message aenc(Message m, Message pub) {
    return fn("aenc", m, pub);
  }

  public static Message pk(Message sk) {
    return fn("pk", sk);
  }
}
