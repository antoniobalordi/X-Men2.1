package com.xmen.service.derivation;

import com.xmen.model.Atom;
import com.xmen.model.Encrypt;
import com.xmen.model.Message;
import com.xmen.model.Pair;
import com.xmen.model.PredictiveFunction;

import java.util.ArrayList;
import java.util.List;

/**
 * Prints a {@link Message} in Tamarin syntax. Right-nested pairs are printed as one tuple
 * ({@code Pair(a, Pair(b, c))} → {@code <a,b,c>}), which is the inverse of how payloads are parsed.
 */
public final class TamarinTermPrinter {

  private TamarinTermPrinter() {}

  public static String print(Message m) {
    if (m == null) return "";
    if (m instanceof Atom a) return a.getValue();
    if (m instanceof Pair) {
      List<String> parts = new ArrayList<>();
      Message cur = m;
      while (cur instanceof Pair p) {
        parts.add(print(p.getLeft()));
        cur = p.getRight();
      }
      parts.add(print(cur));
      return "<" + String.join(",", parts) + ">";
    }
    if (m instanceof Encrypt e) return "senc(" + print(e.getMsg()) + "," + print(e.getKey()) + ")";
    if (m instanceof PredictiveFunction f) {
      List<String> args = new ArrayList<>();
      for (Message a : f.getArgs()) args.add(print(a));
      return f.getName() + "(" + String.join(",", args) + ")";
    }
    return m.represent();
  }
}
