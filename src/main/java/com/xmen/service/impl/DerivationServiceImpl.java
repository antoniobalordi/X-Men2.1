package com.xmen.service.impl;

import com.xmen.model.*;
import com.xmen.service.DerivationService;
import com.xmen.service.derivation.DerivationConfig;
import com.xmen.service.derivation.DerivationTreePrinter;
import com.xmen.service.derivation.NormalDerivationEnumerator;
import org.springframework.stereotype.Service;

import java.util.*;
import java.util.stream.Collectors;

/**
 * DerivationServiceImpl class implements the DerivationService interface. This service provides
 * methods to derive a target message from a set of knowledge messages and to print the derivation
 * tree.
 *
 * <p>All entry points share one derivation semantics: the normal Dolev-Yao derivations of the
 * paper (journal Sec. 3.2), enumerated by {@link NormalDerivationEnumerator}. Every rule
 * application records all of its premises, so the leaves of a tree are exactly its hypotheses.
 */
@Service
public class DerivationServiceImpl implements DerivationService {

  /** Configuration for derivation (function symbols, limits) */
  private DerivationConfig config = new DerivationConfig();

  /** Printer for clean derivation tree output */
  private DerivationTreePrinter printer = new DerivationTreePrinter(config);

  /**
   * Sets the derivation configuration (for controlling projections).
   * @param config The configuration to use
   */
  public void setConfig(DerivationConfig config) {
    this.config = config != null ? config : new DerivationConfig();
    this.printer = new DerivationTreePrinter(this.config);
  }

  /**
   * Gets the current derivation configuration.
   */
  public DerivationConfig getConfig() {
    return this.config;
  }

  /**
   * Derives a target message from a set of knowledge messages up to a specified depth limit
   * according to the Dolev-Yao Model.
   *
   * @param target the target message to derive
   * @param knowledge the set of knowledge messages
   * @param depthLimit the maximum depth for derivation
   * @return one textual description per derivation found (empty if the target is not derivable)
   */
  @Override
  public Set<String> deriveLimited(Message target, Set<Message> knowledge, int depthLimit) {
    Set<String> results = new LinkedHashSet<>();
    for (Derivation d : enumerate(target, knowledge, depthLimit).derivations()) {
      results.add(describe(d));
    }
    return results;
  }

  @Override
  public Set<Derivation> deriveToDepth(
      Message target, Set<Message> knowledge, int depthLimit) {
    Set<Derivation> derivations = deriveToDepthNoPrint(target, knowledge, depthLimit);
    // Use the printer with full context; it now handles the zero-derivation case too
    printer.printAllTrees(derivations, target, knowledge);
    return derivations;
  }

  /**
   * Same as {@link #deriveToDepth} but does NOT print the derivation tree.
   * Use this when the caller only needs the set of derivations (e.g. for blocking
   * analysis) and another caller is responsible for visualisation.
   */
  public Set<Derivation> deriveToDepthNoPrint(
      Message target, Set<Message> knowledge, int depthLimit) {
    return enumerate(target, knowledge, depthLimit).derivations();
  }

  /**
   * Enumerates the normal derivations of {@code target}, reporting whether the configured depth
   * or count limits cut the enumeration.
   */
  public NormalDerivationEnumerator.Result enumerate(
      Message target, Set<Message> knowledge, int depthLimit) {
    return new NormalDerivationEnumerator(
            config.getPrivateFunctions(), config.getMaxDerivationsPerTarget())
        .enumerate(target, knowledge, depthLimit);
  }

  @Override
  public Set<Derivation> deriveToInfinity(Message target, Set<Message> knowledge) {
    // Normal derivations never repeat a term on a path, so the unbounded search is finite.
    Set<Derivation> derivations = deriveToDepthNoPrint(target, knowledge, Integer.MAX_VALUE);
    // Use the printer with full context; it now handles the zero-derivation case too
    printer.printAllTrees(derivations, target, knowledge);
    return derivations;
  }

  @Override
  public void printAllDerivationTrees(Set<Derivation> trees) {
    // When only the trees are known, delegate to printer without extra context.
    // DerivationTreePrinter will fall back to a compact view.
    if (trees == null || trees.isEmpty()) {
      printer.printZeroDerivationReport(null, Collections.emptySet());
      return;
    }
    int i = 1;
    for (Derivation t : trees) {
      printer.printTree(t, i++);
    }
  }

  /**
   * Prints the derivation tree for the target message using the given knowledge set and depth
   * limit. This method prints a visual tree in the console.
   *
   * @param target The target message.
   * @param knowledge The set of known messages.
   * @param depthLimit The recursion depth limit.
   */
  @Override
  public void printDerivationTree(Message target, Set<Message> knowledge, int depthLimit) {
    printer.printAllTrees(deriveToDepthNoPrint(target, knowledge, depthLimit), target, knowledge);
  }

  private static String describe(Derivation d) {
    if (d.getPremises().isEmpty()) {
      return d.getRule() + ": " + d.getGoal().represent();
    }
    return d.getRule()
        + ": ("
        + d.getPremises().stream().map(DerivationServiceImpl::describe).collect(Collectors.joining(", "))
        + ") yields "
        + d.getGoal().represent();
  }
}
