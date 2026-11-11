package com.xmen.service.forget;

import com.xmen.model.*;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * ReplacementComputer implements the replacement step of Algorithm 1 (journal version of
 * November 2026, lines 29-40):
 * - U: the atomic submessages of m2 that H cannot derive under forgetting, whatever the cause
 *   (never added to K, forgotten, or obtainable only with a forgotten rule) — see
 *   {@link #atomicSubmessages(Message)}
 * - Repl(m̄) (line 31): messages of K that are not blocked, with the same format and label as m̄
 * - each combination of replacements yields the variant m2[C] ({@link #substituteSubmessages});
 *   the caller keeps it only if it is derivable under forgetting (line 36)
 */
@Slf4j
@Component
public class ReplacementComputer {

    private static final int MAX_VARIANTS = 100; // Cap to prevent explosion

    /** Closure-aware blocking test of line 31; optional so that unit tests can use {@code new}. */
    @Autowired(required = false)
    private BlockingChecker blockingChecker;

    // ===== Spec rules of the November 2026 algorithm, kept in one place =====

    /**
     * The atomic submessages of {@code m} (Definition 2): submessages are reached through pairs and
     * through the plaintext (not the key) of symmetric and asymmetric encryption; a message is atomic
     * if it has no proper submessage. Tamarin's {@code sign(m, sk)} is read as the paper's signature
     * {m}_{K^-1}, an asymmetric encryption under the private key (Sec. "Algebra of messages"), so its
     * first argument is a submessage. Any other function application (hash, pk, user functions) is
     * atomic.
     */
    public static Set<Message> atomicSubmessages(Message m) {
        Set<Message> out = new LinkedHashSet<>();
        collectAtomicSubmessages(m, out);
        return out;
    }

    private static void collectAtomicSubmessages(Message m, Set<Message> out) {
        if (m == null) return;
        if (m instanceof Pair p) {
            collectAtomicSubmessages(p.getLeft(), out);
            collectAtomicSubmessages(p.getRight(), out);
            return;
        }
        Message body = submessageBody(m);
        if (body != null) {
            collectAtomicSubmessages(body, out);
            return;
        }
        out.add(m);
    }

    /** The argument of {@code m} whose submessages are submessages of {@code m}, if any. */
    private static Message submessageBody(Message m) {
        if (m instanceof Encrypt e) return e.getMsg();
        if (m instanceof PredictiveFunction f && f.getArgs().size() == 2) {
            String name = f.getName().toLowerCase(Locale.ROOT);
            if (name.equals("senc") || name.equals("aenc") || name.equals("sign")) {
                return f.getArgs().get(0);
            }
        }
        return null;
    }

    /**
     * {@code m[C]} of line 35: replaces every occurrence of a key of {@code substitution} at a
     * submessage position of {@code m} (pairs, encrypted or signed plaintexts). Keys and the
     * arguments of other functions are left unchanged.
     */
    public static Message substituteSubmessages(Message m, Map<Message, Message> substitution) {
        if (m == null) return null;
        if (substitution.containsKey(m)) return substitution.get(m);
        if (m instanceof Pair p) {
            Message l = substituteSubmessages(p.getLeft(), substitution);
            Message r = substituteSubmessages(p.getRight(), substitution);
            return (l == p.getLeft() && r == p.getRight()) ? m : new Pair(l, r);
        }
        if (m instanceof Encrypt e) {
            Message body = substituteSubmessages(e.getMsg(), substitution);
            return body == e.getMsg() ? m : new Encrypt(body, e.getKey());
        }
        if (m instanceof PredictiveFunction f && submessageBody(f) != null) {
            Message body = substituteSubmessages(f.getArgs().get(0), substitution);
            if (body == f.getArgs().get(0)) return m;
            List<Message> args = new ArrayList<>(f.getArgs());
            args.set(0, body);
            return new PredictiveFunction(f.getName(), args);
        }
        return m;
    }

    /** Line 31: Blocked({m̄'}, Forget) = ∅, under the configured closure case. */
    private boolean isBlocked(Message candidate, ForgetContext ctx) {
        if (blockingChecker != null) return blockingChecker.isBlocked(candidate, ctx);
        return ctx.getForgetSet().contains(candidate); // closure case (i)
    }

    /**
     * Computes the replacement set R_m̄ for a blocked hypothesis.
     * Per Algorithm 1, line 22:
     * - Candidate is in K' and not in Forget'
     * - Candidate must have matching format
     * - Candidate must have the same label as the blocked hypothesis (an unlabelled hypothesis
     *   can only be replaced by an unlabelled candidate)
     *
     * @param blocked the blocked hypothesis to replace
     * @param ctx the updated context (K' and Forget')
     * @return set of valid replacement candidates
     */
    public Set<Message> computeReplacementSet(Message blocked, ForgetContext ctx) {
        Set<Message> replacements = new LinkedHashSet<>();

        if (blocked == null || ctx == null) {
            return replacements;
        }

        String blockedType = ctx.getTypeOf(blocked);
        TermFormat blockedFormat = TermFormat.formatOf(blocked);

        log.debug("Computing replacements for blocked hypothesis: {} (type={}, format={})",
                  blocked.represent(), blockedType, blockedFormat);

        // Search through knowledge K' for candidates
        for (Message candidate : ctx.getKnowledge()) {
            // Skip if candidate equals blocked
            if (candidate.equals(blocked)) {
                continue;
            }

            // Algorithm 1, line 31: Blocked({m̄'}, Forget^{i+1}) = ∅ (under Cases 2/3 a candidate
            // derivable from Forget is blocked too)
            if (isBlocked(candidate, ctx)) {
                log.debug("  Candidate {} is forgotten, skipping", candidate.represent());
                continue;
            }

            // Check format constraint: format(candidate) == format(blocked)
            if (!TermFormat.formatsCompatible(candidate, blocked)) {
                log.debug("  Candidate {} format mismatch, skipping", candidate.represent());
                continue;
            }

            // Check label/type constraint: same label as the blocked hypothesis (line 22)
            String candidateType = ctx.getTypeOf(candidate);
            if (!Objects.equals(blockedType, candidateType)) {
                log.debug("  Candidate {} type mismatch ({} vs {}), skipping",
                         candidate.represent(), candidateType, blockedType);
                continue;
            }

            log.debug("  Candidate {} accepted as replacement", candidate.represent());
            replacements.add(candidate);
        }

        return replacements;
    }

    /**
     * Generates all variant messages by replacing blocked hypotheses.
     * For each combination of replacements, creates a new message with substitutions.
     *
     * @param originalMsg the original message to mutate
     * @param blockedToReplacements map from blocked hypothesis to its replacement set
     * @return list of variant messages (may be empty if no valid variants exist)
     */
    public List<Message> generateVariants(Message originalMsg,
                                          Map<Message, Set<Message>> blockedToReplacements) {
        List<Message> variants = new ArrayList<>();

        if (originalMsg == null || blockedToReplacements == null || blockedToReplacements.isEmpty()) {
            return variants;
        }

        // Check if any replacement set is empty (no variants possible)
        for (Map.Entry<Message, Set<Message>> entry : blockedToReplacements.entrySet()) {
            if (entry.getValue().isEmpty()) {
                log.info("Empty replacement set for blocked hypothesis {}, no variants possible",
                        entry.getKey().represent());
                return variants; // Return empty list
            }
        }

        // Generate cartesian product of all replacement choices
        List<Message> blockedList = new ArrayList<>(blockedToReplacements.keySet());
        List<Set<Message>> replacementSets = new ArrayList<>();
        for (Message blocked : blockedList) {
            replacementSets.add(blockedToReplacements.get(blocked));
        }

        // Generate all combinations
        List<List<Message>> combinations = cartesianProduct(replacementSets);

        // For each combination, create a variant by substitution
        int variantCount = 0;
        for (List<Message> combination : combinations) {
            if (variantCount >= MAX_VARIANTS) {
                log.warn("Reached maximum variant limit ({}), truncating", MAX_VARIANTS);
                break;
            }

            // Build substitution map
            Map<Message, Message> substitution = new HashMap<>();
            for (int i = 0; i < blockedList.size(); i++) {
                substitution.put(blockedList.get(i), combination.get(i));
            }

            // Apply substitution to create variant
            Message variant = applySubstitution(originalMsg, substitution);
            if (variant != null) {
                variants.add(variant);
                variantCount++;
            }
        }

        log.info("Generated {} variants for message {}", variants.size(), originalMsg.represent());
        return variants;
    }

    /**
     * Applies a substitution map to a message, replacing occurrences structurally.
     *
     * FIX 3 (Paper Algorithm 1): Substitutions should only replace BLOCKED HYPOTHESES,
     * not every occurrence of a blocked term inside other messages.
     *
     * For example, if $oyster is blocked and we have bal($oyster):
     * - If bal($oyster) is NOT blocked, it should remain UNCHANGED
     * - We should NOT recursively replace $oyster inside bal()
     *
     * This means: only replace at the TOP level where the entire message matches
     * a key in the substitution map. Do NOT recurse into function arguments
     * unless the function itself is being replaced.
     */
    public Message applySubstitution(Message msg, Map<Message, Message> substitution) {
        if (msg == null) return null;

        // Check if entire message is being substituted (this is the PRIMARY case)
        if (substitution.containsKey(msg)) {
            return substitution.get(msg);
        }

        // For Pairs: the pair itself is not in substitution, so recurse into components
        // This is correct because pairs are just structural containers, not semantic units
        if (msg instanceof Pair p) {
            Message newLeft = applySubstitution(p.getLeft(), substitution);
            Message newRight = applySubstitution(p.getRight(), substitution);
            // Only create new pair if something changed
            if (newLeft != p.getLeft() || newRight != p.getRight()) {
                return new Pair(newLeft, newRight);
            }
            return msg;
        }

        // For Encryptions: similar to pairs, encryption is structural
        if (msg instanceof Encrypt e) {
            Message newMsg = applySubstitution(e.getMsg(), substitution);
            Message newKey = applySubstitution(e.getKey(), substitution);
            if (newMsg != e.getMsg() || newKey != e.getKey()) {
                return new Encrypt(newMsg, newKey);
            }
            return msg;
        }

        // FIX 3: For Functions like bal($oyster), do NOT recurse into arguments!
        // If bal($oyster) itself is not in the substitution map, leave it unchanged.
        // This is the key difference from the previous (wrong) behavior.
        if (msg instanceof PredictiveFunction) {
            // The function is NOT in the substitution map, so return as-is
            // Do NOT modify the function's arguments
            return msg;
        }

        // Atom or unknown - return as-is (no recursive modification possible)
        return msg;
    }

    /**
     * Computes cartesian product of multiple sets.
     */
    private List<List<Message>> cartesianProduct(List<Set<Message>> sets) {
        List<List<Message>> result = new ArrayList<>();
        if (sets.isEmpty()) {
            result.add(new ArrayList<>());
            return result;
        }

        result.add(new ArrayList<>());

        for (Set<Message> set : sets) {
            List<List<Message>> newResult = new ArrayList<>();
            for (List<Message> existing : result) {
                for (Message element : set) {
                    if (newResult.size() >= MAX_VARIANTS) {
                        return newResult;
                    }
                    List<Message> newList = new ArrayList<>(existing);
                    newList.add(element);
                    newResult.add(newList);
                }
            }
            result = newResult;
        }

        return result;
    }

    /**
     * Converts a Message to its string representation for use in rule rewriting.
     */
    public String messageToString(Message msg) {
        if (msg == null) return "";

        if (msg instanceof Atom a) {
            return a.getValue();
        } else if (msg instanceof Pair p) {
            return "<" + messageToString(p.getLeft()) + "," + messageToString(p.getRight()) + ">";
        } else if (msg instanceof Encrypt e) {
            return "senc(" + messageToString(e.getMsg()) + "," + messageToString(e.getKey()) + ")";
        } else if (msg instanceof PredictiveFunction f) {
            StringBuilder sb = new StringBuilder(f.getName());
            sb.append("(");
            for (int i = 0; i < f.getArgs().size(); i++) {
                if (i > 0) sb.append(",");
                sb.append(messageToString(f.getArgs().get(i)));
            }
            sb.append(")");
            return sb.toString();
        }

        return msg.represent();
    }
}

