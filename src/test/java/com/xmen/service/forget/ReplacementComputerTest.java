package com.xmen.service.forget;

import com.xmen.model.Atom;
import com.xmen.model.Message;
import com.xmen.model.Pair;
import com.xmen.model.PredictiveFunction;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for ReplacementComputer ensuring Algorithm 1 compliance:
 * - Only blocked hypotheses should be replaced
 * - Function arguments should NOT be recursively modified
 */
@DisplayName("ReplacementComputer Algorithm 1 Tests")
public class ReplacementComputerTest {

    private ReplacementComputer replacementComputer;

    @BeforeEach
    void setup() {
        replacementComputer = new ReplacementComputer();
    }

    @Test
    @DisplayName("FIX 3: bal($oyster) should remain unchanged when only $oyster is replaced")
    void testFunctionNotModifiedWhenOnlyArgumentBlocked() {
        // Given: target is <$oyster, bal($oyster), ~gid>
        Message oyster = new Atom("$oyster");
        Message ccard = new Atom("$ccard");
        Message balOyster = new PredictiveFunction("bal", List.of(oyster));
        Message gid = new Atom("~gid");
        
        // Build target as nested pairs: Pair($oyster, Pair(bal($oyster), ~gid))
        Message target = new Pair(oyster, new Pair(balOyster, gid));
        
        // Given: substitution only has $oyster -> $ccard
        Map<Message, Message> substitution = new HashMap<>();
        substitution.put(oyster, ccard);
        
        // When: apply substitution
        Message variant = replacementComputer.applySubstitution(target, substitution);
        
        // Then: $oyster should be replaced but bal($oyster) should remain unchanged
        assertThat(variant).isInstanceOf(Pair.class);
        Pair variantPair = (Pair) variant;
        
        // First element should be $ccard (replaced)
        assertThat(variantPair.getLeft()).isInstanceOf(Atom.class);
        assertThat(((Atom) variantPair.getLeft()).getValue()).isEqualTo("$ccard");
        
        // Second element should be Pair(bal($oyster), ~gid)
        assertThat(variantPair.getRight()).isInstanceOf(Pair.class);
        Pair innerPair = (Pair) variantPair.getRight();
        
        // bal($oyster) should be UNCHANGED - NOT bal($ccard)
        assertThat(innerPair.getLeft()).isInstanceOf(PredictiveFunction.class);
        PredictiveFunction balFunc = (PredictiveFunction) innerPair.getLeft();
        assertThat(balFunc.getName()).isEqualTo("bal");
        assertThat(balFunc.getArgs()).hasSize(1);
        
        // THE KEY TEST: The argument of bal should still be $oyster, NOT $ccard
        Message balArg = balFunc.getArgs().get(0);
        assertThat(balArg).isInstanceOf(Atom.class);
        assertThat(((Atom) balArg).getValue()).isEqualTo("$oyster");
        
        // ~gid should be unchanged
        assertThat(innerPair.getRight()).isInstanceOf(Atom.class);
        assertThat(((Atom) innerPair.getRight()).getValue()).isEqualTo("~gid");
    }

    @Test
    @DisplayName("Function should be replaced when entire function is in substitution")
    void testFunctionReplacedWhenInSubstitution() {
        // Given: bal($oyster) is directly in substitution map
        Message oyster = new Atom("$oyster");
        Message ccard = new Atom("$ccard");
        Message balOyster = new PredictiveFunction("bal", List.of(oyster));
        Message balCcard = new PredictiveFunction("bal", List.of(ccard));
        Message gid = new Atom("~gid");
        
        Message target = new Pair(oyster, new Pair(balOyster, gid));
        
        // Substitution has both $oyster->$ccard AND bal($oyster)->bal($ccard)
        Map<Message, Message> substitution = new HashMap<>();
        substitution.put(oyster, ccard);
        substitution.put(balOyster, balCcard);
        
        // When: apply substitution
        Message variant = replacementComputer.applySubstitution(target, substitution);
        
        // Then: both should be replaced
        Pair variantPair = (Pair) variant;
        assertThat(((Atom) variantPair.getLeft()).getValue()).isEqualTo("$ccard");
        
        Pair innerPair = (Pair) variantPair.getRight();
        PredictiveFunction balFunc = (PredictiveFunction) innerPair.getLeft();
        assertThat(((Atom) balFunc.getArgs().get(0)).getValue()).isEqualTo("$ccard");
    }

    @Test
    @DisplayName("Variant generation with only $oyster blocked")
    void testGenerateVariantsOnlyOysterBlocked() {
        // Given: target <$oyster, bal($oyster), ~gid>
        Message oyster = new Atom("$oyster");
        Message ccard = new Atom("$ccard");
        Message balOyster = new PredictiveFunction("bal", List.of(oyster));
        Message gid = new Atom("~gid");
        
        Message target = new Pair(oyster, new Pair(balOyster, gid));
        
        // blockedToReplacements only has $oyster (bal($oyster) is NOT blocked in CASE1)
        Map<Message, Set<Message>> blockedToReplacements = new LinkedHashMap<>();
        blockedToReplacements.put(oyster, Set.of(ccard));
        
        // When: generate variants
        List<Message> variants = replacementComputer.generateVariants(target, blockedToReplacements);
        
        // Then: should have exactly one variant
        assertThat(variants).hasSize(1);
        
        // The variant should be <$ccard, bal($oyster), ~gid>
        Pair variant = (Pair) variants.get(0);
        assertThat(((Atom) variant.getLeft()).getValue()).isEqualTo("$ccard");
        
        Pair innerPair = (Pair) variant.getRight();
        PredictiveFunction balFunc = (PredictiveFunction) innerPair.getLeft();
        // bal's argument should still be $oyster!
        assertThat(((Atom) balFunc.getArgs().get(0)).getValue()).isEqualTo("$oyster");
    }

    @Test
    @DisplayName("Alg. 1 line 22: R = {m' in K | m' not in Forget, same format, same label}")
    void replacementSetFollowsLine22() {
        Message pw1 = new Atom("pw1");
        Message pw2 = new Atom("pw2");
        Message pw3 = new Atom("pw3");
        Message nonce = new Atom("n");
        Message pairedPw = new Pair(pw2, nonce);
        Map<String, String> labels = Map.of("pw1", "password", "pw2", "password", "pw3", "password", "n", "nonce");
        ForgetContext ctx = new ForgetContext(
            new LinkedHashSet<>(List.of(pw1, pw2, pw3, nonce, pairedPw)),
            new LinkedHashSet<>(List.of(pw1, pw3)), ForgetContext.BlockingMode.CASE1_WEAK, labels);
        // pw3 is forgotten, n has another label, <pw2,n> has another format.
        assertThat(replacementComputer.computeReplacementSet(pw1, ctx)).containsExactly(pw2);
    }

    @Test
    @DisplayName("Line 22 tests m' not in Forget, not closure membership (Case 3)")
    void replacementSetUsesForgetMembership() {
        Message pw1 = new Atom("pw1");
        Message pw2 = new Atom("pw2");
        Message k = new Atom("k");
        Message c = new PredictiveFunction("senc", List.of(pw2, k));
        Map<String, String> labels = Map.of("pw1", "password", "pw2", "password");
        // Forget ⊢ pw2 (decrypt c with k), but pw2 itself is not in Forget.
        ForgetContext ctx = new ForgetContext(
            new LinkedHashSet<>(List.of(pw1, pw2, k, c)),
            new LinkedHashSet<>(List.of(pw1, k, c)), ForgetContext.BlockingMode.CASE3_FULL_DY, labels);
        assertThat(replacementComputer.computeReplacementSet(pw1, ctx)).containsExactly(pw2);
    }

    @Test
    @DisplayName("An unlabelled hypothesis is only replaced by unlabelled candidates")
    void unlabelledHypothesisNeedsUnlabelledCandidate() {
        Message x = new Atom("x");
        Message y = new Atom("y");
        Message pw = new Atom("pw");
        ForgetContext ctx = new ForgetContext(
            new LinkedHashSet<>(List.of(x, y, pw)), new LinkedHashSet<>(List.of(x)),
            ForgetContext.BlockingMode.CASE1_WEAK, Map.of("pw", "password"));
        assertThat(replacementComputer.computeReplacementSet(x, ctx)).containsExactly(y);
    }
}

