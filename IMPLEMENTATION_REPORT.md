# Implementation Report — Procedural Forgetting and Derivation Audit

Companion to [`IMPLEMENTATION_PLAN.md`](IMPLEMENTATION_PLAN.md) (plan, formal
requirements, ambiguities and the interpretations adopted).

Specification sources: the conference paper (*Formal Modeling and Analysis of
Human Memory Lapses in Security Ceremonies*) and the journal manuscript (*Human
Memory Lapses in Security Ceremonies: Formal Modelling and Analysis*). As
instructed, the journal's Defeasible Logic part (§7, §8, Algorithm 2) was
ignored. "Algorithm 1" below always means the journal's 53-line version.

---

## 1. Implementation summary

**Procedural forgetting.** A human transition can now declare that the human
forgets a Dolev-Yao inference rule:

```
--[ H(), ForgetRule('r_sdec'), … ]->
```

This implements Definition 4 case (3), Definition 5 and Algorithm 1
lines 40–53. The forgotten rule set `R̄_H` persists across the human's later
transitions. A derivation that applies a forgotten rule is unusable whatever its
hypotheses are. The send is preserved if some derivation survives and is skipped
otherwise. A forgotten rule never triggers REPLACE, and internal checks that can
no longer be performed are neglected. `Forget(x)` and `ForgetRule(r)` can be
mixed in one file and in one rule.

The workflow is unchanged: the same `.spthy` upload, the same UI checkbox and
endpoints (`/api/forget/mutations`, `/api/generateMutations` with
`Forget-Mutation: true`), and the same zip of `<file>_M<i>.m` models plus
`<file>_DerivationTree.txt`. Unknown or malformed rule names are rejected with
HTTP 400 and the list of rules the theory supports. The only new syntax is the
annotation.

**Derivation engine (rewritten core, same public API).** The audit found that
the enumeration of derivations was neither sound nor complete for the
specifications the tool actually receives (§4). The derivation computation is
now:

* `NormalDerivationEnumerator`: complete enumeration of normal derivations. Every
  rule application lists all its premises, and truncation by limits is reported
  instead of silent.
* `DolevYaoDeducer`: an exact decision procedure (analysis closure plus
  synthesis). It decides "is there a usable derivation?" (Definitions 5 and 7),
  the Case 2/3 closures of Definition 6, and the Neglect test, independently of
  any depth or count limit.

**Atomic forgetting corrections.** These are spec-conformance fixes found during
the audit:

* knowledge of a transition (`K^{i+1} = K^i ∪ {m1} ∪ fresh`);
* the `Forget` set when the received message is forgotten (Algorithm 1 line 5);
* one REPLACE mutant per admissible replacement combination;
* SKIP removing Out-style sends;
* NEGLECT when forgetting a key makes a check impossible;
* the literal replacement filter of line 22.

The paper's Bank Login case study still yields its published result
(REPLACE `pw1 → pw2`, including `PasswordAttempt(…,pw2,…)`). It is now obtained
from actual derivations instead of a textual fallback that bypassed Algorithm 1.

### Architectural changes

| Component | Change |
|---|---|
| `model/InferenceRule` *(new)* | Rule names `r_pair, r_unpair, r_senc, r_sdec, r_aenc, r_adec` (the paper's `R`) and `r_f` for every other public function symbol; parsing of user-written names |
| `model/Derivation` | Each node carries the `InferenceRule` it applies (inferred from the legacy label if not given) |
| `service/derivation/DolevYaoTerms` *(new)* | Which terms can be composed / decomposed and with which rule |
| `service/derivation/DolevYaoDeducer` *(new)* | Exact derivability with an allowed-rule predicate |
| `service/derivation/NormalDerivationEnumerator` *(new)* | Enumeration of `Π_m`, truncation flag |
| `service/derivation/DerivationRules` *(new)* | `Rules(π)` (Def. 5); replay of `π` under a leaf substitution (variant of Alg. 1 l.28) |
| `service/derivation/TamarinTermPrinter` *(new)* | Message → Tamarin text (rewriting, reports) |
| `DerivationServiceImpl` | All entry points delegate to the enumerator (one derivation semantics) |
| `BlockingChecker` | Cases 2/3 via the deducer; `forgottenRulesUsed`, `isUsable` |
| `ForgetContext` | `R̄_H` (`forgottenRules`), public names/constants, Alg. 1 l.5 fix |
| `ForgetDerivationChecker` | Exact `derivableUnderForgetting` honouring `R̄`; enumeration with truncation flag |
| `ReplacementComputer` | Literal line 22 (`m̄' ∉ Forget`, same label) |
| `ForgetMutationStrategy` | Unified Algorithm 1 (messages and rules), per-transition `K`, causal NEGLECT, replay-based variants, per-variant rewriting and propagation, structural SKIP matching, analysis report |
| `ForgetMutationParser`, `ParametersBundle` | `ForgetRule(...)` collection and validation against the theory (`functions:`, `builtins:`), `[private]` functions |
| `CeremonyVocabulary`, `vocabulary.yaml` | `forget-rule: ForgetRule`, added to the core (non-internal) actions |
| `DerivationTreePrinter`, `AlgorithmInfoDialog`, `README.md`, `chatbot/knowledge/forget-paper.yaml` | Rule identifiers in the report; documentation (README, in-app explanation, in-app assistant entry for procedural forgetting) |

---

## 2. Formal-to-code mapping (journal, non-DL part)

| Paper | Meaning | Implementation |
|---|---|---|
| Def. 1 (algebra), other operators "handled in the standard way" | Terms; public function symbols are applicable by agents | `Message` classes; `DolevYaoTerms.compositionRule` (`[private]` excluded via `ForgetMutationParser.privateFunctions`) |
| Def. 3 (`format`) | Top-level symbol | `TermFormat.formatsCompatible` (atoms share one format, see Plan B.1 item 7) |
| §3.2 rules `R` | `r_pair`, `r_unpair` (both projections), `r_senc/sdec`, `r_aenc/adec` | `InferenceRule.PAPER_RULES`; decomposition in `DolevYaoTerms.asCipher` (`sdec` with the same key, `adec` of `aenc(m,pk(sk))` with `sk`) |
| §3.2 derivation, hypotheses | Tree; leaves from `K` | `Derivation` (`Initial` leaves); `BlockingChecker.extractHypotheses` |
| §3.2 normal derivations, finite search | No inverse detours | `NormalDerivationEnumerator` (no term twice on a path, Plan B.1 item 1) |
| Def. 4 (1)(2) | Forget received / known message | `ForgetContext.updateForTransition`, `ForgetMutationStrategy.applyMutation` (state update block) |
| **Def. 4 (3)** | Forget an inference rule | `ForgetRule(r)` → `ParametersBundle.forgetRuleSet` → `ForgetContext.forgetRule` |
| **Def. 5** `Rules(π)`, `R̄_H` | Rules applied in `π`; forgotten rules block every `π` using them | `DerivationRules.rulesOf`; `BlockingChecker.forgottenRulesUsed`; `DolevYaoDeducer.excluding(R̄)` |
| Def. 6 (Blocked, Cases 1–3) | Blocked hypotheses | `BlockingChecker.isBlocked` (Case 1 membership; Cases 2/3 `DolevYaoDeducer` with `PAIRING_RULES` / `ALL_RULES` over `Forget`) |
| Def. 7 | Some derivation without blocked hypotheses | `ForgetDerivationChecker.derivableUnderForgetting` (exact; also requires no forgotten rule) |
| Alg. 1 l.1 | Transition `i` | `MutationGeneratorServiceImpl` → `ForgetMutationStrategy.applyMutation(rule,…)`, per human rule, context persisted |
| Alg. 1 l.3–6 | `m = m1`: `K`, `Forget`, `R̄` unchanged | `updateForTransition(m1, m1)` |
| Alg. 1 l.7–10 | `K ∪ {m1}`, `Forget ∪ {m}` | `updateForTransition(m1, null)` + `addForget(m)`; fresh values `freshValues` (§3.4) |
| Alg. 1 l.12–14 | `m` used in `a` ⇒ NEGLECT, then continue | `isMessageUsedInInternalAction` (textual) ∪ `actionsMadeImpossible` (causal) |
| Alg. 1 l.15–17 | Preserve if an unblocked derivation exists | `derivableUnderForgetting` → "send preserved" branch |
| Alg. 1 l.19–35 | Replacement sets, combinations, REPLACE per variant | `computeVariants` (`ReplacementComputer.computeReplacementSet`, `DerivationRules.replay`), `applyVariantToRule`, `propagateMutationWithVariant` |
| Alg. 1 l.36–38 | No variant ⇒ SKIP + matching receive | `removeSendAndMatchingReceive` |
| **Alg. 1 l.40–43** | Rule lapse: `K ∪ {m1}`, `Forget` unchanged, `R̄ ∪ {r}` | state update block (`ctx.forgetRule`) |
| **Alg. 1 l.44–46** | `r` used in `a` ⇒ NEGLECT | `actionsMadeImpossible` (argument derivable before the lapse, not after) |
| **Alg. 1 l.47–49** | `Π` restricted to `Rules(π) ∩ R̄ = ∅`; preserve if an unblocked one exists | `derivableUnderForgetting` (deducer with forbidden rules) |
| **Alg. 1 l.50–52** | Otherwise SKIP; no REPLACE for rules | SKIP branch; `computeVariants` skips derivations with `forgottenRulesUsed ≠ ∅` and is not called for rule-only lapses |
| §4.3 matching / propagation / re-acquisition | Receiver matching; re-received message leaves `Forget` | existing matching code (now structural for Out payloads); `updateForTransition` |

Not implemented, by instruction: forgetting a procedure as a whole (`Π̄_H`,
Definition 8, Algorithm 2), cues and reinstaters. All of these are part of the
Defeasible Logic section.

---

## 3. Derivation correctness audit

### 3.1 Reconstructed semantics

* **Valid derivation:** a finite tree whose leaves are elements of `K` (public
  names and constants are also available) and whose internal nodes apply one
  rule of `R` (or `r_f`) to the conclusions of their children, with *all*
  premises present (decryption: ciphertext and key; `adec` uses the private key
  `sk` of `pk(sk)`).
* **Normal derivation:** no term occurs twice on a root-to-leaf path. This
  subsumes the paper's "no immediate inverse" and makes `Π_m` finite. It does
  not change any existence question (Plan B.1 item 1).
* **Distinct derivations:** different trees (rule, premise structure or
  leaves). A hypothesis used on two branches is a shared dependency, not a
  merge. Projections on the left and on the right are distinct trees of the same
  rule `r_unpair`.
* **What must be computed:** all of `Π_m`, because REPLACE iterates over every
  derivation (l.20). For the preserve/skip decision only existence matters, and
  existence is decided exactly.

### 3.2 Method

1. **Independent oracle** (`test/.../reference/ReferenceDerivationOracle`). It
   generates trees forward and bottom-up to a fixpoint over `St(K ∪ {t})`, with
   no code shared with the production backward search, and compares them through
   a canonical tree string.
2. **Three-way differential testing** on seeded random instances (pairs, `senc`,
   `aenc`/`pk`, `h`, nesting depth 2):
   * enumerator vs. oracle: identical sets of trees, **300 / 300 instances**;
   * Definition 7 (Cases 1–3) vs. oracle-computed blocking: **600 checks,
     0 mismatches**;
   * Definitions 5 + 7 with random forgotten rules: **600 checks, 0 mismatches**;
     the forgotten rules changed the outcome in **55** of them, so the test is not
     vacuous.
3. **Hand-derived examples:** journal Examples 1–6 (`PaperExamplesTest`). For
   procedural forgetting, an example with 4 derivations, shared key `m2`, and
   alternative rule sets (`ProceduralDerivationTest`).
4. **Before/after comparison:** every new test was first run against the
   unmodified code (results in
   [`docs/audit/before_fix_audit_results.txt`](docs/audit/before_fix_audit_results.txt));
   the end-to-end regressions were re-run on a clean checkout of the original
   commit.

### 3.3 Findings on the original implementation

| Question asked in the task | Finding |
|---|---|
| Omits valid derivation paths? | **Yes** — no decryption of Tamarin `senc`/`aenc` (D2), no nested/derived decomposition sources (D3), no composition of user functions (D4), silent caps (D6). Random test: many instances with fewer derivations than the oracle. |
| Incorrectly merges distinct derivations? | Not in the enumeration; but distinct REPLACE combinations collapsed into one mutant (S2). |
| Generates duplicate or invalid derivations? | **Yes** — non-normal `pair(fst(P),snd(P))` re-derivations (D8); decryption nodes missing the ciphertext premise, i.e. invalid trees with wrong `Hyp_π` (D1). |
| Mishandles multiple rules producing the same conclusion? | Only one decomposition source per kind was considered for `deriveLimited`; the forget path missed decryption entirely (D2). |
| Mishandles shared dependencies? | No defect found once D1–D4 were fixed (shared-dependency tests pass). |
| Incorrectly terminates recursion? | Depth 10 / 50 derivations / per-node caps truncated silently, and the truncated set was used for the existence decision (D6). |
| Cycles / repeated intermediates? | Goal repetition was checked except through projection leaves (D8). |
| Pruning that discards valid results? | The "never decompose user-defined functions" optimisation also forbade *composing* them (D4). |
| Affects atomic forgetting? | **Yes.** On the paper's Bank Login rule, `m2` had **zero** derivations, so the published REPLACE came from a textual fallback outside Algorithm 1. |
| Affects procedural forgetting? | All of D1–D8 would make `Rules(π)` wrong or empty; D7 (post-State as hypotheses) would make procedural forgetting vacuous whenever the lapse is in the first human rule. |

---

## 4. Discovered bugs and fixes

Each entry gives the cause, a minimal counterexample (all confirmed on the
original code), the violated requirement, the fix and the regression test.

**D1 — decryption premises incomplete.**
* *Cause:* the `Decryption` node listed only the key derivation.
* *Counterexample:* `K = { {m1}_m2, m2 }`, `Forget = { {m1}_m2 }`. The original
  code gave `Hyp = [m2]`, so `m1` was "derivable under forgetting". The paper
  (Def. 6/7) says it is blocked.
* *Fix:* the ciphertext is the first premise.
* *Tests:* `DerivationEnumerationOracleTest.legacyEncryptPremises`,
  `PaperExamplesTest.forgottenCiphertextBlocksDecryption`.

**D2 — Tamarin encryptions never decrypted.**
* *Cause:* decryption matched only the legacy `Encrypt` class; real input
  parses to `senc(…)`/`aenc(…)` functions.
* *Counterexample:* `K = { senc(m,k), k }` had 0 derivations of `m`;
  `K = { aenc(m,pk(sk)), sk }` likewise.
* *Fix:* `DolevYaoTerms.asCipher`.
* *Tests:* `symmetricDecryptionOfTamarinTerm`, `asymmetricDecryption`,
  `PaperExamplesTest.example1/4`.

**D3 — decomposition only from terms literally in `K`.**
* *Counterexample:* `c` from `<a,<b,c>>`, `x` from `senc(<x,y>,k)`, and `x` from
  `<senc(x,k),k>` were all underivable.
* *Fix:* sources are all of `St(K)`, derived recursively.
* *Tests:* `nestedProjection`, `decompositionChains`.

**D4 — public user functions not composable.**
* *Counterexample:* `k(nH,nB)` from `{nH, nB}` had 0 derivations, so the Bank
  `m2` was underivable.
* *Fix:* composition for every non-`[private]` symbol.
* *Tests:* `userFunctionComposition`, `bankLoginCredentialMessage`,
  `ProceduralDerivationTest.privateFunctions`.

**D5 — Case 3 closure incomplete (same gaps as D2/D3).**
* *Counterexample (Example 5):* `Forget = { senc(m1,m2), m2 }` did not block
  `m1`.
* *Fix:* `DolevYaoDeducer` over `Forget`.
* *Tests:* `PaperExamplesTest.example5`,
  `ForgetDerivabilityOracleTest.randomised`.

**D6 — silent truncation used for decisions.**
* *Cause:* depth 10, 50 derivations and per-node caps cut `Π`, and "no unblocked
  derivation among the truncated set" triggered REPLACE/SKIP.
* *Fix:* the decision is exact (deducer); enumeration reports `truncated`, and
  the report and logs say so.
* *Tests:* `ProceduralDerivationTest.truncationIsReported`, the differential
  tests.

**D7 — knowledge of a transition.**
* *Cause:* `K` was built once from the first human rule's pre-State,
  **post-State** and 4-ary inbound payloads; later rules added only received
  messages. Fresh values, persistent premises (`!Pk`, `!Ltk`) and the agent's own
  name were never added.
* *Counterexamples:*
  1. Fresh: `User_2` generates `~r` and sends `senc(~r,k)` while forgetting an
     unrelated `n`. The original code found 0 derivations and applied the
     textual fallback, mutating a send that should be preserved.
  2. Post-State: in the first human rule, forgetting the key `k` of a received
     `senc(<x,y>,k)` had no effect, because `x` was taken directly from the
     post-State. Verified on the original code: the tree was `h(x) ← x (K)`.
* *Fix:* `K^i` is the accumulated `K` ∪ pre-State ∪ persistent-premise values ∪
  own name; `K^{i+1} = K^i ∪ {m1} ∪ Fr(Pre_i)` (Plan B.1 item 9).
* *Tests:* `ProceduralForgettingE2ETest.freshValuesAreKnowledge`,
  `forgottenKeyNeglectsCheck`, `atomicBankUsesDerivations`.

**D8 — non-normal derivations.**
* *Cause:* projection premises were bare leaves that bypassed the cycle check.
* *Counterexample:* `K = {<a,b>}` gave 3 derivations of `<a,b>` (oracle: 1).
* *Fix:* projection sources are derived recursively under the path condition.
* *Tests:* `ProceduralDerivationTest.cyclesExcluded`, randomised differential
  test.

**S1 — `Forget` emptied when the received message is forgotten.**
* *Counterexample:* `x ∈ Forget`; transition receives `x` and forgets it again.
  `x` was removed from `Forget`, contradicting Algorithm 1 line 5 in both papers.
* *Fix:* `Forget` unchanged.
* *Tests:* `PaperExamplesTest.forgetJustReceivedKeepsForgetSet`. The existing
  `ForgetContextTransitionTest.updateForTransitionSameMessage` encoded the old
  behaviour; its expectation was corrected to the paper.

**S2 — REPLACE variants collapsed.**
* *Cause:* substitution did not enter function arguments, so every "variant"
  equalled `m2`, and each mutant then used the first replacement.
* *Counterexample:* Bank with `pw2` and `pw3` (`Forget_Bank_ThreePasswords.spthy`)
  produced 1 mutant (`pw2` only).
* *Fix:* variants by replaying `π` under each combination; per-variant
  rewriting and propagation; textual rewrite checked against the variant.
* *Test:* `ForgetReplacementVariantsTest.twoDistinctReplacements` (2 distinct
  mutants).

**S3 — SKIP never removed `Out(...)` sends with structured payloads.**
* *Cause:* the Tamarin text was compared with the internal rendering
  `senc(($Human, pw1), …)`.
* *Counterexample:* any SKIP on the Bank `H_2`. The rule kept its `Out` and
  `Send`. This was latent in the original, which never reached SKIP for Bank.
* *Fix:* structural comparison (`sameMessage`).
* *Tests:* `bankForgetAdecSkipsSend`, `bankForgetOtherNeededRulesSkip`.

**S4 — NEGLECT for messages only textual.**
* *Counterexample:* `Forget(k)` where the check `CheckSecret(x)` needs `x`
  obtained by decrypting with `k`. The original kept the check. §4.3's motivating
  example ("forgets the key needed to decrypt … before checking its contents")
  requires NEGLECT.
* *Fix:* causal criterion for both lapse kinds (Plan B.1 item 3).
* *Test:* `forgottenKeyNeglectsCheck`.

**Replacement filter (line 22).**
* *Change:* `m̄' ∉ Forget` (instead of "not blocked") and literal label equality.
* *Tests:* `ReplacementComputerTest.replacementSetFollowsLine22`,
  `replacementSetUsesForgetMembership`, `unlabelledHypothesisNeedsUnlabelledCandidate`.

**Behaviour preserved on purpose.**
* The textual-substitution fallback is kept only when `m2` is not derivable from
  `K` even without forgetting (Algorithm 1's precondition fails). It is printed
  as "legacy textual fallback, outside Algorithm 1".
* Witness actions referenced only by lemmas (e.g. `PasswordAttempt`) are
  rewritten on REPLACE rather than neglected (Plan B.1 item 12). This reproduces
  the paper's Bank model.

---

## 5. Test results

### Executed

| Suite | Result |
|---|---|
| Full Maven suite (`xvfb-run -a mvn test`, Java 21, incl. JavaFX UI tests under Xvfb) | **169 tests, 0 failures, 0 errors, 2 skipped** (§5.1) |
| Baseline before any change (same command) | 117 tests, 0 failures, 2 skipped (`LexerDebugTest`, `ParserDebugTest` are `@Disabled`) |
| New audit tests on the **original** code | all failing as expected — see `docs/audit/before_fix_audit_results.txt` (e.g. Example 4: 1 derivation instead of 2; Example 5 Case 3: derivable instead of blocked; random differential: mismatches in both directions) |
| New end-to-end regressions on a clean checkout of the original commit | `atomicBankUsesDerivations` (log: *"No derivations found for target senc(($Human, pw1), k(nH, nB)) - falling back to textual substitution"*), `freshValuesAreKnowledge`, `forgottenKeyNeglectsCheck`, `twoDistinctReplacements` fail; all procedural tests fail (feature absent) |
| Tamarin 1.10.0 (Maude 3.2 from Ubuntu) well-formedness of the 2 inputs and 22 generated mutants (Bank: atomic, 6 procedural lapses, combined; Procedural fixture: 14 mutants) | all load and translate; 3 mutants report one warning: restriction `CheckSecret` references an action no rule has — the intended effect of NEGLECT removing the only `CheckSecret` (the restriction becomes vacuous) |
| Tamarin proof of SG1 on the Bank models | see §5.2 |

New test classes: `DerivationEnumerationOracleTest` (11),
`ForgetDerivabilityOracleTest` (2), `PaperExamplesTest` (8),
`ProceduralDerivationTest` (8), `InferenceRuleAndParserTest` (4),
`ProceduralForgettingE2ETest` (15), `ForgetReplacementVariantsTest` (1),
3 added cases in `ReplacementComputerTest`. Fixtures: `Forget_Procedural.spthy`,
`Forget_FreshKnowledge.spthy`, `Forget_Bank_ThreePasswords.spthy`.

Reproduce: `xvfb-run -a ./mvnw test` (or `mvn test` without the UI tests if no
display: `-Dtest='!XMenInterfaceTest,!ChatBotDialogUiTest,!DisplayScaleSupportTest,!UiAdaptationTest'`).

### 5.1 Final run

`xvfb-run -a mvn -B test` on the final code: **169 tests run, 0 failures,
0 errors, 2 skipped** (the same two `@Disabled` debug tests as in the baseline).
All 117 pre-existing tests still pass; one pre-existing expectation was corrected
to the paper (S1, `ForgetContextTransitionTest.updateForTransitionSameMessage`).
Oracle statistics printed by the run:

```
[oracle] enumeration: 300 instances checked, 0 skipped as too large
[oracle] Def. 7: 600 checks, 0 mismatches
[oracle] Def. 5+7: 600 checks, 0 mismatches, forgotten rules changed the outcome in 55
```

Full per-class counts: [`docs/audit/after_fix_test_results.txt`](docs/audit/after_fix_test_results.txt).

### 5.2 Tamarin

(filled in below)

### Not executed / coverage gaps

* **Haskell derivation service:** not available here. It does not influence
  Forget decisions in the code (only the unused `isDerivable`). Unchanged and
  untested.
* **Tamarin `--prove` on all lemmas** of all mutants: not attempted beyond §5.2
  (time).
* Randomised tests use a small signature (pairs, `senc`, `aenc`/`pk`, `h`) and
  nesting depth 2; larger terms are covered only by the hand-written cases.
* Receiver matching for SKIP in In/Out-style models relies on the existing
  textual payload matching (it removed `In(h(x))` in the fixture). Matching
  against pattern variables, e.g. `In(senc(<$Human,pw>,…))`, is unchanged and
  not specified by the paper for public channels.

---

## 6. Limitations and open questions

1. **Normal derivations.** The "no term twice on a path" definition is our
   reading. The literal "no immediate inverse" reading admits infinitely many
   derivations and contradicts the paper's finiteness claim. The choice does not
   affect any preserve/skip decision, but it does determine `Π`, and therefore
   the set of REPLACE variants.
2. **Rules beyond `R`.** `r_f` for each public function and the decomposition
   rules for `senc`/`aenc` follow Def. 1's "handled in the standard way". There
   are no destructors for hashes or signatures. Equational theories (XOR, DH,
   multisets) are not modelled.
3. **"Used in `a`".** The causal reading (Plan B.1 item 3) is a modelling
   decision. The paper does not define it operationally. Witness detection from
   lemmas/restrictions (item 12) is also a decision; the `Witness-Actions`
   header remains available to override it.
4. **Knowledge from Tamarin `State` facts.** `K^i` comes from the pre-State
   payload and premise facts. Values only in a post-State are excluded for the
   current transition but enter `K` in the next transition through its
   pre-State (the modeller's statement of `AgSt(H, i+1, K^{i+1})`).
5. **Persistence vs. generated models.** `Forget` and `R̄` persist across the
   human's transitions *in the analysis* (later annotated transitions see
   them). As before, each annotated transition produces its own mutated theory
   in which only that transition is mutated. Later transitions are not
   rewritten, and the human's `State` facts keep their values (monotonic
   knowledge).
6. **`Π = ∅` before forgetting.** This means the extracted `K` cannot reproduce
   the original send. Message lapses then use the legacy textual fallback, and
   rule lapses follow line 51 (SKIP). Both are flagged in the report. This
   cannot be resolved without a richer knowledge model.
7. **Format of atoms (Def. 3)** is read as "all atoms share one format", which
   is needed for the paper's own case study.
8. **Not implemented (Defeasible Logic part, excluded by instruction):**
   forgetting a procedure as a whole, cues/reinstaters, cognitive traces.
9. **No formal proof.** Correctness evidence is the differential testing against
   an independent oracle, the hand-derived examples and the end-to-end checks.
   This is strong evidence for the cases covered, not a proof.
