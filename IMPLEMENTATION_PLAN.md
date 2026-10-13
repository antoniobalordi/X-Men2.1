# Implementation Plan — Procedural Forgetting and Derivation Audit

Status: **plan written before any implementation change**. Sections marked
*(updated)* were revised after new findings during implementation.

Sources used as specification:

* **Conference paper** — *Formal Modeling and Analysis of Human Memory Lapses in
  Security Ceremonies* (IEEE format, 12 pp.). Introduces FORGET of messages
  (Definition 3, Definition 4, Algorithm 1 with 36 lines).
* **Journal manuscript** — *Human Memory Lapses in Security Ceremonies: Formal
  Modelling and Analysis* (Journal of Cybersecurity draft, 34 pp.). Authoritative
  where it revises the conference version. Per the author's instruction, the
  **Defeasible Logic part (§7 "Defeasible Logic for Forget", §8 "Extended
  Example", Algorithm 2) is ignored**. Everything below is derived from §3–§6 and
  Algorithm 1 of the journal (53 lines).

Terminology used in this document:

* *Atomic forgetting* = the existing FORGET of a message (Definition 4, cases 1
  and 2: forget a just-received message / forget a message already known).
* *Procedural forgetting* = Definition 4, case 3: the human forgets a
  Dolev-Yao **inference rule** `r ∈ R` (Definition 5, Algorithm 1 lines 40–53).
  "Forgetting a procedure as a whole" (`Π̄_H`, Definition 8) only exists in the
  Defeasible Logic section and is therefore **out of scope**.

---

## A. Current architecture

### A.1 Input handling and `.spthy` parsing

1. Entry points: `POST /api/forget/mutations` (`ForgetMutationController`) and
   `POST /api/generateMutations` with header `Forget-Mutation: true`
   (`MutationController`). The JavaFX UI (`XMenInterface.sendMutationRequest`)
   posts the selected `.spthy` file to the first endpoint when *Forget* is ticked.
2. `FileSplitterService.splitFile` splits the file into preamble (theory header,
   `builtins:`, `functions:`), rules, and postamble (restrictions, lemmas).
3. `FileLoadingService` → `ModelLoader` parses the rules with the ANTLR grammar
   (`TamarinLexer`/`TamarinParser`/`TamVisitor`) into `Rule` objects whose
   premises, actions and conclusions are `Fact`s; fact parameters are `Value`,
   `PSpecial` (tuples), `FSpecial`, `Nary_app` (function applications). Term
   payloads are mostly kept as **strings** inside `Value` names (e.g.
   `"senc(<$Human,pw1>,k(nH,nB))"`).
4. `ForgetMutationParser.parseForgetMutations` scans every *human* rule (a rule
   whose actions contain the human marker `H()`) for `Forget(x)` action facts,
   records `rule name → {x,…}` in `ParametersBundle.forgetMutationSet`, and
   removes the `Forget` action from the rule. If none is found it throws
   `"Forget function not found …"` (HTTP 400; the UI matches this text).

### A.2 Internal representation of messages

`DerivationCheckServiceImpl.parseStringToMessage` (duplicated in
`ForgetMutationStrategy`) converts payload strings into the `Message` term model:

| Tamarin text | `Message` |
|---|---|
| `x`, `~x`, `$X`, `'c'` | `Atom` |
| `<a,b,c>` | `Pair(a, Pair(b, c))` (right-nested, as in Tamarin) |
| `f(t1,…,tn)` incl. `senc`, `aenc`, `pk`, `h`, user functions | `PredictiveFunction(f, [t1…tn])` |
| `{m}_{k}` (non-Tamarin legacy notation) | `Encrypt(m, k)` |

Important consequence: **every Tamarin encryption is a `PredictiveFunction`**;
the `Encrypt` class only arises from the legacy notation.

### A.3 Knowledge and the Forget context

* `ForgetContext` holds the monotonic knowledge `K`, the `Forget` set, the
  blocking mode (Case 1/2/3) and a label map (from `!Type(…, 'label', value)`
  facts, `SetupKnowledgeExtractor`).
* `MutationGeneratorServiceImpl.generateMutation` calls
  `ForgetMutationStrategy.applyMutation` once per human rule, in file order, with
  the same `ParametersBundle`, so the `ForgetContext` persists across transitions.
* `K` is initialised once, at the first human rule, from that rule's pre-State,
  **post-State** and 4-ary inbound payloads
  (`extractKnowledgeWithoutForgetRemoval`); afterwards only the received payload
  of each transition is added (`ForgetContext.updateForTransition`).

### A.4 Computation of derivations

* `ForgetDerivationChecker.getAllDerivations` →
  `DerivationServiceImpl.deriveToDepthNoPrint` → `deriveAllRecursive`, a backward
  search producing `Derivation(goal, ruleLabel, premises)` trees with labels
  `Initial`, `Pairing`, `Decryption(c)`, `Projection-First/Second`,
  `PredictiveFunction(f)`; a goal may not repeat on a branch (`visitedGoals`).
  Results are capped (depth 10, 50 derivations, cartesian cap per node).
* `BlockingChecker.extractHypotheses` collects `Initial` leaves (`Hyp_π`);
  `isBlocked` implements Cases 1–3 (Definition 6).
* The Haskell service (`HybridDerivationService`) is only consulted by
  `DerivationCheckService.isDerivable`, which no mutation calls; it does **not**
  influence Forget decisions.

### A.5 Execution of atomic forgetting (`ForgetMutationStrategy.applyMutation`)

1. Update `K`/`Forget` for the transition (`updateForTransition`).
2. Neglect: internal (non-core) actions whose parameters textually contain the
   forgotten name are marked for removal.
3. Target `m2` = payload of the outbound fact (`Out`/`SndS`); if none → Neglect
   only.
4. Enumerate derivations of `m2`; if **none** → *textual substitution fallback*
   (replace the forgotten name by a type-compatible value, not part of
   Algorithm 1); otherwise per derivation: blocked hypotheses → replacement sets
   (`ReplacementComputer`) → variants.
5. Outcomes: send preserved (remove annotation) / Replace (one theory per
   variant, `_M<i>` suffix, propagation to later receivers) / Skip (remove send
   and the matching receive).

### A.6 Output

`MutatedFileGenerator` writes one `<Theory>_M<i>.m` file per mutated theory
(preamble + rules + postamble); `ZipService` returns them as a zip together with
`_DerivationTree.txt` (stdout captured by `DerivationTreeCaptureService`).

---

## B. Formal requirements (journal §3–§6, Algorithm 1)

| Item | Meaning | Implementation requirement | Code mapping |
|---|---|---|---|
| Def. 1–3 (algebra, `submsg`, `format`) | Terms over pairs, `senc/sdec`, `aenc/adec`, other operators "handled in the standard way"; format = top-level symbol | Term model + format classes | `Message` classes, `TermFormat` |
| §3.2 rules `R = {r_pair, r_unpair, r_senc, r_sdec, r_aenc, r_adec}` | Dolev-Yao inference; both projections are one rule `r_unpair` | Every derivation node must name the rule applied and list **all** its premises (decryption: ciphertext **and** key) | new `InferenceRule`; `Derivation` |
| §3.2 derivation, `Hyp_π` (Def. 6) | Finite tree, leaves = hypotheses from `K` | `Hyp_π` = all leaves | `BlockingChecker.extractHypotheses` |
| §3.2 normal derivations | No rule application immediately undone by its inverse; "search the finite space of normal derivations" | Enumerate exactly the normal derivations (finite) | new `NormalDerivationEnumerator` |
| Def. 4 (FORGET) | Lapse = (1) forget received `m1`, (2) forget known `m`, (3) forget rule `r` | Accept message targets and rule targets per transition | parser, `ForgetContext`, strategy |
| **Def. 5** | `Rules(π)` = distinct rules applied in `π`; forgetting `r` adds it to `R̄_H` and blocks every `π` with `r ∈ Rules(π)` | Compute `Rules(π)`; persist `R̄_H` across transitions | `DerivationRules.rulesOf`, `ForgetContext.forgottenRules` |
| Def. 6 (Blocked, Cases 1–3) | Case 1: `Hyp ∩ Forget`; Case 2: hyps derivable from `Forget` with pair rules; Case 3: with all DY rules | Exact closure computations | `BlockingChecker` + new `DolevYaoDeducer` |
| Def. 7 | `K ⊢_Forget m` iff some `π` has no blocked hypothesis | Exact existence test | `ForgetDerivationChecker.derivableUnderForgetting` |
| Alg. 1 l.2–11 | State update for message lapses | `m = m1`: `K`, `Forget`, `R̄` unchanged; else `K ∪ {m1}`, `Forget ∪ {m}` | `ForgetContext.updateForTransition` |
| Alg. 1 l.12–14 | `m` used in `a` ⇒ NEGLECT, **then continue** with the send decision (journal change: the conference version used `else`) | Neglect is not exclusive with preserve/replace/skip | strategy |
| Alg. 1 l.15–39 | `Π` = all normal derivations of `m2`; preserve if one is unblocked; else per `π`, per blocked `m̄`, `R_m̄ = {m̄' ∈ K | m̄' ∉ Forget, same format, same label}`; every combination ⇒ REPLACE variant; none ⇒ SKIP | Complete `Π`; per-combination distinct variants | strategy, `ReplacementComputer` |
| **Alg. 1 l.40–43** | Rule lapse: `K ∪ {m1}`, `Forget` unchanged, `R̄ ∪ {r}` | State update | `ForgetContext.forgetRule` |
| **Alg. 1 l.44–46** | `r` used in `a` ⇒ NEGLECT | Decide whether an internal action needs `r` | strategy + deducer |
| **Alg. 1 l.47–52** | `Π := {π | K ⊢ m2, Rules(π) ∩ R̄ = ∅}`; preserve if some `π ∈ Π` is unblocked, else SKIP. **No REPLACE** for a forgotten rule | Exact test; Skip + matching receive removal | strategy |
| §4.3 matching/propagation | Mutated send ⇒ matching receive mutated; skipped send ⇒ matching receive removed; NEGLECT needs no matching; forgotten message usable again once re-received | Reuse existing matching code | strategy |

### B.1 Ambiguities and the interpretation adopted

1. **Normal derivations.** The text forbids an application "immediately undone
   by its inverse" and claims the space of normal derivations is finite. Read
   literally (only adjacent inverse pairs), the space is *infinite* (e.g. with
   `K = {c = senc(<a,b>,k), k, b}`, `c` can be rebuilt as
   `senc(<fst(sdec(c,k)), b>, k)` and the detour can be nested arbitrarily).
   *Adopted:* a derivation is normal iff **no term occurs twice on any
   root-to-leaf path** (the minimal-derivation notion of Rusinowitch–Turuani,
   which the paper cites). This subsumes both forbidden adjacent patterns
   (`fst(pair(a,b)) = a` repeats `a`; `senc(sdec(c,k),k) = c` repeats `c`), is
   finite (all terms lie in `St(K ∪ {m})`), and agrees with the paper's examples
   (Example 4: exactly two derivations of `m1`). It never changes *whether* an
   unblocked derivation exists: removing a cycle only removes hypotheses and
   rules, and `Blocked` is monotone in `Hyp_π`.
2. **Rules beyond §3.2.** Tamarin models use `pk`, `h`, `sign`, user functions
   (e.g. `k/2`). *Adopted:* each public function symbol `f` gets a composition
   rule `r_f` (e.g. `r_h`, `r_sign`, `r_k`, `r_pk`); `senc`/`aenc`/pairs map to
   `r_senc`/`r_aenc`/`r_pair`; decomposition exists only for pairs (`r_unpair`),
   `senc` (`r_sdec`, same key) and `aenc(m, pk(sk))` (`r_adec`, needs `sk`).
   Functions declared `[private]` cannot be composed.
3. **"`r` is used in `a`"** (Alg. 1 l.44). Internal actions are action facts;
   Tamarin performs inference implicitly by pattern matching. *Adopted
   (semantic, causal):* `r` is used in `a` iff some argument of `a` was
   derivable from `K^{i+1}` without blocked hypotheses using `R \ R̄^i` but is not
   derivable using `R \ R̄^{i+1}`. This covers explicit destructor terms
   (`sdec(…)` in an action) as well as implicit dependence.
   *(updated)* The same causal test is applied to forgotten messages ("`m` is
   used in `a`", l.12), in addition to the existing textual test: §4.3 motivates
   NEGLECT with "the user forgets the key needed to decrypt a message whose
   content they must check", which the textual test alone cannot detect (the key
   does not occur in the check). The "before" state is the successor state
   without any lapse, the "after" state the one with all lapses of the
   transition.
4. **Persistence of `R̄`.** Definition 5 says forgetting `r` blocks every
   derivation using it, and `R̄` is carried to later states, while Algorithm 1
   line 15 does not mention `R̄`. *Adopted:* Definition 5 holds at every state, so
   message-lapse transitions after a rule lapse also exclude derivations using
   forgotten rules.
5. **Re-acquisition in the rule branch.** Line 42 keeps `Forget` unchanged, but
   §4.3 says a re-received forgotten message leaves the Forget set. *Adopted:*
   the §4.3 rule applies to all ordinary receives (as the existing code already
   does for message lapses).
6. **Several lapses in one transition.** Algorithm 1 handles exactly one lapse.
   *Adopted:* apply all state updates (messages, then rules), then decide with
   Definition 5 + Definition 7; REPLACE is attempted only if at least one message
   lapse is present and only over derivations that use no forgotten rule (a
   forgotten rule cannot be repaired by substitution).
7. **Format of atoms.** Definition 3 says the format of an atom is the atom
   itself, which would forbid replacing `PW1` by `PW2` (the paper's own case
   study). *Adopted (unchanged):* all atoms share the atomic format; labels
   distinguish them.
8. **"Replacing each `m̄` with `m̄'`" (l.28).** *Adopted:* substitute the leaves
   of `π` and recompute its conclusion rule by rule. A step that becomes invalid
   (e.g. decrypting with a substituted wrong key) invalidates the variant; a
   variant equal to `m2` is discarded; duplicates are merged.
9. **`K` in Tamarin models.** The paper: `K^{i+1} = K^i ∪ {m1} ∪ fresh(Pre_i)`.
   Tamarin models store knowledge in `State` facts. *Adopted:* `K^i` = accumulated
   `K` ∪ pre-`State` payload ∪ values of persistent premises read by the rule
   (`!Ltk`, `!Pk`, …) ∪ the agent's own name (first `State` argument) ∪ public
   constants; `K^{i+1} = K^i ∪ {m1} ∪ Fr(Pre_i)`. The **post-State is not used**,
   because it contains values the agent only obtains by inference from `m1`
   (e.g. `nB` from `aenc(<nH,nB>,pk(ltkH))`), which would hide `r_adec`/`r_unpair`
   from `Rules(π)` and make procedural forgetting vacuous.
10. **`Π = ∅` before any forgetting** (the extracted `K` cannot derive `m2` at
    all) violates Algorithm 1's implicit precondition. *Adopted:* message lapses
    keep the existing, documented textual-substitution fallback (logged as a
    precondition failure); rule lapses follow line 51 literally (SKIP) with a
    warning in the report.
11. **Replacement filter.** Line 22 requires `m̄' ∉ Forget` (syntactic). The code
    used "not blocked" (closure), which differs under Cases 2/3. *Adopted:* the
    literal reading of line 22. Likewise "same label" is read literally: an
    unlabelled hypothesis can only be replaced by an unlabelled candidate (the
    old code accepted any candidate when the hypothesis had no label).
12. *(updated)* **Witness actions.** Tamarin action facts used only by lemmas
    (e.g. `PasswordAttempt`) label the trace for the security properties; they
    are not internal checks of the role script (checks are constrained by
    restrictions). *Adopted:* an action fact referenced by a lemma and by no
    restriction is a witness: NEGLECT does not apply to it, and a REPLACE mirrors
    the chosen replacement in it (as the paper's Bank model does:
    `PasswordAttempt(U,B1,pw2,…)`). The existing `Witness-Actions` header still
    adds witnesses explicitly.

---

## C. Required code changes

### C.1 Defects found in Phase 1 (confirmed on the unmodified code with probes)

| ID | Defect | Violated requirement |
|---|---|---|
| D1 | Decryption node lists only the key derivation as premise ⇒ the ciphertext is missing from `Hyp_π` ⇒ a forgotten ciphertext never blocks a decryption derivation | §3.2 (`r_sdec` has two premises), Def. 6 |
| D2 | Decryption only matches the legacy `Encrypt` class ⇒ Tamarin `senc`/`aenc` are never decrypted | §3.2 completeness |
| D3 | Projection/decryption sources must be literally in `K` ⇒ no nested tuples, no projection of a decrypted pair, no decryption of a projected ciphertext | §3.2 completeness |
| D4 | User-defined (public) functions are never *composed* (conflated with decomposition) ⇒ e.g. `k(nH,nB)` underivable | Def. 1 "handled in the standard way" |
| D5 | Case 3 closure has the same gaps as D2/D3 ⇒ e.g. `Forget = {senc(m1,m2), m2}` does not block `m1` (contradicts Example 5) | Def. 6 Case 3 |
| D6 | Silent truncation (depth/derivation/cartesian caps) can drop the only unblocked derivation ⇒ spurious REPLACE/SKIP | Def. 7, Alg. 1 l.16 |
| D7 | `K` construction: post-State of the first human rule used as hypotheses; fresh and persistent-premise values never added; agent's own name missing | Alg. 1 l.4/8/41, §3.4 |
| S1 | `m = m1` lapse removes `m1` from `Forget` | Alg. 1 l.5 (`Forget` unchanged) |
| S2 | Variants for payloads under a function symbol collapse to the original message and every mutant uses the *first* replacement ⇒ duplicates, other combinations lost | Alg. 1 l.26–30 |
| D8 *(updated)* | Projection nodes attach the source pair as a bare leaf, bypassing the cycle check ⇒ non-normal derivations such as `pair(fst(P), snd(P))` for `P ∈ K` (found by the differential test) | §3.2 normal derivations |
| S3 *(updated)* | SKIP matched the send to remove by comparing the Tamarin payload text with the internal term rendering (`senc(($Human, pw1), …)`) ⇒ for `Out(...)` payloads with structure the send was never removed (latent: the old code never reached SKIP for Bank) | Alg. 1 l.37, l.51 |
| S4 *(updated)* | NEGLECT for a forgotten message only looked for the forgotten name inside the action ⇒ forgetting a decryption key never neglected a check on the decrypted content | Alg. 1 l.12, §4.3 |

### C.2 New components

* `service/derivation/InferenceRule` — rule identifiers (`r_pair`, …, `r_f`),
  parsing of user-supplied names (with aliases), membership of the paper's `R`.
* `service/derivation/DolevYaoTerms` — term classification (pairs, symmetric /
  asymmetric ciphertexts, composition rule of a term, subterms, private functions).
* `service/derivation/DolevYaoDeducer` — exact decision procedure
  "is `t` derivable from hypotheses `H` with allowed rules `A`?" (analysis
  closure + synthesis); used for Definition 7, Cases 2/3, Neglect checks.
* `service/derivation/NormalDerivationEnumerator` — complete enumeration of normal
  derivations (all premises recorded, decomposition sources = `St(K)`), with an
  explicit `truncated` flag instead of silent caps.
* `service/derivation/DerivationRules` — `Rules(π)`, replay of a derivation under
  a leaf substitution (variant construction).

### C.3 Modified components

* `model/Derivation` — optional `InferenceRule` per node (inferred from the label
  for backward compatibility).
* `DerivationServiceImpl.deriveAllRecursive` — delegates to the enumerator
  (fixes D1–D4); API unchanged.
* `BlockingChecker` — Cases 2/3 via the deducer (D5); helper for forgotten rules.
* `ForgetContext` — `forgottenRules` (`R̄_H`), `forgetRule`, fix S1.
* `ForgetDerivationChecker` — exact `derivableUnderForgetting` honouring `R̄`
  (D6); enumeration result with truncation flag; rule-need test.
* `ReplacementComputer` — literal `m̄' ∉ Forget`; replay-based variants (S2).
* `ForgetMutationStrategy` — per-transition `K` (D7); unified Algorithm 1 with
  the rule branch (lines 40–53); per-variant substitution and propagation (S2);
  analysis summary in the derivation report.
* `ForgetMutationParser` + `ParametersBundle` — `ForgetRule(r)` annotations
  (`forgetRuleSet`), validation, `[private]` function detection; the
  "not found" error accepts either annotation.
* `CeremonyVocabulary`, `vocabulary.yaml` — `forget-rule: "ForgetRule"` action
  name, added to `core-actions` so it is never treated as an internal action.
* Docs: `README.md`, `AlgorithmInfoDialog` text, this plan,
  `IMPLEMENTATION_REPORT.md`.

### C.4 Integration of procedural forgetting into the existing workflow

The user keeps the same workflow: upload a `.spthy`, annotate the human
transition, call the same endpoint/UI button, download the same zip. Only the
annotation differs:

```
rule H_2:
  [ State($Human,'2',<…>), In(aenc(<nH,nB>,pk(ltkH))) ]
--[ H(), ForgetRule('r_adec'), … ]->
  [ State($Human,'3',<…>), Out(senc(<$Human,pw1>,k(nH,nB))) ]
```

`Forget(x)` (atomic) and `ForgetRule(r)` (procedural) may be used in different
rules of the same file or together in one rule.

---

## D. Testing and validation strategy

1. **Independent reference oracle (test code only).** A *forward*, bottom-up
   generator of all derivation trees over `St(K ∪ {t})` (no shared code with the
   backward enumerator) for small finite inputs. Justification: locality of
   normal derivations (all terms are subterms of `K ∪ {t}`).
2. **Differential tests.** Hundreds of seeded random small `(K, t, Forget, R̄,
   Case)` instances: enumerator = oracle (same set of trees), deducer ⇔ oracle
   non-empty, "∃ unblocked derivation" agrees across all three methods.
3. **Hand-computed paper examples.** Examples 1–6 (journal §4) and the derived
   expectations for Cases 1–3; hand-built procedural cases (e.g. a target needing
   `r_sdec` twice, `r_unpair` on one branch only, alternative derivations with
   disjoint rule sets).
4. **Regression tests** for D1–D7, S1, S2, each with its minimal counterexample,
   run against the old code first (documented "before") and the new code
   ("after").
5. **End-to-end tests** through `/api/forget/mutations` and
   `/api/generateMutations`: existing atomic Bank example (expected REPLACE
   `pw1 → pw2`, now via a real derivation), multiple replacements (distinct
   mutants), procedural lapses with expected preserve / SKIP / NEGLECT outcomes,
   combined lapses, unknown rule name (400), missing annotation (400),
   non-derivable target, repeated runs (byte-identical output), unchanged
   behaviour of all pre-existing tests.
6. **Not executable here:** Tamarin is not installed, so mutated models are
   checked structurally, not proved/falsified.

---

## E. Implementation order

| Step | Work | Depends on | Checkpoint |
|---|---|---|---|
| 1 | Write oracle + regression tests; run on old code; record failures | — | failures match C.1 |
| 2 | `InferenceRule`, `DolevYaoTerms`, `DolevYaoDeducer`, enumerator, `Derivation` rule field | 1 | oracle/differential tests green |
| 3 | Wire enumerator into `DerivationServiceImpl`; deducer into `BlockingChecker` / `ForgetDerivationChecker` | 2 | old forget tests still green |
| 4 | `ForgetContext` (S1, `R̄`); per-transition `K` (D7) | 3 | Bank example decided by a real derivation |
| 5 | Parser + vocabulary for `ForgetRule`; strategy rule branch (l.40–53), Neglect test, combined lapses | 4 | procedural unit + E2E tests |
| 6 | Replay-based variants and per-variant rewriting (S2) | 5 | multi-replacement E2E test |
| 7 | Full test suite (incl. UI tests under Xvfb), determinism check | 6 | all green |
| 8 | README, report | 7 | — |

Risks: changing `K` construction and the enumerator can change the outputs of
existing examples. Every changed expectation must be justified against the
paper, not adjusted to make a test pass. Combinatorial growth of the enumeration
is bounded by caps that are now *reported* (truncation flag) and never used for
the existence decision, which is exact.
