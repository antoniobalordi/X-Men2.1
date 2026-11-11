# Invoice-Payment ceremony — Forget, case (1)

Run date: 2026-11-11. X-Men 2.1 built from this repository (Java 21.0.12.1), Java derivation engine with default limits, blocking mode `CASE1_WEAK`, external Haskell engine off. Tamarin 1.12.0 and Maude 3.5.1.

Input: [Forget_Invoice_Input.spthy](Forget_Invoice_Input.spthy). Supplier S nominates account `accOld`, sends an account-change notice for `accNew` (after which S can no longer use `accOld`), then a payment reminder; H pays through bank B with signed and encrypted messages. The lapse is annotated where it happens: `Forget(accNew)` in `H_2`, the receipt of the notice. H reads the notice but does not retain `accNew` (case (1) of Definition 4). The variant with procedural forgetting is in [../invoice-payment-procedural](../invoice-payment-procedural/README.md).

## What X-Men does

From the [derivation report](Forget_Invoice_Input_DerivationTree.txt):

- **H_2 (notice):** `accNew` does not enter H's knowledge. The internal action `RecordAccount($Human,$S,accNew)` is removed (NEGLECT).
- **H_3 (reminder and order, no annotation):** the lapse persists. The order H is expected to send contains `accNew`, which H cannot derive. `accOld` has the same format and label (`'account'`), so Forget triggers a REPLACE (`Repl(accNew) = {accOld}`, one variant).
- The replacement is propagated to B's receipt of the order, the approval request and the confirmation. In `H_4_M`, `CheckApproval`, `Confirmed` and `H_Confirm` all name `accOld`. No later step is neglected.

## Tamarin results

| Lemma | Original | Forget variant |
| --- | --- | --- |
| `Transfer_as_confirmed` (paper Listing 3, SG3) | verified (8 steps) | verified (8 steps) |
| `Transfer_to_latest_account` (paper Listing 4, SG4) | verified (25 steps) | falsified - found trace (11 steps) |
| `Payment_To_Latest_Nominated_Account` | verified | falsified - found trace |
| `Payment_Not_Into_Lost_Account` | verified | falsified - found trace |
| `Transfer_Requires_Confirmation` | verified | verified |
| `Lapse_Pays_Old_Account` (exists-trace) | falsified - no trace found | verified |
| `Functional` (exists-trace) | verified | verified |

Both runs used `--prove --quit-on-warning`, passed all wellformedness checks and reached a conclusive result for every lemma, with no proof-depth bound. Processing times were 5.16 s (original) and 5.87 s (variant). The `Lapse_Pays_Old_Account` witness is the scenario of the paper's Fig. 5: S nominates `accOld` and then `accNew`, sends the reminder, and B executes the transfer into `accOld`. The `Functional` witness shows that a payment can complete and reach H; it does not show completion on every execution.

## Modelling notes

- The paper's lemmas are used verbatim (ASCII quotes). Their action facts are in the model: `S_Nominate(s, acc)` in `S_1` and `S_2`, `H_Confirm(h, b, s, srv, amt, acc)` in `H_4`, and `Transfer(amt, acc)` in `Bank_2`. The repository's additional lemmas use the 6-ary `TransferDetail(b, h, s, svc, amt, acc)`.
- The final message is labelled `'status'`, as in the paper's role scripts.
- The account-change notice (`S_2`) is part of every run.
- Results assume secure channels between the agents, uncompromised keys, and a single ceremony (`OnlyOnce`).

## Files

- [Mutation ZIP returned by X-Men](Forget_Invoice_Input_mutations.zip), containing the [generated theory](Forget_Invoice_Input_M0.m) and the [derivation report](Forget_Invoice_Input_DerivationTree.txt)
- [Original proof](original-proved.spthy) and [prover log](original-tamarin.txt)
- [Mutant proof](mutated-proved.spthy) and [prover log](mutated-tamarin.txt)
- [Counterexample and witness traces (JSON)](mutated-traces.json)

`PaperArtefactsGoldenTest` checks that X-Men regenerates `Forget_Invoice_Input_M0.m` byte for byte from the input.

## Reproduce

Start X-Men on its default port (8081), upload [the input](Forget_Invoice_Input.spthy), select **Forget Mutation**, leave the external Haskell option off, and download the bundle. The API equivalent is:

```sh
mkdir -p target/invoice-payment
curl --fail http://127.0.0.1:8081/api/forget/mutations \
  -H 'Haskell-Activate: false' \
  -F file=@examples/invoice-payment/Forget_Invoice_Input.spthy \
  -o target/invoice-payment/Forget_Invoice_Input_mutations.zip
unzip -o target/invoice-payment/Forget_Invoice_Input_mutations.zip -d target/invoice-payment
```

X-Men must use its shipped vocabulary, which lists `SndS`/`RcvS` as channel facts. A vocabulary saved in the X-Men settings (`~/.xmen/settings.json`) that lists only `Out`/`In` hides this model's sends, and the mutant is then left unchanged. The report in this folder was generated with `--logging.level.com.xmen=WARN`. At the default INFO level, the same report is interleaved with log lines.

Verify with Tamarin and Maude installed:

```sh
tamarin-prover examples/invoice-payment/Forget_Invoice_Input.spthy --prove --quit-on-warning --output=target/invoice-payment/original-proved.spthy
tamarin-prover examples/invoice-payment/Forget_Invoice_Input_M0.m --prove --quit-on-warning --output=target/invoice-payment/mutated-proved.spthy --output-json=target/invoice-payment/mutated-traces.json
```

SHA-256:

- `Forget_Invoice_Input.spthy`: `4d1f1315051bb8b30746276ca20997f0efa64800cd29e7bd4b8b2ab8f62d000f`
- `Forget_Invoice_Input_M0.m`: `1fc76e6ea70db901ae3d6d5051a899e6d72968127a52a67cc02a6efb20f94491`
