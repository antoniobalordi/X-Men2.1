# Invoice-Payment ceremony — procedural forgetting (Forget, case (3))

Run date: 2026-11-11. X-Men 2.1 built from this repository (Java 21.0.12.1), Java derivation engine with default limits, blocking mode `CASE1_WEAK`, external Haskell engine off. Tamarin 1.12.0 and Maude 3.5.1.

Input: [Forget_Invoice_Procedural.spthy](Forget_Invoice_Procedural.spthy). It is the ceremony of [../invoice-payment](../invoice-payment/README.md) with two changes taken from the paper:

- S encrypts all its messages to H under a key `kSH` shared by S and H.
- The setup message carries the service and the amount as well as `accOld` (Fig. 12).

The lapse is `ForgetRule('r_sdec')` in `H_2`. When the account-change notice arrives, H forgets how to decrypt with a symmetric key (case (3) of Definition 4).

## What X-Men does

From the [derivation report](Forget_Invoice_Procedural_DerivationTree.txt):

- **H_2 (notice):** the notice is added to H's knowledge and `r_sdec` to the forgotten rules. Every derivation of `accNew` applies `sdec`, so H cannot read it. `RecordAccount($Human,$S,accNew)` is removed (NEGLECT).
- **H_3 (reminder and order, no annotation):** the forgotten rule persists. H cannot read the reminder either, but already knows the service and the amount from the setup. `accNew` is the only component of the order that H cannot derive (`U = {accNew}`). `accOld` has the same format and label, and the order containing `accOld` can be built without `sdec`, so Forget triggers a REPLACE (`Repl(accNew) = {accOld}`, one variant).
- The replacement is propagated to B's receipt of the order, the approval request and the confirmation, as in case (1). The approval request is protected by asymmetric encryption and signatures, so H can still read it and perform `CheckApproval`. No later step is neglected.

From `H_3` on, the mutant has the same send and receive events as the [case (1) mutant](../invoice-payment/Forget_Invoice_Input_M0.m). Before `H_3`, S's messages differ only in being encrypted under `kSH`.

## Tamarin results

| Lemma | Original | Forget variant |
| --- | --- | --- |
| `Transfer_as_confirmed` (paper Listing 3, SG3) | verified (8 steps) | verified (8 steps) |
| `Transfer_to_latest_account` (paper Listing 4, SG4) | verified (19 steps) | falsified - found trace (11 steps) |
| `Payment_To_Latest_Nominated_Account` | verified | falsified - found trace |
| `Payment_Not_Into_Lost_Account` | verified | falsified - found trace |
| `Transfer_Requires_Confirmation` | verified | verified |
| `Lapse_Pays_Old_Account` (exists-trace) | falsified - no trace found | verified |
| `Functional` (exists-trace) | verified | verified |

Both runs used `--prove --quit-on-warning`, passed all wellformedness checks and reached a conclusive result for every lemma, with no proof-depth bound. Processing times were 5.34 s (original) and 6.29 s (variant).

## Files

- [Mutation ZIP returned by X-Men](Forget_Invoice_Procedural_mutations.zip), containing the [generated theory](Forget_Invoice_Procedural_M0.m) and the [derivation report](Forget_Invoice_Procedural_DerivationTree.txt)
- [Original proof](original-proved.spthy) and [prover log](original-tamarin.txt)
- [Mutant proof](mutated-proved.spthy) and [prover log](mutated-tamarin.txt)
- [Counterexample and witness traces (JSON)](mutated-traces.json)

`PaperArtefactsGoldenTest` checks that X-Men regenerates `Forget_Invoice_Procedural_M0.m` byte for byte from the input.

## Reproduce

As for [case (1)](../invoice-payment/README.md#reproduce), with this folder's input:

```sh
mkdir -p target/invoice-payment-procedural
curl --fail http://127.0.0.1:8081/api/forget/mutations \
  -H 'Haskell-Activate: false' \
  -F file=@examples/invoice-payment-procedural/Forget_Invoice_Procedural.spthy \
  -o target/invoice-payment-procedural/Forget_Invoice_Procedural_mutations.zip
unzip -o target/invoice-payment-procedural/Forget_Invoice_Procedural_mutations.zip -d target/invoice-payment-procedural
tamarin-prover examples/invoice-payment-procedural/Forget_Invoice_Procedural.spthy --prove --quit-on-warning --output=target/invoice-payment-procedural/original-proved.spthy
tamarin-prover examples/invoice-payment-procedural/Forget_Invoice_Procedural_M0.m --prove --quit-on-warning --output=target/invoice-payment-procedural/mutated-proved.spthy --output-json=target/invoice-payment-procedural/mutated-traces.json
```

SHA-256:

- `Forget_Invoice_Procedural.spthy`: `7816f4b559a10e644620d7375bd567461a1af7fe6c389d839dad7029df894ac0`
- `Forget_Invoice_Procedural_M0.m`: `ca0c2323cec11202950713e7332dbfee9198259c299012017a6a536174852a73`
