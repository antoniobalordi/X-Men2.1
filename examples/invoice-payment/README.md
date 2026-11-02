# Invoice payment ceremony — fresh Forget/Tamarin run

Run date: 2026-10-27 (Europe/London). X-Men 2.0 source in this workspace compiled successfully with Java 21.0.12.1. Tamarin 1.12.0 and Maude 3.5.1 were used.

Input: [Forget_Invoice_Input.spthy](Forget_Invoice_Input.spthy). The input and generated variant are preserved unchanged from the verification run. The fresh X-Men `/api/forget/mutations` request returned HTTP 200 and one variant. Java derivation was used, with default limits and blocking mode `CASE1_WEAK`; the external Haskell engine was disabled. The verification run used isolated settings and output directories.

| Lemma | Original | Forget variant |
| --- | --- | --- |
| Payment_To_Latest_Nominated_Account | verified | falsified - found trace |
| Payment_Not_Into_Lost_Account | verified | falsified - found trace |
| Transfer_Requires_Confirmation | verified | verified |
| Lapse_Pays_Old_Account | falsified - no trace found | verified |
| Functional | verified | verified |

Both Tamarin commands exited successfully with `--prove --quit-on-warning`; all wellformedness checks passed and all five lemmas reached a conclusive result. No proof-depth bound was supplied. Proof times were 4.20s for the original and 5.13s for the variant. The security-property counterexamples are findings about the ceremony, not execution errors.

X-Men's derivation report identifies `Forget(accNew)` in H_3, blocks the derivation needing that value, and replaces it with the remembered account `accOld`. The generated order and H_4's approval/confirmation name accOld. The supplier has already nominated accNew and lost access to accOld, but the human confirms the stale order and the bank executes it. The bank-confirmation property still holds. The Functional witness establishes that payment can complete and success can reach the human; it does not establish completion on every execution.

The input retains `RecordAccount(accNew)` in H_2: this run models forgetting at payment time in H_3. Some input comments describe failure to record the notice, which is not the literal behavior tested. Results assume the model's secure channels, uncompromised keys, and single ceremony/session.

Artifacts:

- [Fresh mutation ZIP](Forget_Invoice_Input_mutations.zip)
- [Generated theory](Forget_Invoice_Input_M0.m)
- [Derivation report](Forget_Invoice_Input_DerivationTree.txt)
- [Original proof](original-proved.spthy) and [prover log](original-tamarin.txt)
- [Mutant proof](mutated-proved.spthy) and [prover log](mutated-tamarin.txt)
- [Counterexample and witness traces (JSON)](mutated-traces.json)

Reproduce from the repository root with X-Men running on its default port (8081). Upload [the input](Forget_Invoice_Input.spthy), select **Forget Mutation**, leave the external Haskell option off, then download the generated bundle. The API equivalent is:

```sh
mkdir -p target/invoice-payment
curl --fail http://127.0.0.1:8081/api/forget/mutations \
  -H 'Haskell-Activate: false' \
  -F file=@examples/invoice-payment/Forget_Invoice_Input.spthy \
  -o target/invoice-payment/Forget_Invoice_Input_mutations.zip
unzip -o target/invoice-payment/Forget_Invoice_Input_mutations.zip -d target/invoice-payment
```

Verify the included original and generated variant with Tamarin and Maude installed:

```sh
mkdir -p target/invoice-payment
tamarin-prover examples/invoice-payment/Forget_Invoice_Input.spthy --prove --quit-on-warning --output=target/invoice-payment/original-proved.spthy
tamarin-prover examples/invoice-payment/Forget_Invoice_Input_M0.m --prove --quit-on-warning --output=target/invoice-payment/mutated-proved.spthy --output-json=target/invoice-payment/mutated-traces.json
```

To verify a newly generated variant instead, use `target/invoice-payment/Forget_Invoice_Input_M0.m` as the second command's input.

SHA-256:

- `Forget_Invoice_Input.spthy`: `ba05c6c71b1d72f4f5a0171a69bcc2c6e4724cece480290037237e1d5169c19f`
- `Forget_Invoice_Input_M0.m`: `3f80915cc22e9485c24bff27d31f05de320862a9209cf336929f10f73848e9fe`

No application source or original input was changed. The desktop UI, external Haskell engine, and full Java test suite were not exercised.
