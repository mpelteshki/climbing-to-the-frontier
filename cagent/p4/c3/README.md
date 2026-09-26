# C3 — complete

`ProofPursuit.P4.C3.solution` proves `Statement k` for every `2 ≤ k ≤ 8`. It combines the `k = 2` base case with the complete C1 (`k = 3`), C2 (`k = 4`), `Five` (`k = 5`), `Six` (`k = 6`), and `Seven` (`k = 7`) proofs. For `k = 8`, `Eight.step` derives `Statement 8` from `Statement 7`, and `Progress.solution` discharges that premise with `Seven.solution`.

The theorem has no additional premises. Source: [`../lean/ProofPursuit/P4/C3.lean`](../lean/ProofPursuit/P4/C3.lean). Build and check it using the commands in the [P4 README](../README.md).
