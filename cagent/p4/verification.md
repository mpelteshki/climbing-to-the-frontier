# Verification record

Verified from `cagent/p4/lean` on 2026-09-26 with Lean `4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) and Lake `5.0.0-src+5045d00`.

| Command | Result |
| --- | --- |
| `lake build ProofPursuit.P4.C3` | Exit 0; all eleven build jobs succeeded, including `Basic`, `C1`, `C2`, `Five`, `Six`, `Parity`, `Seven`, `Eight`, `Progress`, and `C3` |
| `lake env leanchecker ProofPursuit.P4.C3` | Exit 0; no output |

The build prints `#print axioms` results for `C3.solution`, `Progress.solution`, `C1.solution`, `C2.solution`, `Five.solution`, `Six.solution`, `Seven.solution`, and `Eight.step`. Each reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No source file in this package contains `sorry`, `admit`, an `axiom` declaration, `native_decide`, or `bv_decide`. The original ten packaged `.lean` files were compared byte for byte with the verified source versions in `lean/ProofPursuit/P4/` at packaging time. The package manifest contains no external packages; its only import outside this package is Lean's bundled `Std`.

This verifies the full C3 range `k = 2, 3, 4, 5, 6, 7, 8`. `Eight.step` is conditional on `Statement 7`, and `Progress.solution` discharges it using `Seven.solution`.

## C4 progress checkpoint

Verified 2026-09-26 in the standalone Std project:

| Module | Build | Independent kernel recheck | Scope |
| --- | --- | --- | --- |
| `Reduction` | Pass | Pass | CRT equivalence and counterexample compression |
| `ThroughNine` | Pass | Pass | Unconditional cases 2–9, including `Nine` and `CommonPrime` dependencies |
| `Density` | Pass | Pass | Finite density bound and compressed version |
| `FiniteSearch` | Pass | Pass | Generic finite-search correctness; no concrete k≥10 certificate |
| `Survivor13` | Pass | Pass | Explicit seven- and thirteen-modulus impossibility |
| `DensityAudit13` | Pass (about 25 seconds) | Pass via `Minimality13` import | Canonical density test for every sublist of explicit candidate |
| `Minimality13` | Pass (about 28 seconds) | Pass | Actual residue assignments for every sublist with at most six entries |

All rechecks use `lake env leanchecker <module>` and return exit 0. The density audit depends only on `propext` and `Quot.sound`; semantic proofs may also use `Classical.choice`. No unproved custom axioms or `sorry` are used. The certificates and definitions are embedded in the published Lean source and require no Python outputs or uncommitted files. Build times are observations from this machine, not guaranteed limits.

## Unconditional range through 12

Fresh isolated checkout verification, 2026-09-26:

- `lake build ProofPursuit.P4.ThroughTwelve`: exit 0, all 27 jobs passed.
- `lake env leanchecker ProofPursuit.P4.ThroughTwelve`: exit 0, no output.
- `ThroughTwelve.solution` proves `∀ k, 2 ≤ k → k ≤ 12 → Statement k`; printed dependencies are exactly `propext`, `Classical.choice`, `Quot.sound`.
- The k=11 concrete certificate checks with `decide`; its `no_candidate` theorem uses only `propext` and `Quot.sound`. No search-exhaustion hypothesis remains in the final range theorem.
- Fresh build observed 115 seconds for `ElevenCertificate`, 81 seconds for `TwelveCheck`, and 67 seconds for `NormalForm12`; these are local observations, not portable guarantees.

C4 remains `Not solved`: the cell also requires the complete survivor audit for sizes 9–16.

`Sharpness` also passes fresh `lake build` and independent `leanchecker`: residues 0,…,k−1 modulo k form pairwise disjoint classes, with all pairwise modulus gcds equal to k.

## Packaged computational replay

Focused replay in the isolated publication checkout passed (all exit 0): `audit.py` for k=9–14; `compare_independent.py` with empty symmetric differences at every k=9–16; `verify_global_minima.py` for 107 claims and 20,436 facts including 19,704 smaller SAT witnesses; `verify_refutations.py` for 59 trees / 40,292 nodes; `verify_cert_strings.py` for those same trees and 83,325-byte ASCII encoding. Exact commands appear in `audit/MANIFEST.md`. These checks verify saved certificates/results; they do not rerun both complete searches.

The k=11 generator reproduced the embedded certificate byte for byte, SHA-256 `83bd0c47bc24923a50ae3df347b5946349d3788302ab76bd9c525ffdb18a3689`.
