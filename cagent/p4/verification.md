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
