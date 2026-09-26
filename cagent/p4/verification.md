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

No source file in this package contains `sorry`, `admit`, an `axiom` declaration, `native_decide`, or `bv_decide`. The ten packaged `.lean` files were compared byte for byte with the verified source versions in `lean/ProofPursuit/P4/` at packaging time. The package manifest contains no external packages; its only import outside this package is Lean's bundled `Std`.

This verifies the full C3 range `k = 2, 3, 4, 5, 6, 7, 8`. `Eight.step` is conditional on `Statement 7`, and `Progress.solution` discharges it using `Seven.solution`.
