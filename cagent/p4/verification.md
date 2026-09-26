# Verification record

Verified from `cagent/p4/lean` on 2026-09-26 with Lean `4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) and Lake `5.0.0-src+5045d00`.

| Command | Result |
| --- | --- |
| `lake build ProofPursuit.P4.Progress` | Exit 0; all seven build jobs succeeded, including `Basic`, `C1`, `C2`, `Five`, `Six`, and `Progress` |
| `lake env leanchecker ProofPursuit.P4.Progress` | Exit 0; no output |

The build prints `#print axioms` results from `Progress.lean` for `Progress.solution`, `C1.solution`, `C2.solution`, `Five.solution`, and `Six.solution`. Each reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No source file in this package contains `sorry`, `admit`, an `axiom` declaration, `native_decide`, or `bv_decide`. The six packaged `.lean` files were compared byte for byte with the verified source versions in `lean/ProofPursuit/P4/` at packaging time. The package manifest contains no external packages; its only import outside this package is Lean's bundled `Std`.

This verifies the `k = 2, 3, 4, 5, 6` range. It does not verify `k = 7` or `k = 8`.
