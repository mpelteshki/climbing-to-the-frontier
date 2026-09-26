# P1: angles between lines

This package contains complete written proofs for C1–C5, partial Lean formalizations, and partial written results for the open cell C6. **Solved** below means a rigorous proof meets the live written-proof hand-in rule; it does not mean the full statement is Lean-formalized, submitted, or accepted. The [criteria audit](criteria-audit.md) checks each proof against the exact live statement.

**[Final judge-ready write-up: C1–C5](writeup.md)** contains all five complete arguments in one Markdown item. [Package manifest](package-sha256.txt) records its files.

| Cell | Status | Complete written result | Lean-checked scope |
| --- | --- | --- | --- |
| [C1](c1/README.md) | Solved — complete written proof; Lean partial | All N planar lines, including empty and repeated configurations | N = 2 via `angle2_le`; N = 3, 4 via named theorems |
| [C2](c2/README.md) | Solved — complete written proof; Lean partial | All m ≥ 2 with non-neighbors orthogonal | m = 2 in ℝ¹ and m = 3 in ℝ² |
| [C3](c3/README.md) | Solved — complete written proof; Lean partial | All d ≥ 1 through the auxiliary bound in C4 §1 | d = 1, 2 |
| [C4](c4/README.md) | Solved — complete written proof; Lean partial | Five lines in ℝ³ and six in ℝ⁴, both sharp | Analytic/coordinate lemmas, compact maximizer, sparse degree-two reduction, corank bounds |
| [C5](c5/README.md) | Solved — complete written proof; Lean partial | All d ≥ 2, N = d + 2, sharp | d = 2 and C4 lemmas used in the written proof |
| [C6](c6/README.md) | Not solved — partial written results; no Lean | [Partial results](c6/partial-results.md): (6,3) case from C5 by averaging; explicit non-sharp bound for all N ≥ d+2; N = d+3 reduced to the connected sparse case. Cell not solved. | None |

The full general statements are not assembled into Lean theorems. [statements.md](statements.md) records the problem statements and source links. C1–C5 complete written proofs and their supporting Lean sources are included in this published package. No hackathon submission or organizer acceptance is claimed.

The toolchain is Lean 4.34.1; Mathlib is pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`. From this directory, reproduce with:

```sh
./verify.sh
```

The script fetches the direct Mathlib imports and dependencies, then checks all modules in dependency order. [Replay evidence](evidence/replay/README.md) records the sequential local replay of these exact files into a fresh output directory, using the same pinned Mathlib checkout. A clean network download of this portable checkpoint was not run.
