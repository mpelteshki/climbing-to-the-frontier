# P1: angles between lines

This package contains a shared Lean source file and written proofs for two general cells. The Lean results are **partial progress**: they formalize only the fixed-size geometric cases listed below. The complete C1 and C2 arguments are in [written-proofs.md](written-proofs.md); they are not complete Lean formalizations.

| Cell | Lean-checked geometric scope | Written scope |
| --- | --- | --- |
| [C1](c1/README.md) | N = 2 via `angle2_le`; N = 3 or 4 via named theorems, with arbitrary unit representatives in ℝ² and repeated lines allowed | All N planar lines |
| [C2](c2/README.md) | m = 2 in ℝ¹; m = 3 in ℝ² with first and last vectors orthogonal | All m ≥ 2 |
| [C3](c3/README.md) | d = 1 via the scalar C2 lemma; d = 2 via the planar three-line lemma | No general proof |
| [C5](c5/README.md) | d = 2 via the planar four-line lemma | No general proof |

C4 has no result in this package. C6 is paused. [statements.md](statements.md) records the problem statements and source links.

The toolchain is Lean 4.34.1; Mathlib is pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`. From this directory, reproduce with:

```sh
./verify.sh
```

The script fetches only the direct import modules and their dependencies. Its final `lake env lean Angles.lean` command should exit 0 and print standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) for the six named result declarations. [evidence/verification.log](evidence/verification.log) is the captured output from checking the identical source using the pinned local Mathlib checkout. [evidence/environment.txt](evidence/environment.txt) records the versions, pin, and source checksum. A clean download and build of this portable package were not run in the isolated packaging environment.
