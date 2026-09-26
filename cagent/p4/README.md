# P4: disjoint congruence classes

This standalone Lean 4 package proves the P4 statement for every number of classes `k` from 2 through 6. Its final theorem is `ProofPursuit.P4.Progress.solution`:

```lean
∀ k : Nat, 2 ≤ k → k ≤ 6 → ProofPursuit.P4.Statement k
```

`Statement k` says that if `k` integer congruence classes with **positive natural-number moduli** are pairwise disjoint as sets of integers, then two of their moduli have gcd at least `k`. The moduli may repeat. `DisjointClasses` asserts actual absence of a common integer; it is not a Chinese remainder theorem assumption. The shared `Basic.lean` proves the needed intersection direction from Bézout's identity.

The package uses Lean `v4.34.1` and its bundled `Std` library, with no external dependencies. From this directory:

```sh
cd lean
lake build ProofPursuit.P4.Progress
lake env leanchecker ProofPursuit.P4.Progress
```

The `leanchecker` command succeeds with exit status 0 and no output. To inspect theorem dependencies directly:

```sh
lake env lean ProofPursuit/P4/Progress.lean
```

The source prints the axioms of the combined theorem and each component theorem. The audit found only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms or `sorry` declarations. See [verification.md](verification.md) for the recorded commands and results.

| Cell | Certified theorem | Status |
| --- | --- | --- |
| [C1](c1/README.md) | `Statement 3` | Complete |
| [C2](c2/README.md) | `Statement 4` | Complete |
| [C3](c3/README.md) | `Statement k` for `2 ≤ k ≤ 6` | Partial: `k = 7, 8` remain |

The package also contains individual proofs of `Statement 5` and `Statement 6`. It makes no claim for `k = 7` or `k = 8`.
