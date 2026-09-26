# P4: disjoint congruence classes

This standalone Lean 4 package proves the P4 statement for every number of classes `k` from 2 through 9. The current range theorem is `ProofPursuit.P4.ThroughNine.solution`:

```lean
∀ k : Nat, 2 ≤ k → k ≤ 9 → ProofPursuit.P4.Statement k
```

`Statement k` says that if `k` integer congruence classes with **positive natural-number moduli** are pairwise disjoint as sets of integers, then two of their moduli have gcd at least `k`. The moduli may repeat. `DisjointClasses` asserts actual absence of a common integer; it is not a Chinese remainder theorem assumption. The shared `Basic.lean` proves the needed intersection direction from Bézout's identity.

The package uses Lean `v4.34.1` and its bundled `Std` library, with no external dependencies. From this directory:

```sh
cd lean
lake build ProofPursuit.P4.ThroughNine
lake env leanchecker ProofPursuit.P4.ThroughNine
```

The `leanchecker` command succeeds with exit status 0 and no output. To inspect theorem dependencies directly:

```sh
lake env lean ProofPursuit/P4/C3.lean
```

`C3.lean` prints the axioms of the final theorem; `Progress.lean` prints those of the combined theorem and its components. The audit found only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms or `sorry` declarations. See [verification.md](verification.md) for the recorded commands and results.

| Cell | Certified theorem | Status |
| --- | --- | --- |
| [C1](c1/README.md) | `Statement 3` | Complete |
| [C2](c2/README.md) | `Statement 4` | Complete |
| [C3](c3/README.md) | `Statement k` for `2 ≤ k ≤ 8` | Complete |
| [C4](c4/README.md) | `Statement 9`; finite-reduction and density lemmas; exact k=13 obstruction audit | Not solved |
| C5 | — | Not solved |
| C6 | — | Skipped; open-conjecture work paused |

The full C3 theorem is in [C3.lean](lean/ProofPursuit/P4/C3.lean). The package contains individual proofs through `Statement 7`. `Eight.step` proves `Statement 8` from `Statement 7`, and `Progress.solution` supplies that premise using `Seven.solution`. `ThroughNine.solution` now extends the unconditional range through 9. No theorem asserting `Statement k` for `k > 9` is claimed. The k=13 results concern one explicit modulus list, not all configurations of thirteen classes.

New C4 work is documented in [c4/README.md](c4/README.md). Every subset of the displayed thirteen-modulus list passes the canonical density test, but the list has no disjoint residue assignment. Lean checks explicit assignments for every submultiset of size at most six, proving that the exhibited seven-class obstruction has minimum cardinality within this list. The generic finite-search completeness theorem is separate from a completed exhaustive search for k=10–12.
