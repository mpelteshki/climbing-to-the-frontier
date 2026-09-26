# P3 C2: triangular maximum depths

[Cell statement](https://hackathon.bainsa.ai/p/p3/c2) · [Package and replay instructions](../README.md)

Theorems `maximumDepth_1`, `_3`, `_6`, `_10`, `_15`, and `_21` prove the exact maximum first-periodic depths for triangular card counts `k(k+1)/2` with `k=1,…,6`:

| `k` | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- | --- |
| Cards | 1 | 3 | 6 | 10 | 15 | 21 |
| Exact maximum depth | 0 | 2 | 6 | 12 | 20 | 30 |

These Lean instances match `k(k-1)`. The all-`k` formula is now proved in writing below; its complete Lean formalization remains unfinished.

## General lower bound

The [written extremal construction](lower-bound-proof.md) proves first cyclic depth exactly `k(k−1)` for its explicit family for every `k≥1`. It uses the general triangular uniqueness theorem to rule out earlier cycles. **C2 is Solved under the task criteria**: the [complete written upper bound](upper-bound-proof.md) handles every starting partition and matches this witness. This lower-bound argument is written mathematics, not a general Lean theorem.

## Checked arithmetic for the upper-bound strategy

[`sandwich_start_bound`](../lean/ProofPursuit/P3/C2SandwichBound.lean) proves an abstract descent bound: a valid pattern with start `p`, level `x`, and width `w` satisfies `p ≤ x*(w−1)` when every pattern has width at least two and either starts by `x` or retreats to a smaller-width pattern with level at most `x` and start at least `p−x`. The proof uses strong induction and is kernel checked. The [written upper-bound proof](upper-bound-proof.md) establishes these retreat hypotheses for Bulgarian-solitaire pile counts. They remain unformalized in Lean; this abstract theorem alone is **not** a general convergence bound.
