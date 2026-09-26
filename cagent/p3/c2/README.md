# P3 C2: triangular maximum depths

[Cell statement](https://hackathon.bainsa.ai/p/p3/c2) · [Package and replay instructions](../README.md)

Theorems `maximumDepth_1`, `_3`, `_6`, `_10`, `_15`, and `_21` prove the exact maximum first-periodic depths for triangular card counts `k(k+1)/2` with `k=1,…,6`:

| `k` | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- | --- |
| Cards | 1 | 3 | 6 | 10 | 15 | 21 |
| Exact maximum depth | 0 | 2 | 6 | 12 | 20 | 30 |

These instances match `k(k-1)`, but no all-`k` maximum-depth formula is proved. C2 remains partial.

## General lower bound

The [written extremal construction](lower-bound-proof.md) proves first cyclic depth exactly `k(k−1)` for its explicit family for every `k≥1`. It uses the general triangular uniqueness theorem to rule out earlier cycles. C2 remains **Not solved**: the upper bound for arbitrary starting partitions is still missing. This lower-bound argument is written mathematics, not a general Lean theorem.
