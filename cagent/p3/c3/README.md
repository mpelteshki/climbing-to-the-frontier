# P3 C3: nontriangular sizes

[Cell statement](https://hackathon.bainsa.ai/p/p3/c3) · [Package and replay instructions](../README.md)

The `N7`, `N8`, `N9`, `N11`–`N14`, and `N16`–`N20` Lean files give exact maximum depths for every nontriangular card count in the finite rank-4-through-rank-6 range:

| Cards | 7 | 8 | 9 | 11 | 12 | 13 | 14 | 16 | 17 | 18 | 19 | 20 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Exact maximum depth | 4 | 5 | 7 | 8 | 8 | 9 | 14 | 15 | 12 | 13 | 16 | 23 |

**C3 is Solved under the task criteria.** The [complete written proof](written-proof.md) establishes the general bound, equality at `T_k−1`, and an explicit inverse construction generating every maximizing partition. These general arguments are not yet Lean theorems. Run `python3 cagent/p3/c3/check.py` for the [independent finite replay](finite-check.json), comparing inverse-generated sets with exhaustive forward depths for k=4–7.
