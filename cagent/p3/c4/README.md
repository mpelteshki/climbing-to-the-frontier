# P3 C4: one above a triangular number

[Cell statement](https://hackathon.bainsa.ai/p/p3/c4) · [Complete written proof](written-proof.md)

**Solved under the task criteria.** For every $k\ge5$,

$$
D_B(T_{k-1}+1)=(k-1)(k-3).
$$

The proof supplies a uniform upper bound and the explicit family $(k-2,k-2,k-3,\ldots,2,2,1)$ attaining it. Two independent mathematical reviews checked its pile-lifetime cases and rotation argument.

Lean proves the finite cases $k=5,6,7$ in `N11`, `N16`, and `N22`, and the shared abstract descent arithmetic. The general C4 proof is written mathematics, not a full Lean formalization.

Run `python3 cagent/p3/c4/check.py` for an independent exhaustive check through $k=9$. [Finite evidence](finite-check.json) includes counts, witnesses, and exact depths; it does not replace the all-$k$ proof.
