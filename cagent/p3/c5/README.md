# P3 C5: two above a triangular number

[Cell statement](https://hackathon.bainsa.ai/p/p3/c5) · [Consolidated judge write-up](../writeup.md)

**Solved — complete written proof; Lean partial.** For $k\ge7$,

$$
D_B(T_{k-1}+2)=(k-1)(k-4).
$$

The [general upper bound](upper-bound-proof.md) closes every final-pattern case using pile lifetimes, exact card counts, and inverse-tree arguments. The [explicit attaining family](lower-bound-proof.md) proves the matching lower bound. The upper proof explains both the strict gap from C3 and the additional inverse argument needed to close it. The general result is not fully formalized in Lean.

## Exceptional values and witnesses

| $k$ | Cards | Maximum depth | An attaining partition | Lean certificate |
| --- | --- | --- | --- | --- |
| 2 | 3 | 2 | $(1,1,1)$ | [N3](../lean/ProofPursuit/P3/N3.lean) |
| 3 | 5 | 3 | $(1,1,1,1,1)$ | [N5](../lean/ProofPursuit/P3/N5.lean) |
| 4 | 8 | 5 | Eight piles of one | [N8](../lean/ProofPursuit/P3/N8.lean) |
| 5 | 12 | 8 | $(3,3,2,2,1,1)$ | [N12](../lean/ProofPursuit/P3/N12.lean) |
| 6 | 17 | 12 | Seventeen piles of one | [N17](../lean/ProofPursuit/P3/N17.lean) |

Each Lean theorem proves its upper bound over every partition and verifies its displayed attaining witness. The same package also proves $D_B(23)=18$ at $k=7$.

## Independent finite replay

Run `python3 cagent/p3/c5/check.py` from the repository root. [The checker](check.py) detects cycles directly, without using the binary-boundary classification, and exhausts all partitions at $k=2$ through $10$. [Recorded evidence](finite-check.json): **158,034 partitions**, maxima **2,3,5,8,12,18,28,40,54**, **0.335 seconds**. This finite replay is a cross-check of the written general proof, not its replacement.
