# P3 C1: staircase behavior

[Cell statement](https://hackathon.bainsa.ai/p/p3/c1) · [Package and replay instructions](../README.md)

`Staircase.lean` proves for every natural `k` that the staircase `(k, k-1, …, 1)` is a decreasing positive partition of `k(k+1)/2` and is fixed by one Bulgarian-solitaire step. `Convergence.lean` additionally proves, by exhaustive kernel-checked computation, that **every** partition reaches this staircase within `k(k-1)` steps for `k=1,2,3,4,5,6`. For these six sizes it also proves that any cyclic partition equals the staircase, hence the staircase is the unique fixed point.

General results now verified in Lean:

- [`Boundary.lean`](../lean/ProofPursuit/P3/Boundary.lean), `boundary_orbit`: for every binary word of length `k+1`, the piles `(k+bit₀, k−1+bit₁, …, bitₖ)`, with zero removed, form a partition of `k(k+1)/2 + bitCount`. Each step rotates the final bit to the front, and `k+1` steps return to the original partition. This proves the constructive direction of the cycle classification. It does not claim the least period is `k+1`.
- [`Eventual.lean`](../lean/ProofPursuit/P3/Eventual.lean), `eventually_cyclic` and `depth_exists`: every partition of every `n` reaches a cycle before the partition enumeration is exhausted. This pigeonhole bound is not a sharp transient bound.
- [`Energy.lean`](../lean/ProofPursuit/P3/Energy.lean), `step_energy_le`: the sum of diagonal indices of cards never increases. `cyclic_energy_constant` proves no loss on a periodic orbit. `cyclic_head_bound` proves the largest pile of any nonempty cyclic partition is at most one plus its pile count.

- [`Classification.lean`](../lean/ProofPursuit/P3/Classification.lean), `cyclic_iff_boundary`: a partition is cyclic **if and only if** it is a staircase with a binary boundary. The converse is proved through energy constancy, diagonal rotation, simultaneous alignment on adjacent diagonals, and reconstruction from the resulting height bounds.
- [`Necklace.lean`](../lean/ProofPursuit/P3/Necklace.lean), `boundary_same_cycle_iff`: two equal-width binary words describe the same solitaire cycle exactly when one is a rotation of the other. `boundary_injective_of_length` proves the encoding is injective at fixed width. This is a cycle correspondence, not yet the numerical necklace-count formula.

- [`TriangularGeneral.lean`](../lean/ProofPursuit/P3/TriangularGeneral.lean), `triangular_cyclic_unique` and `triangular_eventually_staircase`: for every natural `k`, the staircase is the unique cyclic partition of `k(k+1)/2`, and every partition of that size eventually reaches it. This includes `k=0`; no uniform sharp time bound is claimed here.

The binary-boundary characterization and diagonal-energy approach are classical; see [Griggs and Ho, *The Cycling of Partitions and Compositions under Repeated Shifts*](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf). These files supply explicit checked proofs of the stated lemmas, not new mathematical claims.

- [`RankedClassification.lean`](../lean/ProofPursuit/P3/RankedClassification.lean), `ranked_cyclic_iff_boundary`: when `Tₖ₋₁ < n ≤ Tₖ`, cyclic partitions are exactly boundary words of length `k` and weight `n−Tₖ₋₁`, including the triangular upper endpoint.

The [complete written C1 proof](written-proof.md) gives the general numerical cycle-count formula by explicit double counting and completes the mathematical argument. An [independent checker](check_cycles.py) reproduces actual cycle counts and boundary orbits for n=1–40; see [finite replay evidence](../evidence/cycle-counts.json). The remaining assurance gap is **formalizing the counting argument in Lean**. **C1 is Solved under the task criteria**; complete mathematical proof and complete Lean formalization are distinct claims. [Replay evidence](../evidence/verification.json) records exact source hashes and axiom checks.
