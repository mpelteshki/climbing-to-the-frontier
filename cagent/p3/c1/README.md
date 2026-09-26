# P3 C1: staircase behavior

[Cell statement](https://hackathon.bainsa.ai/p/p3/c1) · [Package and replay instructions](../README.md)

`Staircase.lean` proves for every natural `k` that the staircase `(k, k-1, …, 1)` is a decreasing positive partition of `k(k+1)/2` and is fixed by one Bulgarian-solitaire step. `Convergence.lean` additionally proves, by exhaustive kernel-checked computation, that **every** partition reaches this staircase within `k(k-1)` steps for `k=1,2,3,4,5,6`. For these six sizes it also proves that any cyclic partition equals the staircase, hence the staircase is the unique fixed point.

General results now verified in Lean:

- [`Boundary.lean`](../lean/ProofPursuit/P3/Boundary.lean), `boundary_orbit`: for every binary word of length `k+1`, the piles `(k+bit₀, k−1+bit₁, …, bitₖ)`, with zero removed, form a partition of `k(k+1)/2 + bitCount`. Each step rotates the final bit to the front, and `k+1` steps return to the original partition. This proves the constructive direction of the proposed cycle classification. It does not claim the least period is `k+1`.
- [`Eventual.lean`](../lean/ProofPursuit/P3/Eventual.lean), `eventually_cyclic` and `depth_exists`: every partition of every `n` reaches a cycle before the partition enumeration is exhausted. This pigeonhole bound is not a sharp transient bound.
- [`Energy.lean`](../lean/ProofPursuit/P3/Energy.lean), `step_energy_le`: the sum of diagonal indices of cards never increases. `cyclic_energy_constant` proves no loss on a periodic orbit. `cyclic_head_bound` proves the largest pile of any nonempty cyclic partition is at most one plus its pile count.

The binary-boundary characterization and diagonal-energy approach are classical; see [Griggs and Ho, *The Cycling of Partitions and Compositions under Repeated Shifts*](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf). These files supply explicit checked proofs of the stated lemmas, not new mathematical claims.

Still missing: the converse that every cycle is a binary boundary, the general cycle-count formula, and triangular convergence/uniqueness for arbitrary `k`. C1 remains **Not solved**. [Replay evidence](../evidence/verification.json) records exact source hashes and axiom checks.
