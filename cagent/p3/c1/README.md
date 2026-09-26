# P3 C1: staircase behavior

[Cell statement](https://hackathon.bainsa.ai/p/p3/c1) · [Package and replay instructions](../README.md)

`Staircase.lean` proves for every natural `k` that the staircase `(k, k-1, …, 1)` is a decreasing positive partition of `k(k+1)/2` and is fixed by one Bulgarian-solitaire step. `Convergence.lean` additionally proves, by exhaustive kernel-checked computation, that **every** partition reaches this staircase within `k(k-1)` steps for `k=1,2,3,4,5,6`. For these six sizes it also proves that any cyclic partition equals the staircase, hence the staircase is the unique fixed point.

This does not establish convergence or uniqueness for arbitrary `k`. The general non-triangular cycle classification and cycle-count formula are not formalized. C1 remains partial.
