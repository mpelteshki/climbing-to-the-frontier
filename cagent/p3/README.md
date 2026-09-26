# P3: Bulgarian solitaire

[Problem overview](https://hackathon.bainsa.ai/p/p3) · [C1](https://hackathon.bainsa.ai/p/p3/c1) · [C2](https://hackathon.bainsa.ai/p/p3/c2) · [C3](https://hackathon.bainsa.ai/p/p3/c3) · [C4](https://hackathon.bainsa.ai/p/p3/c4) · [C5](https://hackathon.bainsa.ai/p/p3/c5) · [C6](https://hackathon.bainsa.ai/p/p3/c6)

This package proves exact maximum transient depths for **every card count from 1 through 23** in Lean 4.34.1. It also proves that every staircase is a fixed partition, and verifies convergence to the staircase and uniqueness of the cyclic partition for the six triangular card counts 1, 3, 6, 10, 15, and 21. These are finite results; no cell's full general statement is claimed solved.

| Cards `n` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Maximum depth | 0 | 0 | 2 | 2 | 3 | 6 | 4 | 5 | 7 | 12 | 8 | 8 | 9 | 14 | 20 | 15 | 12 | 13 | 16 | 23 | 30 | 24 | 18 |

Each theorem `maximumDepth_n` proves two statements: every decreasing positive partition of `n` enters some periodic orbit by the displayed depth, and an explicit partition first enters a periodic orbit at exactly that depth. “Depth” is the first periodic state, so it does not assume that the orbit is a fixed point. The state transition removes one card from every pile, discards empty piles, creates a pile whose size is the previous number of piles, and sorts the result. `Basic.lean` defines these terms and proves the general certificate logic. `Enumeration.lean` proves that its executable list contains every partition satisfying `IsPartition`, so the finite upper bounds are exhaustive. The `cbv` tactic produces computation proofs checked by Lean's kernel; `#print axioms` records the dependencies. No `sorry`, custom axiom, `native_decide`, or external solver is used.

Cell status: [C1](c1/README.md) has an all-`k` fixed-staircase theorem and finite convergence/uniqueness through `k=6`; [C2](c2/README.md) has six triangular instances; [C3](c3/README.md) has finite instances for ranks 4–6; [C4](c4/README.md) has three finite instances; [C5](c5/README.md) has six finite instances. [C6](c6/README.md) is paused and unattempted.

## Replay

From the repository root, run:

```sh
python3 cagent/p3/verify.py
```

The script uses the package's pinned [`lean-toolchain`](lean/lean-toolchain) and [`lakefile.toml`](lean/lakefile.toml), builds the imports, checks each theorem file with warnings treated as errors, checks its printed axioms against Lean's standard `propext`, `Classical.choice`, and `Quot.sound`, and writes source hashes, commands, outputs, and timings to [`evidence/verification.json`](evidence/verification.json). It needs an installed Lean toolchain through `lake`/`elan`, Python 3, and no third-party Python package. [`evidence/exploration.json`](evidence/exploration.json) is discovery data only; the Lean proofs do not trust it.

The Lean sources are under [`lean/ProofPursuit/P3/`](lean/ProofPursuit/P3/): `Basic.lean` for the transition and abstract lemmas, `Enumeration.lean` for partition completeness and sound certificate checks, `Staircase.lean` for all-`k` staircase properties, `Convergence.lean` for finite triangular convergence, `NegativeCheck.lean` for a wrong-depth rejection, and `N1.lean` through `N23.lean` for exact finite maxima.
