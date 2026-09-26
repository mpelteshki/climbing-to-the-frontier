# P2: uphill paths on hypercubes Q3–Q8

The [standalone judge writeup](writeup.md) contains the complete C1–C4 arguments and all six binary vertex lists in submission order.

This package gives explicit increasing-label vertex lists and Lean-checked witness counts for C1–C4 of P2. The counts are 14, 34, 88, 204, 464, and 1040 for dimensions 3 through 8. Each `Qd.lean` proves that its list is a permutation of all vertices, its exact path count, and an existential witness attaining that count. Lean also proves the universal lower bounds for Q3 and Q4 in [C1Optimal.lean](c1/C1Optimal.lean), establishing their exact optima; for Q5–Q8 the witness theorems give **upper bounds** on U(Qd).

The separate [Established-results.md](Established-results.md) gives written lower bounds, an independently replayable finite Q5 decycling check, and face doubling for Q6–Q8. Together with the witnesses, these support the exact C1–C4 values mathematically. Universal optimality for C2–C4 remains incomplete **in Lean**. C5 bound-improvement work is active; C6 remains paused.

Under the [P2 task](Task.md)'s stated criteria, C1–C4 are **Solved**: each has the required value and full vertex list in increasing label order, and the site marks these cells correct on the values alone. The grid status follows those criteria; Lean proof coverage is reported separately. These materials have not been submitted to the platform.

The C1 proof combines [endpoint decomposition and path-count lower bounds](shared/LowerBound.lean#L463) with [regular-graph lower bounds](shared/RegularLower.lean#L405). `Hypercube.endCount_recurrence` connects enumerated endpoint counts to the recurrence, and `Hypercube.pathCount_eq_sum_endCount` sums them. `Hypercube.pathCount_lower3` and `Hypercube.pathCount_lower4` prove 14 and 34 are lower bounds for **every** valid labelling; [`q3_optimal` and `q4_optimal`](c1/C1Optimal.lean#L7) combine them with the explicit attaining labellings. The [C1 verification log](c1-optimality.log) records the packaged build, independent kernel replay, and `#print axioms` results; only `propext`, `Classical.choice`, and `Quot.sound` appear.

| Cell | Task status | Value and Lean coverage |
|---|---|---|
| C1 | **Solved** | [q3_optimal and q4_optimal](c1/C1Optimal.lean) prove attaining labellings and universal lower bounds for exact optima 14 and 34. [C1 verification](c1-optimality.log). |
| C2 | **Solved** | Value 88 and the full Q5 label list are supplied. [Q5](c2/Q5.lean) proves the witness count; [incremental lemmas](shared/DecyclingBridge.lean) and [exact external replays](c2/C2-notes.md) support the lower bound, which remains conditional in Lean. |
| C3 | **Solved** | Value 204 and the full Q6 label list are supplied. [Q6](c3/Q6.lean) proves the witness count; universal optimality remains incomplete in Lean. |
| C4 | **Solved** | Values 464/1040 and full Q7/Q8 label lists are supplied. [Q7](c4/Q7.lean) and [Q8](c4/Q8.lean) prove the witness counts; universal optimality remains incomplete in Lean. |
| [C5](c5/README.md) | Not solved | Active bound-improvement research for Q9; no verified improvement yet. |
| C6 | Skipped | The open exact Q9 problem was intentionally paused. |

Update this grid and the root `README.md` global coverage/evidence table together when task status or Lean proof coverage changes. Do not resume paused work.

`shared/Hypercube.lean` defines adjacency by bit flip, labellings as permutations, valleys, uphill paths, and exhaustive path enumeration. Its `mem_paths` theorem identifies enumeration with the stated semantics, and `paths_nodup` ensures one count per path. `shared/Fast.lean` proves the raw enumeration has no duplicates for a valid labelling, allowing the same exact count without expensive duplicate removal. Every witness theorem uses that equivalence and then kernel `decide`; none uses `native_decide`, `sorry`, or custom axioms. `#print axioms` in each file reports only `propext`, `Classical.choice`, and `Quot.sound`.

The lists in `Qd.lean` give vertices in increasing label order, with label 1 assigned to the first vertex. Each `qd-labels.txt` gives the same list as one width-d bitstring per line; `qd.json` gives decimal vertex IDs. The script in `shared/witnesses.py` documents the deterministic construction and independently counts paths by dynamic programming. Run `python3 shared/witnesses.py --check` to compare its generated sources and labels with all packaged files without modifying them.

To reproduce with Lean 4.34.1 and its bundled Std library, run `./verify.sh` from this directory. It builds C1 and the incremental Q5 modules, runs `leanchecker` and axiom audits, replays both Q5 checkers, then verifies Q5–Q8 witnesses. The [C1 log](c1-optimality.log), [incremental Q5 Lean log](decycling-increment-verification.log), [Q5 replay notes](c2/C2-notes.md), and original [Q3–Q8 witness log](verification.log) record the focused checks already run. Q8 takes substantially longer than the earlier files and was not rerun for this increment. No external Lean packages are required. [MANIFEST.txt](MANIFEST.txt) lists exactly the files to publish; `.lake/` and the generated Lake manifest are excluded.

The reusable [path-count budget theorem](shared/DecyclingBridge.lean) proves `P ≥ n + (d−1)|B|`, where B consists of vertices ending more than one uphill path. The same module checks Q5's degree and edge count, its short-cycle hitting condition, and a **conditional** `pathCount_lower5_of_search_and_edges`. That final theorem requires `Decycling5.search 13 [] = true` and `Decycling5.internalEdges B ≤ edgeCount 5 B`; neither premise is proved in Lean. [Decycling5.lean](shared/Decycling5.lean) proves the cycle inventory's validity and search soundness. The [incremental log](decycling-increment-verification.log) records both modules' builds, independent kernel replay, and standard-axiom audits.

## Method fit

Lean is useful here for the universal C1 lower bounds, the equivalence between path semantics and enumeration, and exact witness checks. Those proofs expose the assumptions and can be replayed independently; the largest published witness, Q8, took about 53 seconds to kernel-check in the recorded run.

The [Q5 branch replay](c2/decycling5_replay.py) and independent [parity/forest replay](c2/decycling5_parity_replay.py) each take well under a second here. They give checkable finite evidence using different search partitions; their computations have not been kernel checked. Lean verifies the mathematical bridge and the soundness of the branch rule, but a single kernel reduction of the root search was too costly for this package. C2–C4 meet the task criteria while their universal Lean optimality proofs remain incomplete. Q9 C5 bound-improvement work resumed on explicit user request; exact-value C6 remains paused.
