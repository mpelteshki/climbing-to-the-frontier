# P2: uphill paths on hypercubes Q3–Q8

This package gives explicit increasing-label vertex lists and Lean-checked witness counts for C1–C4 of P2. The counts are 14, 34, 88, 204, 464, and 1040 for dimensions 3 through 8. Each `Qd.lean` proves that its list is a permutation of all vertices, its exact path count, and an existential witness attaining that count. Lean also proves the universal lower bounds for Q3 and Q4 in [C1Optimal.lean](c1/C1Optimal.lean), establishing their exact optima; for Q5–Q8 the witness theorems give **upper bounds** on U(Qd).

The separate [Established-results.md](Established-results.md) gives a self-contained mathematical lower bound for Q3 and Q4 and a reduction to the established hypercube decycling numbers for Q5–Q8. Combined with the certificates, it establishes the exact C1–C4 values mathematically. The Q5–Q8 reduction and literature theorem are **not formalized in Lean**, so their universal optimality proofs remain incomplete in Lean. C5 and C6 (Q9) are outside this package.

Under the P2 overview's stated criteria, C1–C4 are **Solved**: they provide the exact values and explicit full vertex lists in increasing label order, and the site marks these cells correct on the values alone. The grid status follows those task criteria; Lean proof coverage is reported separately. These materials have not been submitted to the platform.

The C1 proof combines [endpoint decomposition and path-count lower bounds](shared/LowerBound.lean#L463) with [regular-graph lower bounds](shared/RegularLower.lean#L405). `Hypercube.endCount_recurrence` connects enumerated endpoint counts to the recurrence, and `Hypercube.pathCount_eq_sum_endCount` sums them. `Hypercube.pathCount_lower3` and `Hypercube.pathCount_lower4` prove 14 and 34 are lower bounds for **every** valid labelling; [`q3_optimal` and `q4_optimal`](c1/C1Optimal.lean#L7) combine them with the explicit attaining labellings. The [C1 verification log](c1-optimality.log) records the packaged build, independent kernel replay, and `#print axioms` results; only `propext`, `Classical.choice`, and `Quot.sound` appear.

| Cell | Task status | Evidence and Lean coverage |
|---|---|---|
| C1 | **Solved** | [q3_optimal and q4_optimal](c1/C1Optimal.lean) prove attaining labellings and universal lower bounds for exact optima 14 and 34. [C1 verification](c1-optimality.log). |
| C2 | **Solved** | Value 88 and the full Q5 label list are supplied; [Q5](c2/Q5.lean) proves the witness count. Universal optimality is not yet proved in Lean. [Verification](verification.log). |
| C3 | **Solved** | Value 204 and the full Q6 label list are supplied; [Q6](c3/Q6.lean) proves the witness count. Universal optimality is not yet proved in Lean. [Verification](verification.log). |
| C4 | **Solved** | Values 464/1040 and full Q7/Q8 label lists are supplied; [Q7](c4/Q7.lean) and [Q8](c4/Q8.lean) prove the witness counts. Universal optimality is not yet proved in Lean. [Verification](verification.log). |
| C5 | Skipped | Bound-improvement research for Q9 was intentionally paused. |
| C6 | Skipped | The open exact Q9 problem was intentionally paused. |

Update this grid and the root `README.md` global coverage/evidence table together when task status or Lean proof coverage changes. Do not resume paused work.

`shared/Hypercube.lean` defines adjacency by bit flip, labellings as permutations, valleys, uphill paths, and exhaustive path enumeration. Its `mem_paths` theorem identifies enumeration with the stated semantics, and `paths_nodup` ensures one count per path. `shared/Fast.lean` proves the raw enumeration has no duplicates for a valid labelling, allowing the same exact count without expensive duplicate removal. Every witness theorem uses that equivalence and then kernel `decide`; none uses `native_decide`, `sorry`, or custom axioms. `#print axioms` in each file reports only `propext`, `Classical.choice`, and `Quot.sound`.

The lists in `Qd.lean` give vertices in increasing label order, with label 1 assigned to the first vertex. Each `qd-labels.txt` gives the same list as one width-d bitstring per line; `qd.json` gives decimal vertex IDs. The script in `shared/witnesses.py` documents the deterministic construction and independently counts paths by dynamic programming. Run `python3 shared/witnesses.py --check` to compare its generated sources and labels with all packaged files without modifying them.

To reproduce with Lean 4.34.1 and its bundled Std library, run `./verify.sh` from this directory. It builds C1 and its dependencies, runs `leanchecker C1Optimal`, audits proof axioms, then verifies the unchanged Q5–Q8 witnesses. The [C1 verification log](c1-optimality.log) captures the focused C1 replay; the earlier [witness verification log](verification.log) covers Q3–Q8. Q8 takes substantially longer than the earlier files. No external Lean packages are required. [MANIFEST.txt](MANIFEST.txt) lists exactly the files to publish; `.lake/` and the generated Lake manifest are excluded.

The reusable [path-count budget theorem](shared/DecyclingBridge.lean) now proves `P ≥ n + (d−1)|B|`, where B consists of vertices ending more than one uphill path. `pathCount_regular_budget` states the result for a distinct vertex ordering with degree d and d ≥ 1; its conclusion uses the original `pathCount`. The [verification record](decycling-budget-verification.log) includes independent kernel replay and the axiom audit. This does not yet prove the Q5 deletion bound |B| ≥ 14 or the remaining C2–C4 lower bounds.

## Method fit

Lean is useful here for the universal C1 lower bounds, the equivalence between path semantics and enumeration, and exact witness checks. Those proofs expose the assumptions and can be replayed independently; the largest published witness, Q8, took about 53 seconds to kernel-check in the recorded run.

Exhaustive Q5 decycling search is a less suitable first target for full formalization. A fast external search does not imply a cheap kernel reduction, and adding a native computation axiom would change this package's trust boundary. The useful next steps are a reusable mathematical reduction and a compact, independently replayable finite certificate. A line-by-line proof plus an exact checker can provide valuable evidence before its checker and execution are formalized. C2–C4 meet the task criteria, while their universal Lean optimality proofs remain incomplete. Open Q9 work remains paused.
