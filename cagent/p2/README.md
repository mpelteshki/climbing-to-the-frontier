# P2: uphill paths on hypercubes Q3–Q8

This package gives explicit increasing-label vertex lists and Lean-checked witness counts for C1–C4 of P2. The counts are 14, 34, 88, 204, 464, and 1040 for dimensions 3 through 8. Each `Qd.lean` proves that its list is a permutation of all vertices, its exact path count, and an existential witness attaining that count. Lean also proves the universal lower bounds for Q3 and Q4 in [C1Optimal.lean](c1/C1Optimal.lean), establishing their exact optima; for Q5–Q8 the witness theorems give **upper bounds** on U(Qd).

The separate [Established-results.md](Established-results.md) gives a self-contained mathematical lower bound for Q3 and Q4 and a reduction to the established hypercube decycling numbers for Q5–Q8. Combined with the certificates, it establishes the exact C1–C4 values mathematically. The Q5–Q8 reduction and literature theorem are **not formalized in Lean**, so global optimality for C2–C4 remains open in this package. C5 and C6 (Q9) are outside this package.

Under the P2 overview's stated submission criteria, C1–C4 materials are ready: they provide the exact values and explicit full vertex lists in increasing label order. The status grid below tracks a stricter milestone—a full Lean proof of each cell's optimality. C1 now meets that milestone; C2–C4 remain **Not solved** there. These materials have not been submitted to the platform.

The C1 proof combines [endpoint decomposition and path-count lower bounds](shared/LowerBound.lean#L463) with [regular-graph lower bounds](shared/RegularLower.lean#L405). `Hypercube.endCount_recurrence` connects enumerated endpoint counts to the recurrence, and `Hypercube.pathCount_eq_sum_endCount` sums them. `Hypercube.pathCount_lower3` and `Hypercube.pathCount_lower4` prove 14 and 34 are lower bounds for **every** valid labelling; [`q3_optimal` and `q4_optimal`](c1/C1Optimal.lean#L7) combine them with the explicit attaining labellings. The [C1 verification log](c1-optimality.log) records the packaged build, independent kernel replay, and `#print axioms` results; only `propext`, `Classical.choice`, and `Quot.sound` appear.

| Cell | Status | Lean evidence and remaining work |
|---|---|---|
| C1 | **Solved** | [q3_optimal and q4_optimal](c1/C1Optimal.lean) prove attaining labellings and universal lower bounds for exact optima 14 and 34. [C1 verification](c1-optimality.log). |
| C2 | Not solved | [Q5](c2/Q5.lean) proves witness upper bound 88; optimality is unformalized. [Verification](verification.log). |
| C3 | Not solved | [Q6](c3/Q6.lean) proves witness upper bound 204; optimality is unformalized. [Verification](verification.log). |
| C4 | Not solved | [Q7](c4/Q7.lean) and [Q8](c4/Q8.lean) prove witness upper bounds 464 and 1040; optimality is unformalized. [Verification](verification.log). |
| C5 | Skipped | Bound-improvement research for Q9 was intentionally paused. |
| C6 | Skipped | The open exact Q9 problem was intentionally paused. |

Only a full-cell Lean proof warrants changing a status to Solved. Update this grid, the root `README.md` global coverage/evidence table, and the supporting evidence together through the git integrator. Do not resume paused work.

`shared/Hypercube.lean` defines adjacency by bit flip, labellings as permutations, valleys, uphill paths, and exhaustive path enumeration. Its `mem_paths` theorem identifies enumeration with the stated semantics, and `paths_nodup` ensures one count per path. `shared/Fast.lean` proves the raw enumeration has no duplicates for a valid labelling, allowing the same exact count without expensive duplicate removal. Every witness theorem uses that equivalence and then kernel `decide`; none uses `native_decide`, `sorry`, or custom axioms. `#print axioms` in each file reports only `propext`, `Classical.choice`, and `Quot.sound`.

The lists in `Qd.lean` give vertices in increasing label order, with label 1 assigned to the first vertex. Each `qd-labels.txt` gives the same list as one width-d bitstring per line; `qd.json` gives decimal vertex IDs. The script in `shared/witnesses.py` documents the deterministic construction and independently counts paths by dynamic programming. Run `python3 shared/witnesses.py --check` to compare its generated sources and labels with all packaged files without modifying them.

To reproduce with Lean 4.34.1 and its bundled Std library, run `./verify.sh` from this directory. It builds C1 and its dependencies, runs `leanchecker C1Optimal`, audits proof axioms, then verifies the unchanged Q5–Q8 witnesses. The [C1 verification log](c1-optimality.log) captures the focused C1 replay; the earlier [witness verification log](verification.log) covers Q3–Q8. Q8 takes substantially longer than the earlier files. No external Lean packages are required. [MANIFEST.txt](MANIFEST.txt) lists exactly the files to publish; `.lake/` and the generated Lake manifest are excluded.
