# P2: uphill paths on hypercubes Q3–Q8

This package gives explicit increasing-label vertex lists and Lean-checked witness counts for C1–C4 of P2. The counts are 14, 34, 88, 204, 464, and 1040 for dimensions 3 through 8. Each `Qd.lean` proves that its list is a permutation of all vertices, its exact path count, and an existential witness attaining that count. Therefore Lean proves the corresponding **upper bounds** on U(Qd).

The separate [Established-results.md](Established-results.md) gives a self-contained mathematical lower bound for Q3 and Q4 and a reduction to the established hypercube decycling numbers for Q5–Q8. Combined with these certificates it establishes the exact C1–C4 values mathematically. The reduction and literature theorem are **not formalized in Lean**; no Lean theorem here asserts global optimality. C5 and C6 (Q9) are outside this package.

| Cell | Status | Lean evidence and remaining work |
|---|---|---|
| C1 | Not solved | [Q3](c1/Q3.lean) and [Q4](c1/Q4.lean) prove witness upper bounds 14 and 34; optimality is unformalized. [Verification](verification.log). |
| C2 | Not solved | [Q5](c2/Q5.lean) proves witness upper bound 88; optimality is unformalized. [Verification](verification.log). |
| C3 | Not solved | [Q6](c3/Q6.lean) proves witness upper bound 204; optimality is unformalized. [Verification](verification.log). |
| C4 | Not solved | [Q7](c4/Q7.lean) and [Q8](c4/Q8.lean) prove witness upper bounds 464 and 1040; optimality is unformalized. [Verification](verification.log). |
| C5 | Skipped | Bound-improvement research for Q9 was intentionally paused. |
| C6 | Skipped | The open exact Q9 problem was intentionally paused. |

Only a full-cell Lean proof warrants changing a status to Solved. Update this grid, the `cagent/README.md` grid and verified progress, and the supporting evidence together through the git integrator. Do not resume paused work.

`shared/Hypercube.lean` defines adjacency by bit flip, labellings as permutations, valleys, uphill paths, and exhaustive path enumeration. Its `mem_paths` theorem identifies enumeration with the stated semantics, and `paths_nodup` ensures one count per path. `shared/Fast.lean` proves the raw enumeration has no duplicates for a valid labelling, allowing the same exact count without expensive duplicate removal. Every witness theorem uses that equivalence and then kernel `decide`; none uses `native_decide`, `sorry`, or custom axioms. `#print axioms` in each file reports only `propext`, `Classical.choice`, and `Quot.sound`.

The lists in `Qd.lean` give vertices in increasing label order, with label 1 assigned to the first vertex. Each `qd-labels.txt` gives the same list as one width-d bitstring per line; `qd.json` gives decimal vertex IDs. The script in `shared/witnesses.py` documents the deterministic construction and independently counts paths by dynamic programming. Run `python3 shared/witnesses.py --check` to compare its generated sources and labels with all packaged files without modifying them.

To reproduce with Lean 4.34.1 and its bundled Std library, run `./verify.sh` from this directory. It builds the shared files and verifies Q3 through Q8 sequentially. A captured run is in [verification.log](verification.log). Q8 takes substantially longer than the earlier files. No external Lean packages are required. [MANIFEST.txt](MANIFEST.txt) lists exactly the files to publish; `.lake/` and the generated Lake manifest are excluded.
