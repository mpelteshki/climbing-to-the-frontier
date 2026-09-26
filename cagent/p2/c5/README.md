# P2 C5 — Improve the Q9 bounds

**Solved mathematically: U(Q9) ≥ 2369.** Organizer acceptance is recorded separately in [the submission inventory](../../../docs/latex/SUBMISSIONS.md).

The [complete judge-ready proof](submission.md) excludes every labelling with at most 2368 uphill paths. It includes every finite certificate inline, without requiring hosted links, the unpublished organizer proof, or an external solver. A self-contained character argument proves A(9,4)≤20; local forest constraints and path-count budgets reduce the remaining cases to exact integer inventories. Harper’s classical vertex-isoperimetric theorem is stated and cited explicitly.

Four standard-library Python blocks reproduce the Harper table, monochromatic-sink exclusion, small mixed cases, and the final mixed-core inventory. The last inventory checks 1,110,562 degree multisets, leaves 134 after coarse filters, 20 after the triple-neighbour restriction, and zero after the incoming-core cost bound. Independent replays and exact source hashes appear in [evidence](evidence/). The proof has received independent mathematical review; it is not a full Lean formalization.

[PDF](../../../docs/latex/cells/p2-c5.pdf) · [editable LaTeX](../../../docs/latex/cells/p2-c5.tex)

Run `python3 cagent/p2/c5/verify.py` from the repository root, or run the four Python blocks separately as instructed in the proof. Their combined measured runtime is below one second in the recorded environment. C6 asks for the exact value and remains outside this result: the verified bounds are now 2369 ≤ U(Q9) ≤ 2400.
