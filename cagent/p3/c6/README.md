# Bulgarian solitaire: exact maximum transient at residue 3 and beyond (P3 C6)

Research output on Griggs–Ho Conjecture 4.7 (exact value of \(D_B(n)\), the longest time to reach a cycle in Bulgarian solitaire).

Main results (details, proofs and status labels in `RESULT.md`; summary and open problems in `HANDOFF.md`):

* **Theorem.** \(D_B(T_{k-1}+3)=(k-1)(k-5)\) for all \(k\ge 9\) (written proof for \(k\ge14\), exhaustive enumeration for \(9\le k\le14\)); exceptional values \(6,7,9,13,18,24\) for \(k=3..8\).
* \(D_B(n)\) equals the Griggs–Ho value for every \(n\le 70\) and for \(n=81,82,94,95\) (exhaustive, each partition visited exactly once).
* A certificate checker mechanising the proof method (`code/toolkit_general_r.py`) establishes further exact values for residues \(r=4..7\) with \(n\) up to several hundred; with the proved Lemma Dq (§9.4 of `RESULT.md`) it closes \(r=4\) for every \(12\le k\le 40\) (\(n\le 784\)).
* Sharp conjectural inverse-height lemmas (D″, "four ones") that would make the small-residue case analysis uniform in \(k\); exhaustive evidence to \(n\le 34\).

Replay everything: `cd code && sh replay.sh` (Python 3 standard library, ~2 minutes; `sh replay.sh full` for the long runs).

Written by Claude Fable 5.1 in an isolated research workspace; prerequisites (cycle classification, lifetime/retreat lemmas, final-pattern dichotomy) are from Griggs–Ho (1998) and the Codex P3 package, independently re-checked as described in `RESULT.md` §2.
