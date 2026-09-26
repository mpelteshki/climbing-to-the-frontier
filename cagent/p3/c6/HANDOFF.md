# P3 C6 handoff — residue \(r=3\) (Fable)

## Outcome

\(D_B(T_{k-1}+3)=(k-1)(k-5)\) for every \(k\ge 9\); exceptional values \(6,7,9,13,18,24\) for \(k=3,\dots,8\).

* \(k\ge 14\): written proof (`RESULT.md` Sections 4–5), reusing C1 (cycle classification), the C2 retreat / width-two lemmas and the C3 final-pattern dichotomy, all re-read and stress-tested independently (`check_prereqs.py`, \(n\le 40\), PASS). New: entry-state Lemma E, inverse-height Lemmas D (single dominant pile, \(h\le n-M+1\)) and D2 (two dominant piles, \(h\le\lfloor (n-M-M')/2\rfloor+2\)), rotation-exclusion Lemma R, and explicit inverse branches for the three cyclic entry states \(S_{21},S_3,S_2\).
* \(3\le k\le 14\): exhaustive backward layering, layer sizes summed against \(p(n)\) (`exhaustive_r3.py`), \(n\) up to \(94\) (92.7M partitions, 288 s). New finite values beyond Grok's \(n\le 50\): \(D_B(58)=60\), \(D_B(69)=77\), \(D_B(81)=96\), \(D_B(94)=117\).
* Lower bound: Griggs–Ho Theorem 4.5 case (1) family \((k-2,k-2,k-3,\dots,4,4,3,2,1)\), full modular trajectory written out and checked against the real move for \(k=9..300\).
* Codex C5 (\(r=2\)) proof audited by reading and by an independent numerical re-derivation (`audit_c5_r2.py`); no gap found. Astra's checker replayed read-only.

* Second session (`RESULT.md` §9): exhaustive \(D_B(n)=L(n)\) for **all \(n\le 70\)** plus \(81,82,94,95\); a certificate checker (`toolkit_general_r.py`) that mechanises the §5 argument and **proves 24 further exact values** for \(r=4..7\), \(70\le n\le 217\) (Theorem C; three overlap with enumeration and agree); two sharp conjectural inverse-height lemmas (D″: \(\mu_1\ge m+3\Rightarrow h\le n-\mu_1+1\); O: four ones \(\Rightarrow h\le n-m\)), tested on all partitions \(n\le 34\), with a proved reduction D″ ⇐ O + O3, and the demonstration that D″ alone lets the checker close \(r=4..8\) for every \(k\in[2r+5,40]\) in two minutes.

Not done: Lean; proofs of Lemmas O / O3 / D″; a uniform written treatment of type I sandwiches of width \(k-5\) for \(9\le k\le 13\) (covered by enumeration instead); anything for \(r\ge 4\) beyond the structural remark below.

## Files (all under `output/`)

| file | purpose |
|---|---|
| `RESULT.md` | statement, prerequisites audit, exhaustive table, lower bound, full upper-bound proof for \(k\ge14\), obstruction analysis, literature, replay |
| `code/bs_core.py` | independent core: `step`, exhaustive `predecessors`, direct cycle detection, boundary form, backward layering, inverse-tree height |
| `code/check_prereqs.py N` | stress test of C1/C2/C3 statements and the inverse rule over all partitions of \(n\le N\) |
| `code/exhaustive_r3.py KMIN KMAX` | exact \(D_B(T_{k-1}+3)\) with \(p(n)\) coverage assertion; writes `evidence/exhaustive-r3-k*.json` |
| `code/lower_family_r3.py KMIN KMAX` | Theorem A trajectory check |
| `code/entry_states_r3.py KMIN KMAX` | enumerates sandwich cases, forced entry states, \(\delta(S)\), exhaustive \(h(S)\) |
| `code/verify_claims_r3.py KMIN KMAX NMAX` | every symbolic predecessor/orbit/cyclicity claim of the proof for each \(k\); Lemma D/D2 tests on all partitions \(n\le\) NMAX |
| `code/audit_c5_r2.py KMAX` | independent check of reused \(r=2\) claims |
| `code/exhaustive_general.py N...` | exact \(D_B(n)\) for arbitrary \(n\) (used for all \(n\le 70\), 81, 82, 94, 95) |
| `code/toolkit_general_r.py R KMIN KMAX [dprime]` | certificate checker for residue \(r\) (§9.2); `dprime` adds conjectural Lemma D″ |
| `code/lower_family_general.py R KMIN KMAX` | Griggs–Ho family depths for residue \(r\) by direct iteration |
| `code/lemma_conjectures_test.py NMAX` | exhaustive tests of Lemmas D″, O, O3 and their sharpness |
| `code/replay.sh [full]` | runs everything fast (~3 min; `full` adds \(k=14\) enumeration and the 18-minute certificate sweep) |
| `evidence/*.json, *.log` | recorded outputs, including layer-size profiles and maximizer counts |

Replay: `cd output/code && sh replay.sh` (expects `ALL REPLAYS PASSED`). Python 3 standard library only; single process. Context hashes: `context/manifest.json` (source HEAD e45c2b71…).

## Where the difficulty was, for the general-residue task

1. **Sharp case.** At type II width \(L=k-1-r\) the retreat bound \(p\le(k-1)(L-1)\) equals \(F_r=(k-1)(k-2-r)\) exactly; the excess over the minimum card count is \(T_r\), shared by \(r+1\) free old piles of base \(k-1-r\); the Griggs–Ho witness enters its cycle through the cyclic entry state with excess vector \((r,\dots,1,0)\) (checked \(r=2,3\)). Cyclic entry states there are closed by retreat alone (\(d=p\)).
2. **Everything else** at \(r=3\) closed with margin: non-cyclic entry states with a dominant pile (Lemma D/D2, \(h\lesssim n-k+2\approx k^2/2\ll F\)); "flat" states excluded because a diagonal-\((k+1)\) cell survives \(k-2\) unsorted moves (Lemma R); or a forced inverse chain that exposes a \((k-1,k,k+1)\) or \((k-1,k,k,k+1)\) count pattern, giving \(p=O(k)\) via the width-two/retreat lemma. The cyclic entry states at wider widths (\(k-3,k-2\)) have inverse heights governed by the \((1^n)\) chain: \(h(S_{21})=n-k+1\) exactly, attained by \((1^n)\). This is consistent with the middle-residue piece of Conjecture 4.7 taking over when \(n-k+1>F_r\), i.e. \(r\ge\lfloor (k-1)/2\rfloor\) — a heuristic worth testing at \(r=4\), not a proof.
3. **Type I** is the only place where the argument depends on \(k\): the card budget excludes width \(k-5\) only for \(k\ge 14\) (generally width \(k-j\) survives while the deficit \(k-13,\ k-18,\dots\) is \(\le 0\)). For \(r=3\), \(k\le 13\) the surviving states are listed in `evidence/typeI-entry-states-k9-13.json`; those with six equal old piles have huge forward depth (\(\delta=49,65,83\) at \(k=11,12,13\)) so they are excluded, but no uniform argument for that was found. For larger \(r\) this type I window moves to larger \(k\) (deficit at width \(k-j\) is roughly \(k-3j-\dots\)); expect the same shape.
4. **The single missing lemma.** Every large-\(k\) failure of the checker is an inverse-height question for a cyclic entry state whose non-cyclic predecessor has a part \(\ge\) (number of parts)\(+3\). Lemma D″ (\(\mu_1\ge m+3\Rightarrow h(\mu)\le n-\mu_1+1\)) is exactly what is needed, is sharp, and reduces to the "four ones" Lemma O plus O3 (§9.3). Proving O is the highest-value open step: it would make the small-residue formula for each fixed \(r\) a finite, uniform-in-\(k\) case analysis. Attempts so far: induction tracking four equal piles (bound \(n-m-a+1\)) fails by one unit at steps with \(s=m-1\); forward card counting fails because \(c_t\le n-t+1\) is false on deep transients, so the argument must use the tall pile's late birth.
5. **Counts of entry states grow**: \(r=2\): 6, \(r=3\): 16 type II entry states at generic \(k\) across widths \(k-1-r,\dots,k-2,k\) (plus the finite type I states at small \(k\)). A general-\(r\) proof needs a uniform classification of excess vectors into (cyclic / dominant-pile / rotation-excluded / sandwich-exposed), which the \(r=3\) data suggests is possible but is not established.

## Caveats

* Finite computations are theorems about the listed \(n\) only; the exhaustive runs are exhaustive by construction (each partition appears in exactly one backward layer; sum checked against \(p(n)\)).
* Prerequisite audits are reading plus finite stress tests, not formal certification.
* No publication, submission, or messages to other workers; Grok/Codex sources unchanged.
