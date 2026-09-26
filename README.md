# Climbing to the Frontier

A hackathon research workspace for automated mathematical discovery: explore conjectures, search for counterexamples, improve constructions, and produce independently checkable proofs.

## Proof progress

**18 solved · 1 not solved · 5 skipped.** This is the authoritative progress overview. “Solved” means the **entire cell meets its stated hackathon requirements**, supported by a complete written proof, a checkable computational certificate, or the exact values and constructions that the cell requests. Lean coverage is reported separately. “Not solved” includes partial arguments and finite cases that do not meet the full task. “Skipped” means intentionally paused; it does not mean impossible. No answers have been submitted to the hackathon platform.

The table records **published, verified work**, not unfinished local experiments. Proof links include the exact statements and limitations. Written arguments are identified separately from Lean proofs.

| Problem / cell | Status | Published result | What remains for the full cell |
| --- | --- | --- | --- |
| **P1 · Angles** — [C1](cagent/p1/c1/README.md) | **Solved** | [Complete written proof for all N](cagent/p1/written-proofs.md); Lean covers N=2,3,4. | None for the task; all-N Lean formalization remains incomplete. |
| P1 — [C2](cagent/p1/c2/README.md) | **Solved** | [Complete written proof for every m≥2](cagent/p1/written-proofs.md); Lean covers m=2,3. | None for the task; general Lean formalization remains incomplete. |
| P1 — [C3](cagent/p1/c3/README.md) | **Solved** | [Complete written proof](cagent/p1/c4/proof.md): d+1-line bound in every dimension d≥1. Lean covers d=1,2. | None for the task; general Lean formalization remains incomplete. |
| P1 — [C4](cagent/p1/c4/proof.md) | **Solved** | Complete written sharp bounds: five lines in ℝ³ give S≤4π; six in ℝ⁴ give S≤13π/2. Supporting geometric and matrix lemmas checked in Lean. | None for the task; full geometric Lean assembly remains incomplete. |
| P1 — [C5](cagent/p1/c5/proof.md) | **Solved** | Complete written sharp bound for every d≥2 and N=d+2: S≤(choose(N,2)−2)π/2. | None for the task; general Lean formalization remains incomplete. |
| P1 — [C6](cagent/p1/statements.md) | Skipped | General N-line, d-dimensional conjecture. | Open-conjecture work paused. |
| **P2 · Hypercube paths** — [C1](cagent/p2/c1/C1Optimal.lean) | **Solved** | Lean: exact U(Q3)=14 and U(Q4)=34, with explicit attaining labellings and universal lower bounds. | None. |
| P2 — [C2](cagent/p2/c2/Q5.lean) | **Solved** | Exact value 88 and [required binary labelling](cagent/p2/c2/q5-labels.txt); witness count and permutation checked in Lean. | None for the task; universal Lean lower bound remains incomplete. |
| P2 — [C3](cagent/p2/c3/Q6.lean) | **Solved** | Exact value 204 and [required binary labelling](cagent/p2/c3/q6-labels.txt); witness count and permutation checked in Lean. | None for the task; universal Lean lower bound remains incomplete. |
| P2 — [C4](cagent/p2/README.md) | **Solved** | Exact values 464/1040 and [Q7](cagent/p2/c4/q7-labels.txt)/[Q8](cagent/p2/c4/q8-labels.txt) binary labellings; witness counts and permutations checked in Lean. | None for the task; universal Lean lower bounds remain incomplete. |
| P2 — [C5](cagent/p2/README.md) | Skipped | Q9 bound-improvement research. | Open-problem work paused. |
| P2 — [C6](cagent/p2/README.md) | Skipped | Exact Q9 problem. | Open-problem work paused. |
| **P3 · Bulgarian solitaire** — [C1](cagent/p3/c1/README.md) | **Solved** | Lean, all sizes: cyclic partitions are exactly rank-k binary boundaries of weight n−Tₖ₋₁; cycles correspond to rotations; every triangular partition reaches its unique staircase. Exact convergence times for k≤6. [Complete written C1 proof](cagent/p3/c1/written-proof.md) supplies the numerical necklace-count formula; actual cycles checked independently for n≤40. | None for the task; the numerical counting argument is written, not yet formalized in Lean. |
| P3 — [C2](cagent/p3/c2/README.md) | **Solved** | [Complete written upper bound](cagent/p3/c2/upper-bound-proof.md) and [explicit extremal family](cagent/p3/c2/lower-bound-proof.md) prove D(Tₖ)=k(k−1) for all k≥1. Lean checks k≤6 and abstract descent arithmetic. | None for the task; general lifetime lemmas and witness remain outside Lean. |
| P3 — [C3](cagent/p3/c3/written-proof.md) | **Solved** | Written proof: D(n)≤k²−2k−1 for every nontriangular rank k≥4, equality at Tₖ−1, and explicit inverse construction of every maximizer. Independent inverse/forward sets agree for k=4–7. | None for the task; general classification and bounds are not fully formalized in Lean. |
| P3 — [C4](cagent/p3/c4/written-proof.md) | **Solved** | Complete written upper/lower proof: D(Tₖ₋₁+1)=(k−1)(k−3) for every k≥5, with explicit attaining partitions. Lean covers k=5,6,7; independent exhaustive replay covers k≤9. | None for the task; the general lifetime and rotation proof is not fully formalized in Lean. |
| P3 — [C5](cagent/p3/c5/README.md) | Not solved | Lean: exact exceptional values through k=6 and D(23)=18. [Written explicit family](cagent/p3/c5/lower-bound-proof.md) has depth (k−1)(k−4) for every k≥5. | [Remaining uniform upper-bound case](cagent/p3/c5/upper-bound-proof.md): first entry into one explicit cyclic family; the other family and all other pattern widths handled. |
| P3 — [C6](cagent/p3/c6/README.md) | Skipped | General exact-depth problem. | Open-conjecture work paused. |
| **P4 · Congruence classes** — [C1](cagent/p4/c1/README.md) | **Solved** | Lean: three pairwise disjoint classes imply a pair of moduli with gcd≥3. | None. |
| P4 — [C2](cagent/p4/c2/README.md) | **Solved** | Lean: four pairwise disjoint classes imply a pair of moduli with gcd≥4. | None. |
| P4 — [C3](cagent/p4/lean/ProofPursuit/P4/C3.lean) | **Solved** | Lean: the full gcd bound for every 2≤k≤8. | None. |
| P4 — [C4](cagent/p4/c4/solution.md) | **Solved** | Unconditional Lean proof through 12; two exhaustive searches agree on reduced survivors for every k=9–16; each survivor decided with a certified minimum obstruction. Complete recorded replay: 500.013 seconds. | None for the task; exhaustive search and residue-certificate replay beyond 12 are external computation, not full Lean proofs. |
| P4 — [C5](cagent/p4/c5/solution.md) | **Solved** | Certified contiguous boundary 2–14: Lean through 12; complete computational proofs for 13–14; two methods, exact survivor decisions, minimum obstructions, positive control and pruning on/off replay. Written exclusions of 24/30 as least counterexamples. | None within the explicit boundary 14; no C5 benchmark claim through 16. |
| P4 — [C6](cagent/p4/README.md) | Skipped | General disjoint-congruence-class conjecture. | Open-conjecture work paused. |

### Proofs and replay evidence

All packages pin Lean **4.34.1**. P1 additionally pins Mathlib. Lean-checked finite searches are exact within their stated range; they do not prove unrestricted formulas.

| Package | Reproduce from repository root | Evidence and trust boundary |
| --- | --- | --- |
| [P1 · Angles](cagent/p1/README.md) · [final judge write-up](cagent/p1/writeup.md) | `cd cagent/p1 && ./verify.sh` | [Lean log](cagent/p1/evidence/verification.log), [environment and checksum](cagent/p1/evidence/environment.txt), [written proofs](cagent/p1/writeup.md), [fresh 18-module replay](cagent/p1/evidence/replay/README.md). Source checked against pinned local Mathlib; clean portable dependency-download replay not yet run. |
| [P2 · Hypercube paths](cagent/p2/README.md) · [final judge write-up](cagent/p2/writeup.md) | `cd cagent/p2 && ./verify.sh` | [C1 proof and kernel replay](cagent/p2/c1-optimality.log), [Q3–Q8 witness log](cagent/p2/verification.log), [written lower bounds](cagent/p2/Established-results.md). C1 has complete formal optimality; the [general path-count budget](cagent/p2/shared/DecyclingBridge.lean) and conditional Q5 search bridge are also kernel-checked. C2–C4 have Lean upper bounds and written lower bounds supported by [two independent Q5 replays](cagent/p2/c2/C2-notes.md) plus face doubling; [method fit](cagent/p2/README.md#method-fit) explains the remaining formalization gap. Q8 verification takes substantially longer than smaller cases. |
| [P3 · Bulgarian solitaire](cagent/p3/README.md) · [consolidated write-up; C5 partial](cagent/p3/writeup.md) | `python3 cagent/p3/verify.py` | [Source hashes, axioms and timings](cagent/p3/evidence/verification.json): 41 files passed in 28.203 seconds; [independent kernel checks](cagent/p3/evidence/kernel-checks.json) passed for the three new principal results. Includes exact depths for every n=1–23. [Separate cycle-count replay](cagent/p3/evidence/cycle-counts.json): 215,307 partitions through n=40; this is finite cross-checking, not a Lean proof of the general count. [Method fit](cagent/p3/README.md#method-fit). |
| [P4 · Congruence classes](cagent/p4/README.md) · [final judge write-up](cagent/p4/SUBMISSION.md) | `cd cagent/p4/lean && lake build ProofPursuit.P4.ThroughTwelve && lake env leanchecker ProofPursuit.P4.ThroughTwelve` | [Verification record](cagent/p4/verification.md) and [C4 audit replay](cagent/p4/c4/README.md). Full C1–C3 and unconditional range 2–12 kernel-checked; independent computational survivor replay and cited 24/30 least-counterexample proof published. C5 meets its criteria for boundary 14; [complete replay](cagent/p4/c5/solution.md) includes both algorithms and pruning comparisons. [C4’s full 9–16 audit](cagent/p4/c4/solution.md) is complete; recorded full replay took 500.013 seconds. |

Agents must update this overview in the same publication as new verified coverage. Detailed package READMEs explain individual proofs; they are not separate global scoreboards. [Publishing rules](cagent/AGENTS.md).

## Start here

- [Hackathon brief](docs/frontier-hackathon-brief.md): recommended project, architecture, verification, and 48-hour plan.
- [Problem portfolio](docs/problem-portfolio.md): nine project ideas with definitions, seed proofs, demo flows, and frontier extensions.
- [OpenAI research](docs/openai-math-research.md): mathematical discovery results, proof workflows, and independent benchmarks.
- [Anthropic and autoresearch](docs/anthropic-autoresearch.md): research agents, proof collaboration, and practical use of Fable credits.
- [Discovery systems](docs/discovery-systems.md): FunSearch, AlphaEvolve, AlphaProof, and verification methods.

## Recommended project

**Conjecture Lab:** a visual workspace that takes a mathematical claim through experiments, counterexamples, revised statements, and checked proofs. Start with one complete domain: graph conjecture repair, cap-set construction, or the problems supplied by the organizers.

Research snapshot: **26 September 2026**. These documents are research and project design, not an implemented autonomous research application. Source-reported results are distinguished from locally reproduced results. No large external Lean proof repository was rebuilt for this research.

## Run the calibration experiments

Python 3.10 or newer; standard library only. No API key or GPU required.

```sh
python3 experiments/seed_experiments.py
```

The script enumerates all labeled simple graphs on one through six vertices and searches for small cap sets in the three-dimensional vector space over the field with three elements. It reproduces a five-cycle counterexample and a nine-point cap construction.

[Recorded output](experiments/seed-results.json) contains the exact witnesses. These are known calibration results, not claims of novel mathematics or a complete implemented agent loop.

## Evidence standards

Keep experimental support, exact counterexamples, verified constructions, general proofs, optimality, and novelty separate. Preserve the original problem when changing assumptions. Every accepted result should include its mathematical statement, artifact, checker output, and reproduction instructions.
