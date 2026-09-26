# Climbing to the Frontier

A hackathon research workspace for automated mathematical discovery: explore conjectures, search for counterexamples, improve constructions, and produce independently checkable proofs.

## Proof progress

**3 solved · 16 not solved · 5 skipped.** This is the authoritative progress overview. “Solved” means the **entire cell** is proved in Lean. “Not solved” includes useful partial proofs, finite cases, and witnesses without optimality. “Skipped” means intentionally paused; it does not mean impossible. No answers have been submitted to the hackathon platform.

The table records **published, verified work**, not unfinished local experiments. Proof links include the exact statements and limitations. Written arguments are identified separately from Lean proofs.

| Problem / cell | Status | Published result | What remains for the full cell |
| --- | --- | --- | --- |
| **P1 · Angles** — [C1](cagent/p1/c1/README.md) | Not solved | Lean: planar line-angle bound for N=2,3,4. Written proof: all N. | Formalize the all-N argument. |
| P1 — [C2](cagent/p1/c2/README.md) | Not solved | Lean: chain bound for m=2,3. Written proof: every m≥2. | Formalize the general orthogonal-chain argument. |
| P1 — [C3](cagent/p1/c3/README.md) | Not solved | Lean: d+1-line bound for d=1,2. | Prove the bound in every dimension. |
| P1 — [C4](cagent/p1/statements.md) | Not solved | No complete geometric Lean proof published. | Prove the five-line ℝ³ bound 4π and six-line ℝ⁴ bound 13π/2. |
| P1 — [C5](cagent/p1/c5/README.md) | Not solved | Lean: d+2-line bound for d=2. | Prove the bound for all d≥2. |
| P1 — [C6](cagent/p1/statements.md) | Skipped | General N-line, d-dimensional conjecture. | Open-conjecture work paused. |
| **P2 · Hypercube paths** — [C1](cagent/p2/README.md) | Not solved | Lean: explicit Q3/Q4 labellings with 14/34 uphill paths. Written lower bounds available. | Formalize optimality; Lean currently proves upper bounds only. |
| P2 — [C2](cagent/p2/c2/Q5.lean) | Not solved | Lean: Q5 labelling with 88 paths. Written optimality uses established decycling results. | Formalize the lower bound. |
| P2 — [C3](cagent/p2/c3/Q6.lean) | Not solved | Lean: Q6 labelling with 204 paths. Written optimality uses established decycling results. | Formalize the lower bound. |
| P2 — [C4](cagent/p2/README.md) | Not solved | Lean: Q7/Q8 labellings with 464/1040 paths. Written optimality uses established decycling results. | Formalize both lower bounds. |
| P2 — [C5](cagent/p2/README.md) | Skipped | Q9 bound-improvement research. | Open-problem work paused. |
| P2 — [C6](cagent/p2/README.md) | Skipped | Exact Q9 problem. | Open-problem work paused. |
| **P3 · Bulgarian solitaire** — [C1](cagent/p3/c1/README.md) | Not solved | Lean, all sizes: staircase fixed points; binary-boundary cycles; eventual cycling; non-increasing energy and cyclic largest-pile bound. Triangular convergence/unique cycle for k≤6. | Prove converse cycle classification, count cycles, and general triangular convergence/uniqueness. |
| P3 — [C2](cagent/p3/c2/README.md) | Not solved | Lean: exact triangular maximum depths 0,2,6,12,20,30 for k=1,…,6. | Prove the all-k formula and matching extremal construction. |
| P3 — [C3](cagent/p3/c3/README.md) | Not solved | Lean: exact depths for all nontriangular sizes of ranks 4–6; further small cases included. | General upper bound, exact depth at Tₖ−1, and all maximizing partitions. |
| P3 — [C4](cagent/p3/c4/README.md) | Not solved | Lean: D(11)=8, D(16)=15, D(22)=24. | General formula for Tₖ₋₁+1, with upper/lower proofs and extremals. |
| P3 — [C5](cagent/p3/c5/README.md) | Not solved | Lean: D(3)=2, D(5)=3, D(8)=5, D(12)=8, D(17)=12, D(23)=18. | General Tₖ₋₁+2 formula, exceptions, extremals, and explanation of the failed extension. |
| P3 — [C6](cagent/p3/c6/README.md) | Skipped | General exact-depth problem. | Open-conjecture work paused. |
| **P4 · Congruence classes** — [C1](cagent/p4/c1/README.md) | **Solved** | Lean: three pairwise disjoint classes imply a pair of moduli with gcd≥3. | None. |
| P4 — [C2](cagent/p4/c2/README.md) | **Solved** | Lean: four pairwise disjoint classes imply a pair of moduli with gcd≥4. | None. |
| P4 — [C3](cagent/p4/lean/ProofPursuit/P4/C3.lean) | **Solved** | Lean: the full gcd bound for every 2≤k≤8. | None. |
| P4 — [C4](cagent/p4/README.md) | Not solved | Published general range currently ends at k=8. | Complete the required larger finite cases and justify the reduction/survivor analysis. |
| P4 — [C5](cagent/p4/README.md) | Not solved | No full-cell Lean proof published. | Formalize the required established larger-case results. |
| P4 — [C6](cagent/p4/README.md) | Skipped | General disjoint-congruence-class conjecture. | Open-conjecture work paused. |

### Proofs and replay evidence

All packages pin Lean **4.34.1**. P1 additionally pins Mathlib. Lean-checked finite searches are exact within their stated range; they do not prove unrestricted formulas.

| Package | Reproduce from repository root | Evidence and trust boundary |
| --- | --- | --- |
| [P1 · Angles](cagent/p1/README.md) | `cd cagent/p1 && ./verify.sh` | [Lean log](cagent/p1/evidence/verification.log), [environment and checksum](cagent/p1/evidence/environment.txt), [written proofs](cagent/p1/written-proofs.md). Source checked against pinned local Mathlib; clean portable dependency-download replay not yet run. |
| [P2 · Hypercube paths](cagent/p2/README.md) | `cd cagent/p2 && ./verify.sh` | [Lean log](cagent/p2/verification.log), [written lower bounds](cagent/p2/Established-results.md). Q8 verification takes substantially longer than smaller cases. No formal optimality claim. |
| [P3 · Bulgarian solitaire](cagent/p3/README.md) | `python3 cagent/p3/verify.py` | [Source hashes, axioms and timings](cagent/p3/evidence/verification.json): 31 files passed in 25.466 seconds. Includes exact depths for every n=1–23. |
| [P4 · Congruence classes](cagent/p4/README.md) | `cd cagent/p4/lean && lake build ProofPursuit.P4.C3 && lake env leanchecker ProofPursuit.P4.C3` | [Verification record](cagent/p4/verification.md). Full C1–C3 statements checked; positive moduli and actual set-disjointness are explicit hypotheses. |

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
