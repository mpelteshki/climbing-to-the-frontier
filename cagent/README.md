# Verified proof packages

Completed, verified proofs are published here, grouped by problem. Each published package must include its exact statements, Lean sources, pinned build configuration, verification commands, and evidence.

## Cell status

**Solved** = the full cell statement is verified in Lean. **Not solved** = incomplete, including verified partial results. **Skipped** = deliberately paused under current scope; it does not mean proved or impossible.

| Problem | C1 | C2 | C3 | C4 | C5 | C6 |
| --- | --- | --- | --- | --- | --- | --- |
| [P1 · Angles](p1/README.md) | Not solved | Not solved | Not solved | Not solved | Not solved | Skipped |
| [P2 · Hypercube paths](p2/README.md) | Not solved | Not solved | Not solved | Not solved | Skipped | Skipped |
| [P3 · Bulgarian solitaire](p3/README.md) | Not solved | Not solved | Not solved | Not solved | Not solved | Skipped |
| [P4 · Congruence classes](p4/README.md) | **Solved** | **Solved** | **Solved** | Not solved | Not solved | Skipped |

Skipped cells are paused under the instruction to avoid open-conjecture work. Package READMEs below record exact partial results and verification limitations. Written arguments and finite instances do not upgrade a cell to Solved unless they cover its full statement in Lean.

## Verified progress

| Problem folder | Publication status |
| --- | --- |
| [p1/](p1/README.md) | Partial Lean geometric cases: C1 N=2–4, C2 m=2–3, C3 d=1–2, C5 d=2 |
| [p2/](p2/README.md) | Lean-checked Q3–Q8 labelings and exact witness counts; upper bounds only, optimality not yet formalized |
| [p3/](p3/README.md) | Exact Lean depths for n=1–23; general binary-boundary cycles, eventual cycling, and monotone energy; all-k staircase fixed point; triangular convergence/uniqueness for k=1–6. Converse cycle classification remains unformalized; cells remain partial |
| [p4/](p4/README.md) | Lean proofs for every size 2–8; C1, C2, and C3 complete; C4/C5 not solved; C6 paused |

## Instructions for contributing agents

1. Read [AGENTS.md](AGENTS.md), the target problem README, and the exact cell statement before starting. Coordinate ownership and use GPT-6 Sol at high reasoning for simpler tasks.
2. Keep proofs and reproducible verification under `cagent/<problem>/`. Preserve existing verified results and distinguish full statements from restricted cases.
3. Before marking a cell Solved, verify the complete Lean theorem, audit its assumptions and axioms, and link its source and verification evidence from the problem README. No `sorry`, unproved custom axioms, or unsupported optimality claims.
4. Update this grid and the problem README in the same publication as any status change. Keep partial results Not solved and describe their exact scope in Verified progress. Record a reason when marking a cell Skipped; do not resume paused work without user direction.
5. Coordinate with the current Git integrator, publish only agreed files, verify the remote commit, and report its GitHub link. Never include another agent's unfinished work.

Packages use `cagent/<problem>/` with clearly named cell folders or Lean modules. Follow [publishing instructions](AGENTS.md). GitHub publication does not submit work to the hackathon platform.
