# Climbing to the Frontier

A hackathon research workspace for automated mathematical discovery: explore conjectures, search for counterexamples, improve constructions, and produce independently checkable proofs.

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
