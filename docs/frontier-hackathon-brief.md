# Climbing to the Frontier: hackathon research brief

Research snapshot: 26 September 2026. Context: vibe-coding hackathon, substantial Claude Fable credits. Duration and team expertise unspecified; schedule below assumes 48 hours. This is research and project design, not an implemented autonomous research product.

**Recommendation: build a visual proof-and-counterexample laboratory with one mathematically narrow, working engine.** If organizers supply problems, prioritize an intake-and-proof workflow adapted to that list. If teams choose their problem, graph conjecture repair offers the strongest accessible demo; cap-set construction offers the clearest connection to published discovery systems.

Research tracks: [OpenAI](openai-math-research.md), [Anthropic and autoresearch](anthropic-autoresearch.md), [discovery systems](discovery-systems.md), [problem portfolio](problem-portfolio.md). Each records primary sources and separates provider reports from independently established results. No external proof repositories were compiled in this research session.

## What the product should do

Input mathematical statement → preserve exact assumptions → search references and examples → launch diverse approaches → run cheap falsification → extract useful intermediate claims → check certificates → publish an inspectable result bundle. An unsuccessful full proof should still yield explicit counterexamples to approaches, proved special cases, reusable lemmas, or precisely scoped negative search results.

Agent roles are jobs, not personalities. One researcher locates prior results; one writes a constructive or algebraic approach; one searches counterexamples; one attempts proof and certificate extraction. One coordinator schedules the next action using observed results. The verifier is ordinary trusted software, not another language model. Separate workers only where outputs can be checked independently.

Avoid building a general-purpose research platform first. Ship one problem end to end, then generalize its interface. Credits remove some inference constraints; they do not create a good objective, correct formalization, useful theorem libraries, or guaranteed scientific novelty.

## Ranked project choices

| Rank | Project | Why it fits | Verified output | Main risk |
|---|---|---|---|---|
| 1 | Graph conjecture repair | Visual, exact finite objects, obvious failures and improvements | Counterexample graph; repaired theorem proof | Quietly changing the original question |
| 2 | Cap-set construction laboratory | Direct program-evolution research pattern | Explicit set and checker, product theorem | Rediscovering known constructions |
| 3 | Supplied-problem proof workbench | Best when organizers provide statements | Checked proof or exact unresolved obligation | Lean library gaps and unrestricted scope |
| 4 | Sharp polynomial inequalities | Numerical exploration leads to exact algebra | Rational sum-of-squares identity and sharpness witness | Treating floating-point solver output as proof |
| 5 | Recurrence invariant discovery | Fast computation and short induction proofs | Invariant with base and preservation proofs | Guessing patterns from too few terms |
| 6 | Ramsey coloring explorer | Strong visual demo and certificate structure | Coloring proving lower bound; checked UNSAT for small exact case | Large search explosion |
| 7 | Error-correcting code search | Engineering relevance and simple exact distances | Explicit code and minimum-distance check | Current record comparison and upper bounds |
| 8 | Proof-gap debugger | Helpful even on unsolved input problems | Located gap, counterexample, or repaired lemma | LLM referee agreement mistaken for correctness |

Ranks reflect project judgment, not empirical success probabilities. Required coordination: one person owns statement semantics and verifier; search workers own isolated candidate artifacts. No outside mathematician required for the elementary calibration demos; genuine research novelty and complex formalization benefit from expert review.

## Project 1: graph conjecture repair

Seed claim: every triangle-free simple graph on n vertices has independence number α(G) ≥ n/2. Independence number means the largest vertex set containing no edge.

Search all small graphs, filter those containing triangles, compute α exactly, and exhibit a failing graph. The five-cycle C5 has α=2<5/2. Removing any vertex produces a path, so the witness is easy to understand and visualize. The graph is a direct disproof of the universal claim; no statistical confidence is needed.

Repair branch: for bipartite graphs, α(G) ≥ n/2, since one of the two independent color classes has at least half the vertices. Display this as a new, stronger-hypothesis statement. The original conjecture remains disproved. This distinction is central to honest proof-repair UX.

Next seed theorem: Mantel's theorem, m≤floor(n²/4) for triangle-free graphs. Proof: for each edge uv, N(u) and N(v) are disjoint, so d(u)+d(v)≤n. Summing over edges gives Σd(v)²≤nm. Cauchy–Schwarz gives Σd(v)²≥(2m)²/n. For n,m>0, combine and divide to obtain m≤n²/4. Zero cases are immediate. Balanced complete bipartite graphs attain floor(n²/4). This proves all n; finite search only suggests and checks examples.

Research extension: users impose an additional explicit forbidden-subgraph or degree condition and study extremal edge counts or independence bounds. Generate conjectures from small cases, then test different graph families and larger sizes. Before calling a bound new, compare exact hypotheses and parameters against the literature. A restricted-family result is still valuable when clearly named.

Three-minute demo: type false claim; watch smallest counterexample appear; inspect violating values; propose a new hypothesis; inspect its proof; then launch a bounded unexplored variant. Every status transition references an actual artifact.

## Project 2: cap-set construction laboratory

A cap set A⊆F₃ⁿ has no three distinct elements x,y,z with x+y+z=0 coordinatewise modulo 3. Objective: find large A. Small n gives cheap experiments; structured construction programs can generalize across n.

Baseline: {0,1}ⁿ has size 2ⁿ and is a cap. In any coordinate, a sum of three binary entries is 0 modulo 3 only if all three entries are equal. Thus a zero-sum triple is constant in every coordinate.

Candidate engine: generate a priority rule for points, build a cap greedily, add local deletion-and-repair moves, and evolve the generating program. The checker independently reads only the resulting point list. It validates dimension, allowed coordinates, uniqueness, and every forbidden triple. A larger valid set establishes a better construction lower bound, not optimality.

Lifting theorem: if A⊆F₃ⁿ and B⊆F₃ᵐ are caps, then A×B is a cap. For any zero-sum triple in the product, each projected triple must have all entries equal: in characteristic 3, if two entries agree, the third agrees too; otherwise the cap condition forbids it. Both projections are constant, so the full triple is constant. Hence |A×B|=|A||B|.

This session's 9-point seed in dimension 3 therefore gives 9ᵏ points in dimension 3k, compared with 8ᵏ from the binary-cube baseline. This is a known elementary calibration result, not a new bound.

Fable's useful job: propose reusable priorities, exploit observed symmetries, explain why successful constructions work, and suggest stronger families. Let Python evaluate many candidates per model call. Compare against random greedy and local-search baselines under equal runtime. Require a separate larger-dimension evaluation before claiming a heuristic generalizes.

Demo: rotate a 3D point set, highlight the forbidden third point created by a selected pair, compare constructions, replay exact checking, and show the Cartesian-product proof. Larger n can use coordinate tables or projections with an explicit label: projections do not preserve the full geometry.

## Project 3: supplied-problem proof workbench

Import the organizer's exact statement. Record domains, quantifiers, hypotheses, target conclusion, allowed tools, and whether a formal proof is required. Search for existing results only when competition rules permit it. If a formal statement exists, preserve its pinned version.

Represent a proposed proof as a directed acyclic graph of lemmas. Every node has its exact statement, dependencies, artifact, and status. A lemma is verified only after its proof passes the relevant checker. The full claim is verified only after every needed dependency closes and the final theorem matches the input. Counting completed lemmas does not yield a meaningful percentage of proof completion.

Example split: algebraic identity → nonnegativity lemma → desired inequality. Failed branch: an intermediate lemma is false → counterexample worker supplies witness → planner replaces that branch. A counterexample to a lemma need not disprove the original theorem.

Weekend scope: support one domain already represented in the chosen library. Polynomial identities, integer divisibility, or short induction arguments are more tractable than importing an entire analysis textbook. Unresolved theorem remains unresolved even if many interesting lemmas were proved.

## Project 4: sharp-constant inequality search

Seed: determine the largest real c such that x⁴+y⁴+z⁴ ≥ c(x²y²+y²z²+z²x²) for all real x,y,z.

Setting x=y=z=1 forces c≤1. For c=1,

    x⁴+y⁴+z⁴−x²y²−y²z²−z²x²
      = ((x²−y²)²+(y²−z²)²+(z²−x²)²)/2 ≥ 0.

Therefore c=1 is sharp. This is a known warm-up. The useful workflow is search for a candidate constant and decomposition, then check exact coefficients and positivity; boundary or equality cases certify sharpness.

Generalization: constrained homogeneous polynomial families, symmetric variables, or low-degree rational certificates. Numerical SDP feasibility is a proposal. Rational reconstruction plus exact identity checking supplies the certificate. Failure to find a sum-of-squares decomposition does not prove an inequality false: the certificate class can be incomplete. Surface that distinction directly.

## Experiments actually run

[seed_experiments.py](../experiments/seed_experiments.py) uses Python's standard library; [seed-results.json](../experiments/seed-results.json) contains its output.

- Enumerated every labeled simple graph for n=1,…,6. Among triangle-free graphs, maximum edge counts were 0,1,2,4,6,9. The first failure of α(G)≥n/2 appeared at n=5 and was a five-cycle. This finite coverage does not prove Mantel's theorem.
- Ran 100 seeded random-greedy cap searches in F₃³. Best size: 9, exceeding the 8-point cube baseline. A separate direct checker inspected all 84 triples. No proof of optimality was attempted.
- Neither experiment calls Fable. They establish working baselines; any agent-based approach should be evaluated against them rather than credited for improvements that ordinary search already achieves.

Reproduce: `python3 experiments/seed_experiments.py`. No model API, new packages, training, server, or simulator required.

## Architecture and trust boundaries

Keep immutable problem statements and trusted verifiers outside worker write access. Workers emit candidate programs, proof files, or structured mathematical objects. Run generated code in bounded isolated processes with no secrets or network by default. Capture timeouts separately from mathematical failures.

For each attempt record: problem revision, precise claim, source links, model/version, approach, parent artifact, seed, tool versions, input/output tokens, duration, verification command, exit status, result artifact, and human interventions. Cache duplicate claims. Preserve negative results.

Accepted statuses: proposed; empirically supported within a named domain; explicit counterexample verified; construction verified; informal proof awaiting review; formal proof checked; unresolved. Store novelty separately: known; literature match found; novelty unchecked; expert-reviewed novelty. A formal proof can reproduce old mathematics.

The formal route requires reviewing statement meaning, compiling the actual theorem module, auditing transitive axioms, and pinning Lean/mathlib. Reject unfinished proofs and unauthorized axioms. If native evaluation is used, document its expanded trust base. The [Lean verification guide](https://leanprover-community.github.io/did_you_prove_it.html) explains these distinctions; [Comparator](https://github.com/leanprover/comparator) can check a submitted solution against a fixed challenge under its documented environment assumptions.

Use a small initial worker pool. Split strategies, not duplicate vague prompts: combinatorial counting, explicit construction, algebraic reformulation, and counterexample search. Let independent branches work before sharing a compact evidence summary. Expand only after measuring duplicate work, timeouts, and verified yield. Credit availability alone does not establish safe API concurrency or throughput.

## Evaluation plan

Before autonomous runs, freeze a small calibration suite: known true statements, known false near-neighbors, invalid certificates, boundary cases, and a few unrevealed parameter instances. Pre-register the exact comparator and resource caps.

Compare (1) direct Fable proof attempt, (2) one agent with tools and verification feedback, and (3) multiple strategy workers. Use the same mathematical inputs and matched inference or elapsed-time budgets; report both spend and wall time. For stochastic construction tasks, repeat across fixed seeds. For proof tasks, report verified successes, unresolved cases, statement mismatches, and false acceptances. Do not manufacture success-rate estimates from a handful of examples.

Useful metrics: valid counterexamples found; checked constructions and sizes; genuinely closed theorems; time and tokens per accepted artifact; checker failures; intervention count. Open-problem progress should name the exact new bound or proved special case. Avoid confidence meters and subjective novelty scores.

## 48-hour plan

Hours 0–4: select one engine; freeze statements and checker; run known true/false calibration cases. Exit condition: one valid artifact accepted and one invalid artifact rejected.

Hours 4–12: implement experiment runner, persistence, budget controls, direct-agent baseline, and replayable evidence. Exit condition: end-to-end job survives failure and reports honest status.

Hours 12–24: add diverse strategy workers, checkpointing, and experiment comparison. Exit condition: real measured output against the non-agent baseline.

Hours 24–36: add visual explanation, statement revision tracking, and certificate export. Introduce one clearly labeled frontier stretch task only after the working path is reliable.

Hours 36–44: run held-out cases; test wrong statements, altered assumptions, malformed witnesses, stale results, timeouts, and unresolved proofs. Rebuild exported proof artifacts in a clean pinned environment where applicable.

Hours 44–48: freeze demo artifacts, record a genuine live run and replay fallback, prepare the source and novelty ledger. Demo should distinguish live progress from recorded output.

For a 24-hour event: remove general-purpose problem import, external solver provisioning, and complex formalization. Preserve one exact checker, one autonomous loop, one visual explanation, and one exportable artifact.

## What earns a strong demo

1. A conjecture is entered with explicit assumptions.
2. Several materially different strategies start.
3. A candidate fails and the app shows why.
4. A useful object or proof survives independent checking.
5. An explanation connects that artifact to the claim.
6. Judges can download and rerun the evidence.

An open problem solved would be exceptional. A system that reliably turns speculation into checkable mathematical progress is already a coherent hackathon outcome.
