# Mathematical discovery systems: evidence and hackathon design

Research checked September 26, 2026. Primary sources below; recommendations explicitly labeled. Source-reported success does not imply independent reproduction during this research.

## Main finding

Best hackathon architecture: **propose → execute → falsify → retain → explain → certify**. Choose problems whose output admits cheap, exact checking. Separate search ingenuity from trusted verification. A verified finite construction can already constitute real mathematical progress; proving global optimality is a different task.

## What successful systems actually do

### FunSearch: search for programs that construct mathematical objects

FunSearch combines an LLM proposing code with an evaluator retaining successful programs. Its cap-set application searches for large subsets of finite vector spaces with no nontrivial three-term arithmetic progression; its bin-packing application searches for useful heuristics. Program output matters because mathematicians can inspect a compact rule, rather than only a giant list of points. Manual simplification of discovered code helped expose construction structure. The Nature paper reports a cap set of size 512 in dimension eight. This establishes existence of that construction; it does not prove the maximum possible size. [Nature, December 2023](https://www.nature.com/articles/s41586-023-06924-6).

Public repository includes cap-set constructions, numerical outputs, bin-packing examples, evolutionary machinery, and a single-threaded pipeline. **It excludes the language model, sandbox for untrusted execution, and distributed infrastructure.** Therefore “clone and run FunSearch” still requires engineering and model access. [Official repository](https://github.com/google-deepmind/funsearch/blob/main/README.md).

**Hackathon adaptation:** freeze a correct greedy constructor; evolve only its priority function. Constructor preserves validity by design. Separate verifier checks every final object from scratch. This keeps model freedom focused and makes failures interpretable. Start with small dimensions where exhaustive or baseline results are available, then increase difficulty.

### AlphaEvolve: evolve algorithms, not only short priorities

AlphaEvolve accepts working seed code, editable regions, and an automated evaluator. Candidate edits can span multiple components. It executes candidates, scores them, stores promising programs, and uses previous programs to guide later proposals. Mathematical evaluators can be simple: generate a graph, verify its property, score its size. Its main prerequisite is an automated evaluator. Human mathematicians helped choose problems and express useful objectives. [Technical paper, June 2025](https://arxiv.org/html/2506.13131v1).

Launch examples include an algorithm using 48 scalar multiplications for 4×4 complex matrix multiplication and 593 mutually non-overlapping spheres touching a central sphere in dimension 11. The latter proves a lower bound, not the exact kissing number. The reported roughly 75% rediscovery/20% improvement figures refer to the authors’ selected suite of over 50 problems, not a universal success rate for open mathematics. [Official launch report](https://deepmind.google/blog/alphaevolve-a-gemini-powered-coding-agent-for-designing-advanced-algorithms/).

Availability changed: Google announced AlphaEvolve generally available on Google Cloud July 9, 2026. It is no longer accurate to describe it as internal-only. Access through a commercial service does not mean training code or weights are open source. [Google Cloud announcement](https://cloud.google.com/blog/products/ai-machine-learning/alphaevolve-is-available-for-everyone).

**Hackathon adaptation:** allow evolution of representation, initialization, mutation, and local-search schedule only after a single-function baseline works. Evaluation correctness remains outside editable code. Store raw candidate artifacts as well as score: a score without reconstructible witness is weak evidence.

### Discovery → informal proof → formal proof: real example, real limits

The 2025 *Mathematical exploration and discovery at scale* paper studies 67 problems. It describes a finite-field Kakeya pipeline: AlphaEvolve finds constructions; Deep Think derives formulas and proofs; AlphaProof formalizes one instance in Lean. Formalization succeeded for an elementary three-dimensional case. More demanding four- and five-dimensional arguments required human checking; relevant mathematical machinery exceeded available formalization capabilities. A Nikodym construction became a starting point for humans, who simplified it and obtained a better result. The paper also reports failures and numerical findings not upgraded to rigorous proofs. Setup often took hours; runs ranged from hours upward. Thousands of LLM samples could suffice, whereas FunSearch used millions. Those scales describe reported experiments, not a guaranteed budget. [Paper, November 2025](https://arxiv.org/html/2511.02864v1).

Public problem gallery supplies a useful starting inventory, mathematical definitions, references, and construction artifacts. Treat each entry’s status individually; archived best-known bounds can become stale. [Official mathematical problem repository](https://google-deepmind.github.io/alphaevolve_repository_of_problems/).

**Hackathon adaptation:** plan three distinct deliverables: verified instance, conjectured family, proved family. Never silently promote one level into the next.

### AI-guided intuition: learn which quantities matter, then do mathematics

DeepMind’s 2021 collaboration used supervised models to predict mathematical properties, then attribution to identify informative invariants. In knot theory, geometry predicted signature; salient cusp quantities suggested a new “natural slope.” An initial conjecture fit large datasets but failed on constructed counterexamples. Refinement produced a theorem involving additional geometric information. Representation-theory work produced a candidate algorithm related to the combinatorial invariance conjecture, not a proof settling that conjecture. Humans chose questions, interpreted model evidence, revised statements, and supplied mathematical proofs. Interactive notebooks were released. [Nature paper](https://www.nature.com/articles/s41586-021-04086-x).

**Hackathon adaptation:** generate a clean dataset of small combinatorial objects, compute exact invariants, fit simple predictors, and search for sparse formulas. Counterexample search should target data outside training distribution: extremal objects, disconnected objects, degenerate cases, and recursively constructed families. Prediction accuracy supplies leads; never certify theorem status through accuracy.

### Ramanujan Machine: conjecturing identities is its own valuable stage

Ramanujan Machine searches continued-fraction representations of mathematical constants. Its algorithms include meet-in-the-middle search and a gradient method adapted to recurrences. Numerical matches generate conjectures, not proofs; the authors explicitly distinguish these. Some generated conjectures were later proved, others remained open at publication. [Nature, February 2021](https://doi.org/10.1038/s41586-021-03229-4).

Official implementation and instructions are public. [Project repository](https://github.com/RamanujanMachine/RamanujanMachine), [run instructions](https://ramanujanmachine.com/run-the-ramanujan-machine/). Subsequent mathematical work proves and generalizes families of these conjectures, illustrating a division of labor between discovery and proof. [Proof and generalization paper, March 2024](https://arxiv.org/abs/2403.09729).

**Hackathon adaptation:** restrict to finite sums or recurrences with available symbolic certificates before attempting infinite continued fractions. A 200-digit match can still be coincidence or truncation error; proving an infinite identity requires convergence and limit reasoning, not merely increasing precision.

### AlphaProof: formal feedback plus large-scale learning

AlphaProof combines policy/value-guided proof search with reinforcement learning in Lean. Training includes proofs and disproofs, with difficult problems receiving additional adaptation through related variants. The published pipeline autoformalized roughly one million informal problems into approximately 80 million formal statements. Reported autoformalization consumed about 100,000 TPU-days; main reinforcement learning about 80,000 TPU-days. Those figures make reproduction of training unsuitable for a weekend project. Open Lean/Mathlib and pseudocode are available; scientific users can apply for server-based AlphaProof access. [Nature paper](https://www.nature.com/articles/s41586-025-09833-y).

**Hackathon adaptation:** use pretrained models and compiler feedback. Spend scarce time on selecting well-formalized problems, retrieval of existing lemmas, and clean validation. Do not train a proof model from scratch.

### AlphaProof Nexus: strongest current lesson for a practical prototype

Nexus reported 9/353 Erdős formal statements and 44/492 OEIS conjectures solved. Erdős search stopped after 3,000 episodes per statement; some reported successes are variants. OEIS statements were autoformalized, tested against initial sequence terms, then manually reviewed. Basic generation–Lean-feedback loops replicated all nine Erdős successes **post hoc on those selected successes**, not through a fresh full-portfolio search. Full agents combined ten prover subagents, evolutionary sketch selection, and optional AlphaProof. Evolution saved 2–5× on two hard examples but was less cost-efficient elsewhere. Reported solved-instance inference costs omit the unsuccessful portfolio search; comparison plots omit AlphaProof, estimated at $60 per problem. Failure modes included moving the entire hard step into an unproved helper and inventing supposedly established lemmas. [May/June 2026 paper](https://arxiv.org/html/2605.22763v2).

**Hackathon adaptation:** begin with independent restart loops. Add shared memory only when evidence shows complementary partial results. Track cost across *all attempted problems*, not just solved examples. Unproved helper count is not a trustworthy progress score: one helper can hide the whole theorem.

### Aristotle and open proof models

Aristotle combines Lean proof search, informal reasoning that proposes/formalizes lemmas, and a specialized geometry solver. Its proof-search core uses Monte Carlo tree search with learned guidance. It reports complete Lean solutions for five of six IMO 2025 problems; accepted solutions exclude proof gaps and unsound placeholder axioms. Published proofs permit inspection. Contest success demonstrates formal problem solving under a specific evaluation setup; it does not by itself demonstrate discovery of new mathematics. [Aristotle paper](https://arxiv.org/html/2510.01346v1).

Goedel-Prover-V2 releases 8B and 32B models plus code/data. Its repository reports miniF2F results at Pass@32, and separate self-correction results. These are multi-attempt benchmark results, not per-prompt reliability or research discovery rates. [Official repository](https://github.com/Goedel-LM/Goedel-Prover-V2).

**Hackathon adaptation:** hosted general reasoning plus local Lean is often simpler operationally. Consider an open proof model when suitable inference hardware is already ready. Access convenience, context handling, library retrieval, and compiler iteration matter more than treating benchmark rank as universal quality.

## What verification must mean

Lean checks the statement actually encoded. That statement can differ from the intended mathematics through assumptions, definitions, quantifiers, types, or notation. Successful compilation is therefore one component of validation. Official Lean guidance separately addresses proof validity and statement meaning. [Validating a Lean proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

Audit theorem dependencies with `#print axioms`. Reject `sorryAx` and unauthorized axioms. Standard mathematical axioms such as choice should be governed by an explicit policy, not confused with arbitrary assumptions. Native evaluation tactics expand the trusted computing base to compiled evaluation; record this instead of claiming exclusively small-kernel checking. [Lean axiom documentation](https://lean-lang.org/doc/reference/latest/Axioms/).

Recommended certificate ladder:

| Claim | Required artifact | What remains unproved |
|---|---|---|
| Numerical pattern | Inputs, precision, residuals, replication | Universal claim; even exact equality |
| Finite counterexample | Exact witness plus independent checker | Nothing further needed to refute matching universal statement |
| Finite construction | Object plus exact constraint checks | Optimality; extension to arbitrary size |
| Optimal finite answer | Valid witness plus matching upper-bound certificate | General theorem across all sizes |
| Infinite family | Construction rule plus general proof | Optimality unless separately proved |
| Formal theorem | Fixed statement, compiled proof, dependency audit, semantic review | Novelty and mathematical importance |
| New research result | Above evidence plus literature/status review | Community validation if not yet obtained |

This ladder is a proposed judging standard. Arithmetic identities over exact integers/rationals offer particularly cheap witnesses. Geometric floating-point outputs need stronger certification: interval arithmetic, algebraic reconstruction, or exact rational perturbation with a proved margin.

## Independent research evaluation: First Proof

First Proof’s second batch used ten withheld-solution research problems, autonomous runs, independent referees, and published costs. Ratings require care: “minor revisions” can include actual proof gaps. These were benchmark problems, not ten previously unsolved public conjectures. [June 2026 report](https://1stproof.org/assets/docs/report.pdf).

**Hackathon adaptation:** freeze hidden challenge statements before development. Record human assistance and all model costs. Have another team review final proofs without knowing which harness produced them. Include baseline single-agent runs; orchestration has to earn its complexity.

## Recommended 24–48-hour build

The following is a design proposal, not a replication claim or measured budget estimate.

### Smallest complete research loop

1. **Problem manifest:** natural-language statement, exact domain, fixed formal statement or checker, known baseline, source date, allowed changes, search budget.
2. **Researcher:** retrieves references and proposes representation, candidate constructions, conjectures, or proof decompositions.
3. **Executor:** runs generated code under restricted execution; returns artifacts, errors, objective values, time, and resource use.
4. **Falsifier:** searches for counterexamples using different methods and edge cases. It can refute an idea but cannot establish a theorem from failed searches.
5. **Archive:** stores every attempt, lineage, hash, score, reason rejected, model/version, seed, and cost. Retains structurally different strong candidates.
6. **Proof worker:** turns promising structure into lemmas and formal proofs where practical.
7. **Independent verifier:** reads immutable original statement and candidate artifact; recomputes validity without trusting search-agent assertions.
8. **Research note:** exact claim, certificate, limitations, prior-art links, budget, human edits, reproduction command.

Do not let generator rewrite verifier, frozen statement, or acceptance rules. Execution needs time and memory limits, network restrictions, and isolation from credentials. Prefer a tiny explicit data format between search and verifier.

### First project: cap-set or forbidden-pattern construction lab

Input: dimension and forbidden configuration. Output: an explicit finite set and proof certificate. Search evolves priority rules or local exchanges. Checker verifies coordinates, uniqueness, cardinality, and forbidden triples using exact modular arithmetic. Comparing unordered pairs gives a direct check: the third point completing a progression must not appear as a distinct member.

Product flow: choose dimension → inspect baseline → watch valid best score improve → inspect candidate structure → independently verify → export witness and research note. Preserve rejected candidates for learning, but do not display invalid candidates as achievements.

Proof ladder: rediscover known small example → beat a naive baseline → match published bound → obtain a new instance under a constrained variant → conjecture a recursive construction → prove closure/size → only then discuss a genuine bound improvement after literature review.

Why strong: exact arithmetic, cheap validation, visualizable low-dimensional cases, natural evolutionary search, clear separation of discovery from certification. Why limited: high-dimensional records may require far more compute and mathematical insight than a weekend.

### Second project: counterexample hunter for graph inequalities

Input: graph class and conjectured inequality between exact invariants. Build seed families: paths, cycles, complete graphs, complete bipartite graphs, trees, disconnected unions, and small enumerated graphs. Search proposes graphs, graph transformations, or inequalities. Falsifier uses random generation, local mutation, and exhaustive enumeration within a small size limit.

Output: smallest found counterexample with exact invariant values, or a clearly bounded verified range. Shrink a counterexample by vertex/edge deletion while preserving failure. A small interpretable obstruction makes a better research artifact than a large opaque graph.

For true statements, look for restricted classes where proof decomposes by induction or existing library results. Do not confuse “holds for every graph enumerated through n vertices” with “holds for every finite graph.”

### Third project: sequence-conjecture repair and proof

Input: curated sequence definition and proposed recurrence/divisibility identity. Generate exact initial terms; test formal definition against those terms; search for minimal recurrence or invariant; challenge extrapolation; prove a restricted or full statement with induction.

Best weekend scope: polynomial recurrences, finite sums, modular periodicity with a proven finite-state argument, or combinatorial counting identities. Avoid using OEIS matching as proof or calling an old identity novel merely because the model rediscovered it.

### Fourth project: proof-carrying optimizer

Input: parameterized recurrence or simple iterative algorithm. Search for coefficients, schedule, or potential function. Evaluator tries to falsify proposed inequalities over varied instances. Proof worker certifies algebraic nonnegativity, induction, or invariant preservation. Output includes both algorithm and guarantee.

Good first target: rational parameters and polynomial potentials whose obligations reduce to exact algebra or sum-of-squares certificates. Hard part: certificate existence and checker correctness. Do not claim convergence of arbitrary optimization methods based only on simulated trajectories.

## Experiment design and finish criteria

Keep three baselines: ordinary random/local search, one-shot model, iterative model with verifier. Add evolution or agent collaboration as a fourth condition only after these run.

Measure verified outcomes, not persuasive text: valid constructions, exact counterexamples, complete formal theorems, independent replay rate, cost per verified improvement, and total cost including failures. Report search seed, hardware, model version, deadline, and assistance. Use fixed candidate count or fixed total cost when comparing methods; equal wall clock alone can hide large compute differences.

Suggested sequence:

- Hours 0–4: lock one mathematical domain, checker, baselines, and known regression cases.
- Hours 4–10: implement one complete propose–execute–verify loop and inspect failures.
- Hours 10–22: run bounded search and independent falsification; retain evidence.
- Hours 22–32: extract structure; attempt proof or exact certification.
- Hours 32–40: re-run cleanly, compare baselines, audit statements and novelty.
- Hours 40–48: prepare live demonstration plus downloadable witness/proof and honest result labels.

For a 24-hour event, cut breadth and formalization ambition; keep independent verification. A complete small result beats an impressive dashboard filled with unproved claims.

Completion means another participant can reproduce the advertised claim from exported artifacts. “Open question solved” requires both mathematically adequate proof and verified open status. A useful failed attempt can still ship: minimized counterexample, corrected conjecture, reproducible search frontier, or a precisely identified missing lemma.
