# OpenAI mathematical research: evidence and hackathon implications
Research checked 26 September 2026. Primary sources only. No proof claimed independently verified here; linked artifacts inspected, not compiled. Later publications excluded. Public availability of certificates does not imply availability of original model, training, or orchestration.

## Decision
Build a small research loop whose output is a checked mathematical artifact: counterexample, proved lemma, verified construction, or explicit unresolved gap. Use headline discoveries as architectural inspiration; choose scope using independently measured success rates.

Most useful practical combination: fixed conjecture + diverse candidate approaches + executable experiments + adversarial review + independent certificate checking + human check that formal statement matches intended question. Separate correctness, novelty, and significance.

## Evidence map

**OpenAI formal theorem proving, 2 February 2022.** Statement curriculum learning used language-model-generated Lean tactics, then retrained on successful proofs. Reported miniF2F improvement from 29.3% to 41.2% after eight iterations. Curriculum supplied statements at varying difficulty, addressing sparse success feedback. This was proof search/training on known-style problems, not autonomous discovery of important open mathematics. Useful architectural ancestor: objective verification turns model suggestions into reliable training/search feedback. Training this system is unsuitable for a weekend; adapting the generate/check loop is feasible. [Official article](https://openai.com/index/formal-math/), [paper](https://cdn.openai.com/papers/Formal_Mathematics_Statement_Curriculum_Learning__ICML_2022.pdf), [Lean environment](https://github.com/openai/lean-gym).

**IMO 2025.** OpenAI reports 35/42, gold-medal-level performance, with a general-purpose experimental reasoning model. This is contest performance, not discovery of an unknown theorem. Public repository contains five natural-language proof files; it is not a released inference harness or trained model. Avoid presenting “gold medal-level” as an official medal awarded to the system. [OpenAI retrospective](https://openai.com/index/first-proof-submissions/), [original proof repository](https://github.com/aw31/openai-imo-2025-proofs/).

**Research collaboration, 20 November 2025.** OpenAI's curated GPT-5 cases include sharpening a gradient-descent step-size condition, contributing an idea to an Erdős-problem proof, and finding cross-field references. Humans selected problems, challenged output, and checked results. Authors explicitly say cases were selected illustrations, not a systematic success-rate study. One especially reproducible pattern: give a known theorem, ask whether a hypothesis or constant can improve, then independently test the proposed strengthening. [Article](https://openai.com/index/accelerating-science-gpt-5/), [research paper](https://arxiv.org/abs/2511.16072).

**First Proof round one, February 2026.** Ten research-origin problems, already solved by their proposers but unpublished; not ten then-open global conjectures. OpenAI's 20 February update assessed problems 4, 5, 6, 9, 10 as likely correct and withdrew confidence in problem 2. Manual orchestration, useful-strategy suggestions, expert-feedback revisions, and human selection among attempts were disclosed. This is evidence for assisted research reasoning, not a clean autonomous success rate. [OpenAI submission update](https://openai.com/index/first-proof-submissions/).

**First Proof's reusable pipeline.** Appendix A, pages 69–71, retrospectively sketches an automated approximation to that manual process: generate five seed approaches; solve from each; check proof and bibliographic references; revise up to three times; typeset survivors. The appendix was produced after the deadline, and same-model approval was not independent proof certification. Good starting scaffold, with one change: model-verifier approval should trigger external checking, never final “proved” status. [Actual 90-page submission and prompts](https://cdn.openai.com/pdf/26177a73-3b75-4828-8c91-e8f1cf27aaa0/oai_first_proof.pdf).

**First Proof round two, June 2026.** Independent refereeing gives more useful comparison than provider anecdotes. GPT-5.5 Pro alone cost $117 across ten problems: two essentially flawless, three minor revisions, one major revision, four rejected. ProofCouncil cost $3,186 and UCLA's harness $4,799. These are small-sample results, not a universal agent ranking. Failure examples include citing a nonexistent theorem equivalent to the target, replacing “almost everywhere” with “everywhere,” and omitting the crucial argument behind polished exposition. [Organizer report, sections 4–5](https://1stproof.org/assets/docs/report.pdf), [code, logs, submissions, referee-report index](https://1stproof.org/second-batch.html).

**Unit-distance disproof, 20 May 2026.** OpenAI reports an internal general-purpose model constructed infinitely many planar point sets with at least n^(1+δ) unit-distance pairs for fixed δ>0, contradicting an n^(1+o(1)) conjecture. External mathematicians checked the argument and wrote companion remarks. It connects algebraic number theory to discrete geometry. This is novel mathematics, distinct from benchmark answers. The original model was internal; the announcement describes a selected discovery and subsequent investigation, not a public reproducible discovery service. [Announcement and linked proof/companion papers](https://openai.com/index/model-disproves-discrete-geometry-conjecture/).

**Ten advances, 1 August 2026.** OpenAI reports ten new results from an internal Astra version, including non-sofic groups, coding bounds, permanent lower bounds, and extremal graph questions. Humans prepared manuscripts with the model; the model subsequently formalized arguments in Lean. Reported discovery tokens would cost roughly $2,000 at Sol API rates—an equivalent token-pricing estimate, not full research cost or expected cost per arbitrary problem. [Announcement](https://openai.com/index/ten-advances-in-mathematics/), [253-page manuscript](https://cdn.openai.com/pdf/ten-proofs-oai.pdf).

**What can actually be reproduced from those ten advances.** The Apache-2.0 certificate repository includes theorem modules, pinned toolchain, Mathlib dependencies, and Comparator challenges. Its README specifies Lean 4.32.0 and `lake exe cache get`, then `lake build All`. This offers independently executable checking of supplied formalizations. It does not reproduce discovery from scratch or establish correct informal-to-formal translation by itself. [Certificate repository](https://github.com/openai/ten-proofs).

**Navier–Stokes, 8 September 2026.** OpenAI reports a forced three-dimensional blowup construction addressing Clay alternatives C/D, using an internal model more capable than GPT-6 Astra. Reported solution group: about 10,000 concurrent agents, 88 hours before resolution, another 17 for formalization, roughly 130 billion output tokens on Navier–Stokes. Human orchestration allocated resources, seeded agents with earlier Euler results, updated models, and consolidated intermediate insights. This is not weekend-scale reproducibility. [Provider announcement, updated 10 September](https://openai.com/index/navier-stokes-solution/).

**Navier artifacts and status boundary.** Actual artifacts exist: a 166-page manuscript and public Lean repository describing forced Navier–Stokes plus unforced Euler results. Repository uses Lean 4.34.0-rc2, Mathlib, Lake, and separate Comparator checking. I inspected descriptions, not mathematical soundness or builds. Clay's 11 September statement calls Navier–Stokes “apparently” settled and anticipates analysis; that is not a prize award or a claim this research pass independently verified it. Distinguish forced Navier–Stokes from unforced Euler and from practical simulation of real fluids. [Paper](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf), [Lean repository](https://github.com/openai/NavierStokesAndEuler), [Clay statement](https://www.claymath.org/news/navier-stokes-announcement/).

## Independent calibration: most important hackathon evidence

**Original FrontierMath.** Tiers 1–4 contain 350 author-created problems with automatically checkable closed-form answers. That output contract differs from proving a theorem. OpenAI funded the dataset and had access to portions; documented holdouts include 53 core solutions and 20 of 50 Tier-4 problems. Do not compare scores without version, tools, budget, and holdout details. [Epoch dataset description](https://epoch.ai/frontiermath/tiers-1-4/about).

**FrontierMath Erdős, announced 1 September 2026.** 68 significant conjectures, open as of August; one attempt/problem, $300 and 72-hour limits; accepted output must be verified Lean proof or disproof. Pre-release Astra scored 2/68, reported as 3%; GPT-5.6 Sol, GPT-5.5, Claude Fable 5.1, Claude Fable 5 each scored zero. Separate experiments changed budgets and agent configurations: five distinct problems solved across all runs, exceeding $220,000, compared with about $20,000 for the benchmark run. These additional successes are explicitly not the benchmark score. This sharply limits any promise that ample Fable credits imply solving an arbitrary famous problem. [Epoch announcement](https://epoch.ai/latest/announcing-frontiermath-erdos).

**Actual evaluation architecture.** The paper describes tool-using agents with shell, editor, budgets, delegation, memory, and todo lists; Lean, SageMath, Python, symbolic/numeric libraries; no network; an offline mathematical literature corpus. Comparator checks submissions separately, replays proof terms and restricts axioms. Formalization can consume most of the budget; missing library lemmas can hide real mathematical progress from an all-or-nothing score. More elaborate agents and literature access had not improved accuracy in earlier OEIS experiments discussed by the authors. [Paper](https://arxiv.org/pdf/2609.25050), [open harness](https://github.com/epoch-research/LeanOpenProblems).

**Why independent checking matters.** The harness separates agent sandbox from checker sandbox. Accepted results must pass Comparator rather than an agent-controlled “build passed” message. This prevents classes of proof-environment manipulation and separates candidate generation from trust. Formalized conjectures still need semantic review: valid proof of the wrong statement is not a solution. [Harness README](https://github.com/epoch-research/LeanOpenProblems).

## Hackathon proposals derived from evidence
These are design recommendations, not published empirical claims.

### 1. Counterexample-first research lab — strongest fit
Input a conjecture about finite graphs, integer sets, recurrences, or an algorithm. Agents search both for proof and counterexample. Python/Sage enumerates small cases; independent checker verifies each witness exactly. If conjecture fails, minimize witness and propose a repaired statement.

Demo: conjecture → failed small cases → smallest verified counterexample → revised conjecture → proved restricted version.

Why strong: finite witness is easy to inspect live, value survives failure to solve original conjecture, and exact checking avoids attractive-but-false prose. Do not call smallest-found witness globally smallest unless exhaustive search establishes it.

### 2. Lemma refinery
Start with a meaningful theorem and adjustable hypothesis, constant, or finite range. Generate nearby strengthenings, attack boundary cases, retain candidates, prove manageable lemmas in Lean. Every candidate has explicit assumptions and proof obligations.

Demo: find which assumption is necessary; show counterexample when removed; prove improved theorem under precisely stated conditions.

Why strong: models need not invent a major research agenda. User's actual “things to prove” can supply initial objects. Novelty is a separate literature-review question; success can be a new proof or verified special case even when theorem already known.

### 3. Proof referee with evidence
Input a proposed mathematical argument. Split into claims; attach references and dependencies; ask agents to attack specific steps with counterexamples, algebra checks, and citation inspection. Final output is a gap map with exact location, explanation, and minimal failing example where possible.

Demo: planted false “standard lemma” gets rejected despite plausible surrounding text. Repair it, then show downstream claims update.

Why strong: directly targets First Proof's observed failure modes. LLM consensus is not a correctness certificate. Score on adjudicated faults, missed faults, false alarms, and reviewer time—not confidence scores.

### 4. Conjecture-to-Lean contract checker
Give informal theorem plus formalization. Agents generate semantic test cases and compare assumptions, quantifier order, domains, coercions, and conclusion. Human confirms statement, then isolated checker verifies proof.

Demo: catch “positive” silently weakened to “nonnegative,” swapped quantifiers, or an added hypothesis that makes the target trivial.

Why strong: addresses trust boundary overlooked by theorem-proving demos. Useful even if prover supplied by another team.

### 5. Budget-aware research portfolio
Maintain five genuinely different strategies, not five paraphrased prompts. Allocate short exploration budgets; promote only approaches producing verified lemmas, exact witnesses, or a clearly reduced obstacle. Preserve failed approaches and prevent cyclic retries.

Demo: dashboard distinguishes conjectured / experimentally supported / proved / disproved / unresolved. Show wall time, token cost, verifier evidence, and human interventions.

Why strong: resembles real orchestration while making limits inspectable. Compare against one strong sequential agent at equal budget; “more agents” is a hypothesis to test, not an automatic improvement.

## Minimal proof-bearing architecture
1. Human locks problem statement, mathematical domain, baseline, and acceptable evidence.
2. Literature worker checks whether target already solved and records precise references.
3. Search workers pursue structurally different proof, construction, and counterexample directions.
4. Experiment worker executes reproducible exact computations; numeric results remain labelled evidence.
5. Referee audits weakest claims and verifies actual cited theorem statements.
6. Formalizer converts selected claims into checked certificates when feasible.
7. Independent checker runs with immutable target and restricted trust.
8. Human validates semantic match and significance; report scope and unresolved obligations.

Persist artifacts: original statement, each revised statement, scripts, seeds, counterexamples, proof files, dependencies, checker output, costs, model versions, human intervention log. Keep summaries as navigation, artifacts as evidence.

Best judging criteria: correctness of artifact; relevance to supplied target; novelty checked separately; reproducibility; cost and elapsed time; clarity of explanation. Give partial credit for useful exact counterexamples, certified special cases, and localized proof failures. Do not reward unverified claims of resolving named conjectures.

## Ten strongest starting links
1. [First Proof prompt appendix](https://cdn.openai.com/pdf/26177a73-3b75-4828-8c91-e8f1cf27aaa0/oai_first_proof.pdf)
2. [First Proof round-two independent referee report](https://1stproof.org/assets/docs/report.pdf)
3. [First Proof code/logs/submissions index](https://1stproof.org/second-batch.html)
4. [FrontierMath Erdős calibration](https://epoch.ai/latest/announcing-frontiermath-erdos)
5. [FrontierMath Erdős methods paper](https://arxiv.org/pdf/2609.25050)
6. [LeanOpenProblems reproducible harness](https://github.com/epoch-research/LeanOpenProblems)
7. [OpenAI real research collaboration cases](https://arxiv.org/abs/2511.16072)
8. [Unit-distance discovery and expert companion material](https://openai.com/index/model-disproves-discrete-geometry-conjecture/)
9. [Ten frontier Lean certificate projects](https://github.com/openai/ten-proofs)
10. [Navier–Stokes orchestration disclosure](https://openai.com/index/navier-stokes-solution/)
