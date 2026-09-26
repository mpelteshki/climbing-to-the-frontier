# Climbing to the Frontier: hackathon problem portfolio

Research date: 26 September 2026. Designed for a 24–48-hour vibe-coding hackathon, with Fable credits available for candidate code, conjectures, proof attempts, and critique. Rankings below are product judgments, not measured success probabilities. Two small calibration witnesses were independently checked during this task; no proof-assistant compilation was performed.

Best default: **a visual conjecture lab with graph counterexamples, followed by cap-set construction search**. Keep supplied-problem proof assistance as a third mode with an explicit supported mathematical domain. One working discovery loop beats nine disconnected mini-tools.

Local calibration evidence: the parent research task enumerated all labeled simple graphs on 1–6 vertices and found C₅ as the first counterexample by vertex count. It also found a nine-point cap in 𝔽₃³ after 100 seeded greedy runs and checked all 84 triples. This portfolio review independently recomputed the graph's independence number using vertex subsets and checked all 36 unordered cap pairs: both witnesses passed. Thus the product proof below gives 9ᵏ points in dimension 3k, improving the binary-cube baseline 8ᵏ. These are known calibration results, not novel research. [Seed script](../experiments/seed_experiments.py), [results](../experiments/seed-results.json).

## What counts as a result

Keep these labels separate in the interface and exported report:

1. **Tested:** no failure among the explicitly listed finite cases.
2. **Refuted:** an exact counterexample violates the original statement.
3. **Witness verified:** a finite construction satisfies every defining constraint; proves an existence/lower-bound claim only.
4. **Proved:** a complete argument exists; identify whether human-reviewed, checked by an exact certificate verifier, or checked by a proof-assistant kernel.
5. **Novel:** a separate literature and expert check supports originality. None of the known seed examples below are novel.

“Search found nothing” is never “proved.” “Best in this run” is never “world record.” A verified mathematical artifact can be valid while its proposed novelty is false.

## Ranked choices

| Rank | Build | Useful weekend result | Math burden | Search cost / risk |
|---|---|---|---|---|
| 1 | Graph conjecture → counterexample → repair | Exact graph witness, corrected statement, short proof | Low | Low per small candidate; exhaustive graph search grows rapidly |
| 2 | Cap-set construction explorer | Verified sets and evolving construction programs | Low–medium | Low for n≤5; steep growth by n=8 |
| 3 | Supplied-problem proof lab, starting with polynomial inequalities | Exact identity certificate or exact counterexample | Medium | Low for a narrow family; broad input scope is main risk |
| 4 | Forbidden-subgraph extremal lab | Dense valid graph plus certified upper-bound gap | Low–medium | Moderate; exact optimality quickly expensive |
| 5 | Recurrence invariant discovery | Conjectured formula → induction certificate | Medium | Low on chosen families; domain/sign mistakes |
| 6 | Ramsey coloring + proof certificates | Small exact Ramsey experiment with SAT/UNSAT evidence | Medium | Large cases explode; symmetry restrictions easy to misreport |
| 7 | Arithmetic-progression-free set builder | Integer witness and transferable heuristic | Low | Low–moderate; training-size overfitting |
| 8 | Schur coloring proof dashboard | Valid coloring and checked small impossibility proof | Medium | Low for k=2,3; historic frontier uses huge compute |
| 9 | Error-correcting code discovery | Verified code with explicit minimum distance | Medium | Low on small n; record tables need careful audit |

No dedicated GPU needed for these initial demos. Model credits help explore proposals, but deterministic evaluators, timeouts, and exact checking determine throughput. Set explicit per-candidate CPU and memory budgets.

## 1. Graph conjecture repair — recommended main project

**Exact calibration problem.** For a finite simple graph G with n vertices, let α(G) be its largest independent-set size. Test the deliberately false statement:

> Every triangle-free graph satisfies α(G) ≥ n/2.

The five-cycle C₅ is triangle-free and has α(C₅)=2<5/2. This is a known counterexample, chosen for calibration, not a discovery claim. A valid repair is: every **bipartite** graph satisfies α(G)≥⌈n/2⌉, since each side of a bipartition is independent and one side contains at least half the vertices.

**Engine.** Exact bitset independent-set enumeration for n≤14; triangle checking; BFS bipartiteness. Search by enumeration at n≤6, random graphs, edge mutations, and Fable-proposed constructive families. Restrict graph primitives instead of asking a model to fabricate numerical invariants. For larger n, a returned independent set proves a lower bound on α; it does not determine α exactly.

**90-second demo.** Enter statement → highlight domain and quantifiers → watch graph candidates → C₅ appears → click “Why false?” to show maximum independent sets → choose a proposed repair → show bipartition → render complete three-line proof → export original statement, witness, repaired statement, proof, and provenance.

**Frontier path.** A mathematician supplies a precisely stated graph inequality or a recently published conjecture packet. The agent searches for counterexamples, reduces witness size, extracts a recurring family, and attempts a theorem for a restricted class. Wagner demonstrated real counterexample discovery with reinforcement learning; later work systematizes alternative graph-building games. This establishes the workflow, not a promise that a randomly chosen open conjecture will fall. [Wagner, 2021](https://arxiv.org/abs/2104.14516), [Angileri et al., 2024](https://arxiv.org/abs/2406.12667).

**Weekend fallback.** Fully working known-conjecture calibration pack with deliberate false claims, known theorems, adversarial examples, exact checking, and proof provenance. Valuable even without novel mathematics.

**Main risk.** Repair by adding arbitrary assumptions makes a statement vacuously true. Require an explicit nonempty graph class, compare strength with the original, show examples satisfying the new hypothesis, and keep the original claim visible. Avoid spectral inequalities initially: floating-point eigenvalues are insufficient near a conjectured threshold.

## 2. Cap-set construction explorer

**Definition.** A cap set A⊆𝔽₃ⁿ contains no three **distinct** vectors x,y,z with x+y+z=0. Distinctness matters: x+x+x=0 for every x in characteristic three.

**Seed theorem.** {0,1}ⁿ is a cap of size 2ⁿ. Products of caps are caps, so a(n+m)≥a(n)a(m), where a(n) is the maximum cap size. Full proof below.

**Engine.** Fable proposes a priority function used by a fixed greedy constructor, or a bounded add/remove/swap policy. Keep evaluator immutable. Independently check all unordered distinct pairs x,y and reject if −x−y lies in A. Pair checking costs O(|A|²n), avoiding cubic enumeration. Start n=3,4,5; each full ambient space has 3ⁿ points. Save actual vectors, program, random seed, and verification report.

**Demo.** Show a 2D ternary grid for explanation; higher dimensions as coordinate tables and slices. Run baseline and evolved priorities side by side. Display exact size, rejected triples, checker pass, and best-so-far curve. Click “Generalize” to form a Cartesian product and show the theorem explaining why it works.

**Real-world precedent and status.** FunSearch evolved programs, using a fixed evaluator, and produced a 512-point cap in dimension eight. The 2025 primary paper *Greedy capsets* also identifies 512 as the then-best lower bound for a(8), while studying deletion-based search. This is a historical documented target, not a fully audited September 2026 world-record claim. [FunSearch](https://www.nature.com/articles/s41586-023-06924-6), [Greedy capsets](https://arxiv.org/abs/2502.06005).

**Frontier path.** Improve a documented construction or discover a simpler generalizable rule under fixed compute. A new finite cap establishes a lower bound; it does not prove optimality or determine the asymptotic growth constant. Note that *small complete caps* optimize a different quantity: complete means no point can be added, not largest. This distinction matters when reviewing 2026 literature. [Algebraic capsets](https://arxiv.org/abs/2602.05254).

**Weekend fallback.** Beat a naive priority on held-out seeds, reproduce a known construction, and explain product amplification. Report benchmark improvement honestly. Do not promise to beat 512 in a weekend.

## 3. Supplied-problem proof lab — polynomial inequality edition

**Input contract.** A rational polynomial p(x₁,…,x_d), explicit domain, and claim p≥0; optionally a parameter whose sharp value must be found. Keep arbitrary-text problems in an “unsupported until formalized” queue.

**Concrete seed.** Find the largest real λ such that, for every real x,y,z,

    x⁴+y⁴+z⁴ ≥ λ(x²y²+y²z²+z²x²).

Answer λ=1. Substituting x=y=z=1 forces λ≤1. At λ=1, the difference equals

    ½[(x²−y²)²+(y²−z²)²+(z²−x²)²] ≥ 0.

This demonstrates two complementary proof artifacts: a witness forbids larger parameters; an exact identity proves the boundary value.

**Engine.** Search rational test points and numerical minima for counterexamples; ask Fable for transformations or sums-of-squares decompositions; expand proposed identities with exact rational arithmetic. A numerical semidefinite solution can suggest a certificate, but require rational reconstruction and exact identity/positivity checks. Plain sums of squares are incomplete: failure to find an SOS is not a counterexample. Constraints require the appropriate multiplier certificates. [Magron, Safey El Din, Vu](https://arxiv.org/abs/2107.11825).

**Demo.** Paste inequality → confirm variables and domain → agent proposes λ=1.1 → exact point (1,1,1) rejects it → agent proposes λ=1 → proof identity expands → each square becomes clickable → export certificate and human-readable proof. Lean export is an advanced track, not a prerequisite for the working app.

**Frontier path.** Expert-provided parameterized inequality with unresolved sharp constant, or simplification of a large existing certificate. No generic inequality here is asserted to be a published open problem.

**Weekend fallback.** Three supported polynomial families with exact certificates and counterexample search. Do not label an unchecked prose proof as proved.

## 4. Forbidden-subgraph extremal lab

**Definition.** ex(n,C₄) is the maximum number of edges in a simple n-vertex graph containing no four-cycle, including non-induced four-cycles. Diagonals do not make a four-cycle admissible.

**Seed theorem.** Every C₄-free graph with n≥1 vertices and m edges satisfies

    m ≤ n(1+√(4n−3))/4.

Derive it by counting length-two paths; full proof below. The integral bound is the floor of the right-hand side.

**Engine.** Construct graphs under the invariant that every vertex pair has at most one common neighbor. Adding an edge updates common-neighbor counts. Exact SAT or integer programming for small n can certify an upper bound; otherwise show the seed bound and current witness side by side. Independent verification counts common neighbors from scratch.

**Demo.** Drag an edge; highlight the four-cycle it would create. Agent searches for more edges, then summarizes recurring structure. Show “verified 12-edge construction; upper bound 13” rather than “optimal.”

**Frontier path.** Narrow a verified finite gap or classify extremal constructions in a specified restricted family. No particular n is claimed open in this report: choose it only after checking current primary literature. Existing extremal graph research uses such constructive and counting arguments; small self-contained tasks are safer than a famous asymptotic claim. [Erdős–Simonovits primary paper](https://www.renyi.hu/~p_erdos/1967-05.pdf).

**Weekend fallback.** Rediscover a small optimum by complete enumeration, compare heuristic constructions against the universal upper bound, and generate the double-counting proof interactively.

## 5. Recurrence invariant discovery

**Definition.** Given a state transition T and initial state s₀, find an expression I whose value stays fixed, changes predictably, or proves an output property for every iteration.

**Concrete seed.** Fibonacci transition (a,b)↦(b,a+b), starting (0,1). Let I(a,b)=b²−ab−a². Then I(T(a,b))=−I(a,b); hence I(F_n,F_{n+1})=(−1)ⁿ. Full proof below. Merely calling I an invariant would be incorrect; it is a sign-flipping quantity. Adding a sign state s↦−s makes sI(a,b) constant.

**Engine.** Generate exact integer traces, fit low-degree polynomial templates with rational linear algebra, then verify the symbolic transition identity and initial condition. Ask Fable to select the template, explain the structure, or generalize the recurrence. Hold out longer traces to catch fitting mistakes, while remembering that symbolic induction supplies the proof.

**Demo.** A sequence grows → candidate formula matches samples → intentionally wrong formula fails later → transition identity proves the corrected formula for every n.

**Frontier path.** New restricted recurrence families or simpler invariants for supplied programs. Existing invariant-generation work already solves broad restricted classes, so polynomial discovery alone is not novelty. General invariant inference also has undecidability barriers; claim only the supported template class. [Amrollahi et al.](https://arxiv.org/abs/2206.06943), [Bayarmagnai et al.](https://arxiv.org/abs/2412.14043).

**Weekend fallback.** A small recurrence suite with exact induction certificates. Strong fit if hackathon judges require “things proved” rather than only finite constructions.

## 6. Ramsey coloring and certificate explorer

**Definition.** R(s,t) is the smallest N such that every red/blue edge coloring of K_N has a red K_s or a blue K_t.

**Seed theorem.** R(3,3)=6. On K₅, color a five-cycle red and its complement blue; neither color has a triangle. At any vertex of K₆, three incident edges share a color. If any edge among their other endpoints has that color, it completes a triangle; otherwise those three endpoints form the opposite-color triangle.

**Engine.** One Boolean variable per edge. For each s-subset forbid an all-red clique; for each t-subset forbid an all-blue clique. Independently verify SAT witnesses; obtain and check an UNSAT proof certificate for impossibility. Unchecked solver output is weaker than a checked certificate.

**Demo.** Toggle colors on K₅; expand to six vertices; show unavoidable triangle and animate the proof. Advanced demo searches R(3,4)-type calibration cases or constrained extensions of supplied graphs.

**Actual open frontier.** The current primary result located is 43≤R(5,5)≤46: Angeltveit–McKay prove the upper bound, and their March 2026 publication identifies 43 as the best lower bound. A valid coloring on 43 vertices would prove R(5,5)≥44. A failed search does not prove R(5,5)=43. [Primary paper](https://arxiv.org/abs/2409.15709), [2026 journal publication](https://onlinelibrary.wiley.com/doi/full/10.1002/jgt.70029).

**Weekend fallback.** Fully checked small Ramsey proofs and an honest frontier dashboard. Never promise to determine R(5,5). Proving nonexistence within a symmetry class proves only that restricted statement, unless symmetry reduction is itself exhaustive and justified.

## 7. Three-term-progression-free integer sets

**Definition.** Maximize |A| for A⊆{1,…,N} subject to no x<y<z in A satisfying x+z=2y.

**Seed theorem.** Numbers with k base-three digits, all digits in {0,1}, form a 3-AP-free subset of {0,…,3ᵏ−1} of size 2ᵏ. Translate by one for a subset of {1,…,3ᵏ}. To prove it, reduce x+z=2y modulo three: if y's last digit is zero then both endpoint digits are zero; if one then both endpoint digits are one. Remove the common last digit and repeat. Thus x=y=z.

**Engine.** Integer pair checks, greedy insertion, swap search, SAT for small N, and Fable-evolved ordering rules. Test different N and unseen seeds. Exact verification is cheap; proving maximum size is a separate task.

**Demo.** Selected integers light up on a number line; forbidden triples appear as evenly spaced arcs. Show the digit construction, then a search improvement, then whether the rule transfers to larger N.

**Frontier path.** Finite constructions or improved bounded-compute heuristics. A 2025 primary empirical study specifically investigates how asymptotic constructions perform at small sizes; 2024 work improved Behrend-type lower bounds. Thus use their actual constructions as baselines, not only naive greedy. [Gasarch–Glenn–Kruskal](https://arxiv.org/abs/2501.01634), [Elsholtz–Hunter–Proske–Sauermann](https://arxiv.org/abs/2406.12290).

**Weekend fallback.** Known digit proof, verified larger examples, honest benchmark table. Do not present a finite improvement as an asymptotic theorem.

## 8. Schur colorings

**Definition.** S(k) is the largest N admitting a k-coloring of {1,…,N} with no monochromatic solution a+b=c. Here a=b is allowed. This convention prevents off-by-one confusion with versions defining the first unavoidable N.

**Seed theorem.** S(2)=4. Coloring {1,4} red and {2,3} blue works. For {1,…,5}, assume 1 red; then 2 blue, 4 red, 5 blue. If 3 red, 1+3=4 is monochromatic; if 3 blue, 2+3=5 is monochromatic.

**Engine.** SAT coloring variables with exactly one color per number; for every a+b=c and color, forbid all three membership literals. Repeated operands must be handled correctly. Independently check colorings and UNSAT certificates.

**Demo.** Color-number strip; animate forbidden sums; show a valid coloring at N and a certificate of impossibility at N+1.

**Real-world precedent.** S(5)=160 was proved by massively parallel SAT solving; the certificate was about two petabytes and checked with a formally verified checker. This is an example of proof-producing computation, not a weekend compute template. [Heule, Schur Number Five](https://arxiv.org/abs/1711.08076), [author's proof archive](https://www.cs.utexas.edu/~marijn/Schur/).

**Frontier path.** Better constrained constructions or shorter certificates. Do not promise S(6); this report does not audit the latest exact S(6) bounds. The already solved S(5) is a reproduction target only.

**Weekend fallback.** Complete S(2) proof and a small k=3 SAT experiment with downloadable artifacts.

## 9. Binary error-correcting codes

**Definition.** A₂(n,d) is the largest size of a set C⊆{0,1}ⁿ in which distinct words differ in at least d coordinates. Do not silently restrict to linear codes; that is a different search domain.

**Seed theorem.** If minimum distance is at least 2t+1, Hamming balls of radius t around codewords are disjoint. Therefore

    |C| Σᵢ₌₀ᵗ binom(n,i) ≤ 2ⁿ.

If two balls met, their centers would be at distance at most 2t by the triangle inequality, contradiction.

**Engine.** Model a code as a clique in the compatibility graph on binary words, with an edge whenever Hamming distance is ≥d. Use bit operations for verification, greedy/local search for witnesses, and exact methods for small instances. Fable proposes structured constructors or prioritization rules.

**Demo.** Send a small message encoded as a codeword, flip t bits, recover by nearest neighbor, then show the mathematical certificate establishing guaranteed correction.

**Frontier path.** Improve a verified table gap or produce a simpler construction. Brouwer's primary-maintained table documents exact values and unresolved intervals, but the accessible page includes older updates; no table gap is certified here as still open in September 2026. Cross-check chosen parameters before any novelty claim. [Brouwer's code table](https://aeb.win.tue.nl/codes/binary-1.html).

**Weekend fallback.** Construct a small code, verify all pairwise distances, demonstrate correction, and show the packing bound. Avoid extrapolating a random-noise demo into a guarantee beyond the proven correction radius.

## Three complete seed proofs

These are known elementary results, provided as checked-by-reasoning mathematical seeds. They have not been compiled in Lean or another proof assistant in this task.

### A. Cap products and the 2ⁿ construction

Suppose A⊆𝔽₃ⁿ is a cap. If a₁+a₂+a₃=0 with aᵢ∈A, either all three are distinct or some two are equal. The first case is forbidden. In the second, say a₁=a₂, the equation gives a₃=−2a₁=a₁. Thus every zero-sum triple in A is constant.

Now let A and B be caps. If three elements (aᵢ,bᵢ) of A×B sum to zero, the coordinate triples each sum to zero. The preceding argument gives a₁=a₂=a₃ and b₁=b₂=b₃. Therefore the three product elements coincide. So A×B is a cap, with size |A||B|.

The two-point set {0,1}⊂𝔽₃ is a cap. Repeated products give {0,1}ⁿ and size 2ⁿ. Consequently a(n+m)≥a(n)a(m).

**What this proves:** every verified cap can generate an infinite sequence of larger caps via products. **What it does not prove:** optimality of those caps, or a new record without comparison against other constructions.

### B. A universal C₄-free edge bound

Let G be C₄-free with n≥1 vertices, m edges, and degrees d₁,…,d_n. Any two distinct vertices have at most one common neighbor: two common neighbors would form a four-cycle. Counting unordered pairs of neighbors at each vertex gives

    Σᵢ binom(dᵢ,2) ≤ binom(n,2).

Because Σdᵢ=2m and Σdᵢ²≥(Σdᵢ)²/n=4m²/n,

    (4m²/n−2m)/2 ≤ n(n−1)/2.

Multiply by 2n:

    4m²−2nm−n²(n−1) ≤ 0.

The nonnegative root of the corresponding quadratic is n(1+√(4n−3))/4. Therefore m is at most that root, and at most its floor because m is integral.

**Product lesson:** search finds a lower-bound witness; counting supplies an upper bound; only a matching pair establishes an optimum.

### C. Fibonacci's sign-flipping polynomial identity

Define F₀=0, F₁=1, Fₙ₊₂=Fₙ₊₁+Fₙ, and I(a,b)=b²−ab−a². Direct expansion gives

    I(b,a+b)
      = (a+b)²−b(a+b)−b²
      = a²+ab−b²
      = −I(a,b).

At (F₀,F₁)=(0,1), I=1. Each transition multiplies I by −1, so induction proves

    Fₙ₊₁²−FₙFₙ₊₁−Fₙ²=(−1)ⁿ  for every n≥0.

Equivalently, Fₙ₊₁²−FₙFₙ₊₂=(−1)ⁿ. The initial state and transition identity are both necessary; fitting any finite prefix alone does not prove the statement.

## Suggested 48-hour cut

- Hours 0–6: graph problem schema; exact invariant checker; known true/false calibration pack; witness format.
- Hours 6–14: visible search and C₅ counterexample journey; verifier output; statement revision history.
- Hours 14–24: Fable proposes graph constructors and repairs in bounded batches; immutable checker rejects invalid output; persist runs.
- Hours 24–34: add cap-set module using the same proposal → evaluate → retain → explain loop. Start n≤5.
- Hours 34–42: export proof/witness reports; replay runs; test false positives, timeouts, duplicated proposals, inconsistent domains, empty output, and malformed artifacts.
- Hours 42–48: complete demo script and use remaining time for one expert-provided problem packet. No broad “solve any math problem” parser.

For a 24-hour event, finish only the graph flow. Optional Lean integration follows after the complete exact-witness product works.

## Research boundaries and novelty checklist

Before calling anything new, pin the exact statement, quantified domain, baseline construction, primary citation/version, candidate artifact, independent verification command, complete compute budget, and literature check date. Check whether a reported “new” result is a known special case, a relabeling, an equivalent construction, or a weaker bound.

This search found usable primary evidence for historical method precedents and the stated Ramsey interval. It did **not** establish exhaustive September 2026 novelty status for every cap, code, extremal-graph, Schur, or integer-progression parameter. That is why most frontier routes above are scoped search directions rather than invented currently-open numerical targets.
