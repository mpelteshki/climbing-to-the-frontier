# C6: general bound

**Status: Not solved — partial written results; no Lean.** Work on this open cell was resumed on user direction on 2026-09-26. The [partial results](partial-results.md) contain complete written proofs of:

- an averaging lemma: the C6 bound at $N$ follows from the bound at $N-1$ whenever $d$ divides $N$ (Theorem 2.3). With C5 this proves the $(N,d)=(6,3)$ case, $S\le6\pi$ (Corollary 2.4).
- an explicit bound for all $d\ge2$, $N\ge d+2$: $S\le\frac\pi2\binom N2\left(1-\frac{4}{(d+1)(d+2)}\right)$ (Theorem 2.5). It equals the conjectured value only for $N=d+2$ and $(6,3)$.
- structural lemmas (row bound, line deletion, orthogonal components, kernel forcing) and a reduction of the family $N=d+3$ to connected configurations with maximum degree three, distinct lines, no essential line, light vertices and no long degree-two chains (Theorem 4.1, Lemma 4.2).

No $\mathrm{C6}(N,d)$ with $N\ge d+3$ other than $(6,3)$ is proved, so no infinite family beyond C5 is claimed. The connected sparse case for $N=d+3$ is open (Question 4.4).

Numerical evidence: [explore.py](explore.py) reproduces the conjectured minimum deficiency for $21$ small pairs $(N,d)$ and exhibits non-axis equality configurations; results in [explore-results.json](explore-results.json). [local_ineq.py](local_ineq.py) samples the local projection inequalities discussed in Remark 4.3. These are numerical experiments, not proofs.

No submission to the hackathon platform has been made or is authorized.
