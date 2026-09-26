# Astra approval: P2 C5

**FINAL APPROVE** the exact standalone `submission.md` identified below.

- SHA-256: `4125609499ae662beccdc3e9d1d81db9205293c8789cb70bb3cd34638012c25b`
- Size: 28,418 UTF-8 bytes; 28,398 characters.
- Claim: every ordering of the vertices of Q9 has at least 2,369 uphill paths, so U(Q9) >= 2369.
- Scope: written mathematical proof and exact finite integer certificates. This is not a claim of Lean formalization, organizer acceptance, or submission.

The proof directly assumes P <= 2368 and reaches a contradiction. It does not depend on the organizer's unpublished lower bound. I reviewed the exact path-count and forest identities; bounds on b, excess, and the core budget; the elementary distance-four code bound of 20; the local forest and code-deletion lemmas; and the application of Harper's explicitly stated, bibliographically cited vertex-isoperimetric theorem. The four included programs evaluate finite consequences of the proved reductions. They do not replace Harper's minimizing theorem with enumeration of initial segments.

The complete case inventory covers monochromatic sinks, mixed sinks with at most six cores, singleton minority sinks, two minority sinks, nine cores, and the remaining seven/eight-core cases for every delta from zero through seven. The final text explicitly disposes of the m=0 branch omitted from the mixed enumeration and includes the needed N(11)-11=37 check. Zero-neighbor deletion terms and the binomial convention are correct.

I extracted and ran all four Python blocks from this exact final Markdown. All exited successfully under Python 3.14.5 in 0.452852667 seconds total. The mixed inventory examines 1,110,562 degree multisets, leaving 134 after the basic necessary conditions, 20 after the triple-union condition, and zero after the strengthened cost condition. The last 20 rows have minimum strengthened costs 68, 71, or 72, exceeding the available 63. These checks use standard-library integer arithmetic, without solvers, timeout-based exclusions, network access, or external code files.

The singleton and nine-core arguments were independently cross-reviewed. Another reviewer independently reimplemented the monochromatic and mixed arithmetic checks and reproduced the results, then replayed all four final embedded blocks. I contributed research lemmas and a separate arithmetic implementation during development; this approval therefore records both my full final review and the separate cross-review evidence rather than claiming sole authorship-independent provenance for every lemma.

Earlier exploratory SMT code that conflated unknown/timeouts with infeasibility is not relied upon anywhere in this proof. Successful PDF compilation is not used as proof-validity evidence. The exact final text has no URLs; the required code and replay instructions are included inline. No remaining mathematical or finite-coverage objection was found.

Replay evidence: `astra-final-replay.json`. Separate reviewer evidence: `submission-four-block-replay.json`.
