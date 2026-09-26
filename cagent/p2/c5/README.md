# P2 C5 — Improve the Q9 bounds

**Not solved.** Work resumed on explicit user request on 2026-09-26.

The live cell states that Q9 has 512 vertices and 2304 edges, with organizer bounds 2368 ≤ U(Q9) ≤ 2400; the lower bound is unpublished. A complete answer must either prove U(Q9) ≥ 2369 or give an explicit full labelling with at most 2399 uphill paths.

Parallel work covers direct ordering search, code-based constructions, lower-bound structure, finite constraints, primary-source research, and independent verification. Research results are not a solved-cell claim. C6's exact-value problem remains outside this task.

## Verified supporting results

- The existing 2400-path code construction is reproduced exactly; it is not an improvement.
- [A self-contained proof that A(9,4)=20](research/construction/even_code_bound.md) uses character-square identities and parity. This excludes independent feedback vertex sets below 236, but does not alone prove the requested path bound.
- An independent [path verifier](research/verification/verify_order.py) uses descending suffix-path counts and cross-checks endpoint counts, cube edges, and the structural budget.

Current candidate search and lower-bound case analysis remain incomplete. No supporting lemma is presented as a C5 solution.
