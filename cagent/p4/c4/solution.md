# P4 C4: range proof and exact method audit

Task source: [Every k up to 12](https://hackathon.bainsa.ai/p/p4/c4), checked on 2026-09-26. This document is a proposed solution, not an organizer acceptance or platform submission.

## Claim and meaning of the computation

For every integer k with 2 ≤ k ≤ 12, every k pairwise disjoint integer congruence classes with positive moduli contain a pair whose moduli have gcd at least k. Repeated moduli are allowed.

A complete Lean proof is `ThroughTwelve.solution` in [ThroughTwelve.lean](../lean/ProofPursuit/P4/ThroughTwelve.lean). Its theorem has no search-completion or smaller-case premises. The supplied `Statement` uses actual disjointness of integer sets. Bézout/CRT, normalization, the density inequality, enumeration correctness, and the concrete k=11 and k=12 refutations are proved inside the package. Lean 4.34.1 plus bundled Std suffices. Both a fresh build and a separate kernel replay passed; [verification record](../verification.md) gives commands and axiom audit.

For the requested audit at 9–16, distinguish two stages:

1. **Necessary modulus tests:** enumerate finite normalized modulus multisets, apply every-subset density and the explicitly described extra minimal-counterexample conditions.
2. **Actual residue decision:** decide every remaining multiset by complete finite residue search, with independently checked refutation trees and concrete witnesses proving minimum obstruction cardinalities.

The [reduction and pruning proof](../audit/reduction-proof.md) supplies the mathematical justification. The [manifest](../audit/MANIFEST.md) locates exact data and code. The residue tests concern all assignments, not a sample and not a bounded search over the original unbounded integers: the finite residue normalization is proved in that document.

## Exact results

| k | Raw density-only lists | Lists after extra modulus tests | Lists still undecided after residue certificates |
|---:|---:|---:|---:|
| 9 | 0 | 0 | 0 |
| 10 | 0 | 0 | 0 |
| 11 | 0 | 0 | 0 |
| 12 | 0 | 0 | 0 |
| 13 | 51 | 1 | 0 |
| 14 | 0 | 0 | 0 |
| 15 | not certified in an unpruned run | 30 | 0 |
| 16 | not certified in an unpruned run | 77 | 0 |

The chosen method at 15 and 16 includes extra necessary-condition pruning during enumeration. Its complete final survivor sets are the `reduced_survivors` arrays in [k=15](../audit/run-15-strong-60.jsonl) and [k=16](../audit/run-16-strong-300.jsonl). These files exhibit every modulus with multiplicity. For 9–14, the exact raw and reduced arrays are in [run-9-14.jsonl](../audit/run-9-14.jsonl). A strong run's intermediate `base_survivors` must not be described as the complete raw density-only set.

The second implementation chooses compatible distinct values and then their multiplicities, whereas the first grows occurrence lists from anchor triples. The recorded [elementwise comparison](../audit/compare-independent-9-16.jsonl) has empty symmetric differences for every claimed final set. Fresh replay records node counts and wall clocks, and checks those counts against the baseline.

## Why no surviving modulus list remains undecided

At k=13 the single reduced list is

`[10,10,10,10,10,12,12,12,12,24,36,40,45]`.

Its subset `[10,10,10,10,10,12,45]` is impossible. Disjointness from the 12-class forces all five 10-class residues to have the other parity. Pairwise disjointness among the 10-classes makes those five residues distinct modulo 10. They therefore exhaust all residues modulo 5. The 45-class meets one of them because its gcd with 10 is 5. This proves impossibility without computation. The 239 explicit assignments for every distinct nonempty submultiset of size at most six prove that seven is the smallest obstruction cardinality inside the full list. Both the impossibility and minimality are also Lean-certified in `Survivor13` and `Minimality13`.

At k=15 and 16, [global-minima-claims.jsonl](../audit/global-minima-claims.jsonl) gives each of the 107 lists, its individual obstruction, and its minimum cardinality. Every obstruction has a complete refutation tree; there are 59 distinct trees and 40,292 nodes. Every smaller submultiset has an explicit residue witness, checked directly by the CRT gcd criterion. Thus no smaller submultiset can force the negative decision. Repeated values are treated as separate positions when defining subfamilies, and duplicate submultisets share witnesses only because equal modulus multisets have exactly the same realizability question. The zero-entry subfamily is trivially realizable.

These facts also extend the mathematical conclusion inductively to k=16: assume a least failing size in 13–16, apply its justified finite reduction, and obtain a list which the exhaustive computation and residue certificates exclude. Every invocation of a smaller-size theorem is thereby discharged. This extension is computationally certified, not claimed to be formalized in Lean.

## Source discrepancy, tested rather than assumed

O'Bryant's [paper](https://arxiv.org/abs/math/0604347), §4.4, reports no survivors through 19 from the displayed pair-gcd and every-subset density machinery. The explicit thirteen-list above passes those tests: every pair gcd is in [2,12], and all 8,178 position subsets of cardinality at least two satisfy the canonical integer density inequality. Independent Python checking and `DensityAudit13.every_sublist_passes` establish this. Consequently that reported emptiness claim, interpreted as the stated necessary-condition tests, is incorrect. Our exhibited survivor is not a counterexample to the disjoint-congruence conjecture; its residue impossibility was proved above. We do not claim to have identified the cause of the paper's computational discrepancy.

During our own audit we also found an implementation error: an old residue search compared an original modulus to an effective residue bound when applying equal-modulus symmetry. The corrected search compares original moduli with each other. Independent saved-tree replay already used the correct condition. The correction and reruns are recorded openly; no old search-only UNSAT answer is being treated as sufficient evidence.
