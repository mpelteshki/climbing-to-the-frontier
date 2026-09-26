# C4: partial, not solved

The cell requires all cases through 12 and an exact account of the chosen method's survivors at every size 9–16. The published Lean range is currently **2–9**. Cases 10–12 and the complete 9–16 method audit are not yet certified.

## Unconditional case 9

`ThroughNine.nine` proves the actual disjoint-congruence statement. Assume all pairwise gcds are below 9. If every modulus is even, five of the nine residues share parity; dividing that subfamily by two contradicts the already-proved five-class case. Hence some modulus is odd.

Deleting any one class and applying the eight-class theorem gives a pair with gcd 8. Therefore at least three moduli are divisible by 8. Each shares an odd prime from {3,5,7} with the odd modulus. Two such anchors cannot share that prime: their gcd would be at least 24. The three anchors thus account for the three primes separately; a fourth anchor is impossible.

Remove the anchors carrying 5 and 7. The seven-class theorem gives a pair with gcd 7 in the remaining seven classes: gcd 8 is impossible because only one 8-anchor remains. Both moduli in that pair must be odd, since each shares 7 with the removed 7-anchor. Both must share an odd prime with the removed 5-anchor; its only available prime from {3,5,7} is 5. Their gcd is therefore divisible by 35, a contradiction.

Dependencies are discharged by existing proofs of cases 5, 7 and 8. No modulus-normalization assumption is needed for this argument.

## Formal infrastructure

- `Reduction.compress_counterexample`: compress moduli to gcds with a positive common multiple of all positive integers below k; preserve positivity, actual disjointness and every pairwise gcd.
- `CommonPrime.no_common_divisor_of_smaller_statements`: assuming all smaller cases, a counterexample cannot have any common divisor p≥2 across all moduli.
- `density_bound_compressed`: the sum of `M / gcd(m_i,M)` is at most M when every pairwise gcd divides M. The proof counts distinct residues, not approximate rational values.
- `FiniteSearch.search_true_iff`: exact correctness of a finite search with prefix pruning, allowing repeated values. This alone does not certify any concrete search result.

## Exact thirteen-modulus audit

Consider

```
[10,10,10,10,10,12,12,12,12,24,36,40,45].
```

`DensityAudit13.every_sublist_passes` checks every sublist using the lcm of its pairwise gcds as M. It proves the integer density inequality for every sublist with at least two entries. All computations run through Lean's kernel using `decide`, with no native evaluation axiom.

`Survivor13.candidate_impossible` proves that no choice of integer residues makes these thirteen classes pairwise disjoint. Its seven-class obstruction is `[10,10,10,10,10,12,45]`: the 12-class forces the five 10-classes to share parity. Their residues modulo 5 must then be distinct. They occupy all five residue values, so the 45-class cannot avoid them.

`Minimality13.every_small_sublist_admissible` proves every sublist of size at most six has an actual disjoint residue assignment. Its embedded certificate contains witnesses for all 239 distinct nonempty submultisets of those sizes, plus the empty list. Thus seven is the smallest possible obstruction size within this thirteen-modulus list, not merely an inclusion-minimal example.

This separates density admissibility from actual residue realizability. It also contradicts the claim in §4.4 of [O'Bryant, arXiv:math/0604347v2](https://arxiv.org/abs/math/0604347) that its stated necessary-condition search has no survivors through 19. It does **not** refute the disjoint-congruence conjecture or, by itself, the paper's final theorem. A full audit of every requested size remains unfinished.

## Reproduce

From `cagent/p4/lean`:

```sh
lake build ProofPursuit.P4.ThroughNine ProofPursuit.P4.Density ProofPursuit.P4.FiniteSearch ProofPursuit.P4.Survivor13 ProofPursuit.P4.Minimality13
lake env leanchecker ProofPursuit.P4.ThroughNine
lake env leanchecker ProofPursuit.P4.Density
lake env leanchecker ProofPursuit.P4.FiniteSearch
lake env leanchecker ProofPursuit.P4.Survivor13
lake env leanchecker ProofPursuit.P4.Minimality13
```

`Minimality13` imports and checks `DensityAudit13`. Only Lean 4.34.1 and bundled Std are required. See [verification record](../verification.md). No hackathon-platform submission was made.
