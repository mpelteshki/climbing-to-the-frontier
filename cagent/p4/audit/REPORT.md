# P4 finite-search audit (Python, not a Lean proof)

This folder gives an exact integer enumeration and independent checks for the
necessary modulus conditions of a **least-size** counterexample to the
disjoint-congruence-classes conjecture. Together with the [finite-reduction and pruning proof](reduction-proof.md),
exact outputs, and replay evidence, it forms a computational exhaustiveness
certificate. The adjoining `cagent/p4/lean` package separately records Lean
formalization; a Python execution is not a Lean theorem.

## Source and finite reduction

Kevin O'Bryant, [*On Z.-W. Sun's Disjoint Congruence Classes Conjecture*,
arXiv:math/0604347v2](https://arxiv.org/pdf/math/0604347), Proposition 2,
Lemma 5, and Lemma 6, gives the following necessary conditions. Suppose `k`
is the least number of pairwise-disjoint congruence classes with every pair
of moduli having gcd `< k`; among such examples minimize the sum of moduli.
Then every modulus `m_i` divides `L_k = lcm(1,...,k-1)`, has at least two
distinct prime factors, and every pair gcd lies in `[2,k-1]`. At least three
moduli are divisible by `k-1`. If exactly three are, at least two *other*
moduli are divisible by `k-2`. Every maximal prime power present in one
modulus is present in another. For `7 <= k <= 30`, any prime `p >= k/2`
which occurs in a modulus occurs in exactly two. These are Lemma 6 items
1–6 and 8, under its minimality hypotheses.

For any position subset `S` of at least two moduli, let
`M_S = lcm{gcd(m_i,m_j): i<j in S}`. The source's Lemma 5 rules out disjoint
residues if `sum_{i in S} M_S/gcd(m_i,M_S) > M_S`. All arithmetic here is
integer arithmetic; no floating-point comparison is used. It suffices to
check this minimal `M_S`: if `M` is any larger multiple, each
`gcd(m_i,M)` is a multiple of `gcd(m_i,M_S)`, so the fractional sum cannot
increase. This explains why checking one `M_S` per subset covers Lemma 6(7).

`enumerate.py` constructs every divisor of `L_k` with at least two prime
factors. It chooses the three smallest `k-1`-divisible moduli by
`combinations_with_replacement`, then appends nondecreasing values; later
anchors must be at least the third chosen anchor. Thus every eligible
multiset, including repeated anchors, has a unique search path. Pair-gcd
failures reject a path. Density failures on a prefix or triple reject it
because each is an actual position subset of every extension. At a leaf,
every position subset of sizes 3 through `k` is checked. Pairs already pass
automatically since their gcd is at least 2. `--strong` additionally rejects
partial paths only when the remaining candidate pool makes Lemma 6's prime
power support, large-prime count, or exact-three-anchor rule impossible.
These rules can reject a tuple that passes density, so the strong run's
`base_survivors` is **not** the raw density-only survivor set.

`clique.py` independently factors divisors of `L_k` by trial division,
constructs a graph on distinct compatible modulus values, selects a clique
of values, and assigns each value a multiplicity. A value `d >= k` has
multiplicity at most one because repetition gives gcd `d >= k`; a value
`d < k` has multiplicity at most `d` by the density bound on identical
classes. Anchor and nonanchor values are handled as two graph stages. This
does not reuse the anchor-triple search. It applies the same mathematical
necessary conditions and produces sorted multiset lists for elementwise
comparison. In strong mode the two implementations can have different
intermediate `base_survivors` because their partial pruning differs; their
final `reduced_survivors` must agree. The second implementation completed
through `k=16`. `compare-independent-9-16.jsonl` records an empty symmetric
difference for the exact raw sets at 9–14 and exact reduced sets at 15–16.

## Observed enumeration

| `k` | Complete run | Raw density survivors | Survivors after Lemma 6 extras | Further residue result |
| --- | --- | ---: | ---: | --- |
| 9 | yes | 0 | 0 | no tuple remains |
| 10 | yes | 0 | 0 | no tuple remains |
| 11 | yes | 0 | 0 | no tuple remains |
| 12 | yes | 0 | 0 | no tuple remains |
| 13 | yes | 51 | 1 | seven-modulus contradiction below |
| 14 | yes | 0 | 0 | no tuple remains |
| 15 | yes, strong mode | not measured in complete raw run | 30 | all 30 fail exact residue CSP |
| 16 | yes, strong mode | not measured in complete raw run | 77 | all 77 fail exact residue CSP |

The 51 raw `k=13` lists are in `run-9-14.jsonl`; `audit-9-14.json` gives
one explicit violated prime-power support clause for each of 50 lists.
The sole survivor after all implemented Lemma 6 clauses is
`[10,10,10,10,10,12,12,12,12,24,36,40,45]`. It passes the density
inequality for every one of its 8,178 position subsets of size at least two,
as checked by a separate direct subset loop. Its pair gcds lie in `[2,12]`,
and both the lcm of all moduli and the lcm of all pair gcds equal 360.

This is a concrete discrepancy with the paper's §4.4 statement that its
Mathematica `Grow` returns `False` through `k=19` under the listed pair-gcd
and every-subset density tests. The paper's main theorem is not contradicted:
the surviving modulus list cannot be assigned pairwise-disjoint residues.
No cause for the discrepancy in the reported computation has been established.

The seven-element submultiset `[10,10,10,10,10,12,45]` is impossible:
disjointness from the `12`-class forces all five `10`-class residues to have
the parity opposite its residue. Since the five `10`-classes are pairwise
disjoint, their residues exhaust that parity modulo 10 and therefore all
five residues modulo 5. A `45`-class must meet one of them, because
`gcd(10,45)=5`. This subset passes the density test. It is smallest by
cardinality **within the full 13-list**: `audit.py` finds and verifies a
disjoint residue assignment for every distinct submultiset of sizes 1–6.
There are respectively 6, 17, 32, 48, 63, and 73 of those. The 239
position-independent witnesses are recorded in `audit-9-14.json`. In
particular, each single deletion from the seven-list has a concrete witness:

| Deletion | Remaining moduli | One residue list |
| --- | --- | --- |
| one `10` | `[10,10,10,10,12,45]` | `[0,2,4,6,1,3]` |
| `12` | `[10,10,10,10,10,45]` | `[0,1,2,3,5,4]` |
| `45` | `[10,10,10,10,10,12]` | `[0,2,4,6,8,1]` |

The full `k=15` and `k=16` strong-run survivor lists are in
`run-15-strong-60.jsonl` and `run-16-strong-300.jsonl`. The independent
residue CSP in `audit.py` assigns each modulus `m_i` only the residues
modulo `R_i=lcm_{j != i} gcd(m_i,m_j)`, which divides `m_i`. This is
complete: every original residue restricts to one such value, and every
such value can be used as an original residue. It checks exact pair-gcd
inequalities, fixes one residue to zero by common translation, and orders
equal-modulus copies by residue because they can be permuted. It found
no feasible assignment for any of the 30 or 77 final lists. The files
`global-minima-claims.jsonl` and `global-minima-facts.jsonl` give the
stronger smallest-cardinality obstruction result described below. These
unsatisfiability claims are independently replayed finite certificates.
Their completeness relies on the written residue-normalization proof and
the branch-by-branch verifier, not on an unexamined search return value.

### Globally smallest obstructions inside each survivor

`global_minima.py` checks submultisets in increasing cardinality and caches
results across all 107 reduced survivors. Its bounded run completed in
15.784 seconds, recording 20,436 distinct submultisets in
`global-minima-facts.jsonl`. Every SAT entry carries a residue list. For
each original survivor, `global-minima-claims.jsonl` names one UNSAT
submultiset of the *smallest possible cardinality* within that survivor.
The independent `verify_global_minima.py` recomputes the 107 UNSAT outcomes,
checks every stored SAT witness by pair gcd, and confirms that every one
of the 19,704 distinct smaller submultisets needed for those minimality
claims has a stored SAT witness. Its result is in
`global-minima-verification.json`.

| `k` | Minimum-size obstruction distribution |
| --- | --- |
| 15 | size 6: 16 lists; size 7: 11; size 12: 3 |
| 16 | size 7: 16 lists; size 8: 2; size 9: 39; size 10: 11; size 11: 9 |

There are 59 distinct minimum obstructions among the 107 lists.
`minimum-refutations.jsonl` exports a complete finite residue-search tree
for each distinct obstruction, only 40,292 nodes in total. In its tree
grammar, `0` is a dead leaf; `[i, children]` branches on modulus position
`i`, with one child for **every** currently admissible residue in ascending
order. The residue values are implicit and recomputed by the independent
`verify_refutations.py`. That checker confirmed all 59 trees, every branch,
and every dead leaf; see `minimum-refutations-verification.json`.
For Lean ingestion, `cert-strings.json` gives the same 59 trees as compact
preorder strings (83,325 bytes total). `A` is a dead leaf; a branch is
`B<hex-index><hex-arity>` followed by exactly that many child trees, where
each hex field is one uppercase digit. Maximum observed index is 11 and
maximum arity is 14. `verify_cert_strings.py` requires full input
consumption, reconstructs each original tree exactly, and reruns the
semantic checker; `cert-strings-verification.json` records success.

The tree search uses three sound reductions that a later Lean proof must
establish explicitly. First, the residue for `m_i` ranges only over
`R_i = lcm_{j != i} gcd(m_i,m_j)`, a divisor of `m_i`; every pair condition
depends only on its residue modulo a divisor of `R_i`, and every reduced
residue is an actual residue modulo `m_i`. Second, all residues can be
translated by the first residue, making position 0 have residue 0 while
preserving every pair difference modulo its gcd. Third, positions with
equal modulus can be permuted so their residues are strictly increasing:
their constraints with all other positions are identical. The first
position remains smallest among copies of its modulus after translation,
since it has residue 0 and all other copies have distinct nonzero residues.
The Python replay is a checkable search artifact, **not** a Lean proof of
these normalizations or of the full theorem.

As a nonvacuous positive control, the same base enumerator is run with
`gcd_cap=7` and `target_length=6`. Its output includes six copies of
modulus 6. The residue list `[0,1,2,3,4,5]` makes those six classes
pairwise disjoint; pair gcd 6 is strictly below the cap 7 and the density
sum is exactly 1. The counterexample-minimality clauses are inapplicable
to this separate parameter choice. The ordinary `k` runs always use
`target_length=k` and `gcd_cap=k`.

## Reproduction and limitations

These runs used Python 3.14.5. From the repository root, replay the packaged
results with these focused checks:

```sh
python3 cagent/p4/audit/audit.py cagent/p4/audit/run-9-14.jsonl
python3 cagent/p4/audit/compare_independent.py --tuple-runs cagent/p4/audit/run-9-14.jsonl cagent/p4/audit/run-15-strong-60.jsonl cagent/p4/audit/run-16-strong-300.jsonl --clique-runs cagent/p4/audit/clique-9-12.jsonl cagent/p4/audit/clique-13-14.jsonl cagent/p4/audit/clique-15-strong.jsonl cagent/p4/audit/clique-16-strong.jsonl
python3 cagent/p4/audit/verify_global_minima.py --runs cagent/p4/audit/run-15-strong-60.jsonl cagent/p4/audit/run-16-strong-300.jsonl --facts cagent/p4/audit/global-minima-facts.jsonl --claims cagent/p4/audit/global-minima-claims.jsonl
python3 cagent/p4/audit/verify_refutations.py cagent/p4/audit/global-minima-claims.jsonl cagent/p4/audit/minimum-refutations.jsonl
python3 cagent/p4/audit/verify_cert_strings.py cagent/p4/audit/minimum-refutations.jsonl cagent/p4/audit/cert-strings.json
```

To regenerate the enumeration, run `enumerate.py` and `clique.py` with the
`k` values and time limits in their saved JSONL records. Use
`--target-length 6` with `enumerate.py 7` for the positive control.
`global_minima.py` resumes existing fact and claim files; give it fresh
output paths to regenerate them. `export_refutations.py` and
`encode_cert_strings.py` regenerate the two tree encodings.

For the least-counterexample exclusions at 24 and 30, no search is needed:
`k-1` is respectively the prime 23 or 29. Lemma 6(5) demands at least
three moduli divisible by it, while Lemma 6(8) allows exactly two when
it occurs (`k <= 30` and `k-1 >= k/2`). These are conditional exclusions
of a *least* counterexample at 24 or 30; they do not independently prove
the conjecture at those sizes without earlier sizes. The reconstructed
[known-cases proof](../c5/known-cases.md) gives the full conditional
argument and its scope.

Only output with `"complete": true` licenses an exhaustive claim. Earlier
exploratory output omitted repeated anchors and is excluded from this
package. Timed-out runs do not imply empty survivor sets. No size above
16 was searched here. The 24/30 conditional argument has not been
converted into a Lean certificate in this folder.

## Correction and fresh replay

The old `audit.py` compared an original modulus with an effective residue bound when imposing equal-modulus ordering. It now compares original moduli `xs[j] == xs[i]`. Freshly regenerated 107 minimum claims, 20,436 facts including their statuses and concrete witnesses, and the k=13 audit match the earlier artifacts exactly. The independent tree checker always used the correct condition and checks all 59 refutations. Our initial diagnosis of unsoundness was too strong: those unequal original moduli have identical effective residue constraints, so the old symmetry was also sound. The [reduction proof](reduction-proof.md) proves this and explicitly corrects that diagnosis. The current code matches the simpler documented equal-original-modulus rule; all claims are supported by fresh replay.
