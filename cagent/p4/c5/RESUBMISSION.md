# P4 C5 resubmission: certified contiguous range through 16

**Claim:** Every pairwise disjoint family of $k$ integer congruence classes with positive moduli has two moduli whose gcd is at least $k$, for every $2\le k\le16$. Moduli and residues may repeat. The claimed range ends at **16**; no claim is made for 17–23. Sizes 24 and 30 cannot be the *least* failing size. This is a resubmission of C5 with the two previously missing pruning-off comparisons at 15 and 16.

## Proof of the contiguous range

The [Lean theorem `ThroughTwelve.solution`](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/lean/ProofPursuit/P4/ThroughTwelve.lean) proves the statement for every $2\le k\le12$ with no added hypotheses. Its definition of disjointness concerns actual sets of integers. A fresh build and independent `leanchecker` replay passed with only Lean's standard axioms.

For $k=13,14,15,16$, proceed in order. If $k$ were the first failing size, choose a counterexample minimizing the sum of its moduli. The [finite-reduction and pruning proof](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/audit/reduction-proof.md) shows that every modulus divides $L_k=\operatorname{lcm}(1,\ldots,k-1)$, has at least two prime factors, and satisfies every search condition. It also proves the exact search-path coverage, including repeated moduli, the every-subset density test, the three complete-tuple special conditions, and the three optional early conditions. No assumption about a smaller unproved case enters: the induction has established all preceding sizes.

The [two independent enumerators and their recorded 500.013-second replay](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/audit/rerun-full/replay-evidence-9-16.json) agree elementwise. At 13 their complete reduced search leaves [one modulus list](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/audit/run-9-14.jsonl); its seven-element subfamily is impossible by the parity-and-modulo-5 proof in the [C4 write-up](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/c4/solution.md). At 14 nothing survives. At 15 the exact complete reduced list has **30** objects; at 16 it has **77**. Full lists, with multiplicities, occur in [run-15-strong-60.jsonl](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/audit/run-15-strong-60.jsonl) and [run-16-strong-300.jsonl](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/audit/run-16-strong-300.jsonl). These are final lists after the stated necessary conditions; incomplete raw density-only counts at 15 and 16 are not claimed.

Every one of the 107 lists is decided separately. [Global minimum claims](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/audit/global-minima-claims.jsonl) give each list its smallest forcing submultiset, including its cardinality. [Fifty-nine distinct complete refutation trees](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/audit/minimum-refutations.jsonl) exclude all assignments of residues for those obstructions; the independent verifier replayed **40,292** nodes. [Explicit positive residue assignments](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/audit/global-minima-facts.jsonl) realize every smaller submultiset needed for each minimum claim: **19,704** such facts, checked against pairwise gcd conditions. The corrected residue solver reproduced all **107** claims and **20,436** stored fact records; the old stronger symmetry was separately shown sound. Thus each obstruction is globally minimum by cardinality inside its corresponding survivor, rather than merely minimal under one deletion. The [verification record](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/verification.md) explains trust and replay boundaries.

Each possible first failing size 13–16 leads to an excluded complete list. This proves the claimed contiguous range through 16. The general Lean theorem stops at 12; cases 13–16 have written reductions and independently replayable exhaustive certificates.

## Early pruning switched off at 15 and 16

The [new C++ search](../audit/rule_ablation.cpp) reconstructs the finite divisor domain and grows anchor triples with replacement. It precomputes compatible pairs and exact integer density-valid triples, which is equivalent to rejecting those hereditary failures when a candidate is appended. At a complete tuple, **both modes apply exactly the same** prime-power support, large-prime count, exactly-three-anchor, and every-subset density conditions. `on` additionally applies the three proved no-future tests to unfinished prefixes; `off` skips all three. The complete-tuple conditions are evaluated before the more expensive density subset scan in both modes. Reordering two necessary checks changes runtime, not the survivor set. The underlying proofs for every rule and search-path coverage are in the linked reduction proof. Source can be compiled with any C++17 compiler.

| $k$ | Mode | Search nodes | Wall seconds | Exact final lists |
|---:|:---|---:|---:|---:|
| 15 | on | 2,116,642 | 1.825 | 30 |
| 15 | off | 8,750,591 | 1.909 | 30 |
| 16 | on | 6,832,600 | 9.975 | 77 |
| 16 | off | 27,446,587 | 10.856 | 77 |

At each size, the two entire lists—not only their counts—are identical, and each equals the list independently obtained by both published Python methods. [Machine-readable evidence](../audit/ablation-evidence.json) records those comparisons, per-run nodes and wall clocks, source hash, and fresh certificate-verifier outputs. Four full arrays are saved as `ablation-{on,off}-{15,16}.json`. The initial unoptimized subset-check ordering gave the same 30 lists at 15 but took 135 seconds with pruning off; it was replaced by the common, logically equivalent leaf ordering before the final reproducible run. These counts are the **C++ search's** states, so they need not match either Python method's traversal counts.

Rebuild, rerun all four searches, check their lists against the published independent results, and independently replay every minimum certificate:

```sh
cd cagent/p4/audit
python3 -B verify_rule_ablation.py
```

The command creates a new temporary output directory and took **27.626 seconds** in the recorded run. The already-published full Python replay took **500.013 seconds**; both computations separately meet the ten-minute requirement, and their recorded times total **527.639 seconds**. Exact source and output appear next to this write-up. Do not replace the 15/16 raw density-only counts with the strong run's intermediate `base_survivors` fields.

## Nonvacuity and isolated sizes

The [positive-control run](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/audit/positive-control.jsonl) invokes the same base enumerator with gcd cap 7 and target length 6; it returns six copies of modulus 6. Residues $0,1,2,3,4,5$ realize six genuinely disjoint classes. The parameters differ because no positive example with target size equal to cap can exist within the proved range. No answer is injected or rule silently removed.

The [line-by-line 24/30 proof](https://github.com/mpelteshki/climbing-to-the-frontier/blob/ed55f76eb8c558825bb629fd2cd8dbf46e5f1314/cagent/p4/c5/known-cases.md) shows neither 24 nor 30 can be the *least* failing size. Its prime-support argument includes the corrected $q,q'$ step in O'Bryant's exceptional $k=30$ case. These are conditional least-failure exclusions, not unconditional theorems at sizes 24 and 30. Published arguments are credited and reconstructed; the $k=13$ discrepancy with the paper's reported necessary-condition search is documented in the C4 proof.

No platform result is claimed in this document until a new submission is actually accepted. The certified endpoint here is 16; no status for size 17 or higher is inferred from an unfinished search.
