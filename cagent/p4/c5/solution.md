# P4 C5: certified range and certificate checklist

Task source: [The certified boundary](https://hackathon.bainsa.ai/p/p4/c5), checked on 2026-09-26. This package is not a platform submission or an organizer acceptance.

## Claimed certified boundary: 14

**C5 is solved for the contiguous claimed range 2–14**, the largest range for which this package currently completes every C5 benchmark, including an observed rule-on/rule-off comparison. This endpoint describes our completed certificate, not the largest true size of the conjecture.

Sizes 2–12 have a complete Lean theorem. For 13, assume it is the least failing size, normalize a minimum-modulus-sum counterexample, and apply the [proved finite reduction and pruning rules](../audit/reduction-proof.md). The complete modulus search leaves exactly the explicit thirteen-list; its seven-entry obstruction is impossible, as proved in the [C4 argument](../c4/solution.md). Thus 13 holds. Repeating the least-counterexample argument at 14 gives an empty enumerated list, proving 14. Every smaller-size dependency is discharged in order.

The full computational replay for this C5 claim took **16.109 seconds**, including both independent implementations, exact node-count and survivor comparisons, all rule-on/off runs at 9–14, positive control, and the saved residue-certificate checks. Reproduce with:

```sh
python3 -B cagent/p4/audit/replay.py --max-k 14
```

It writes outputs to a new temporary directory by default, preserving bundled evidence. [Recorded replay](../audit/replay-evidence-9-14.json) contains every size's nodes, wall clock, exact baseline agreement, and equal final lists with early strong rules enabled and disabled. Counts agree exactly; elapsed time is machine-dependent.

Computational evidence also extends the mathematical argument through 16, but its additional C5 rule-off runs are unfinished. Those sizes are **not included in this C5 boundary claim**. No completed exhaustive search at 17 or above is claimed.

## Isolated sizes

[Known-cases proof](known-cases.md) reconstructs, line by line, the exclusions of **24 and 30 as least counterexample sizes**. It explicitly assumes all smaller sizes for each exclusion. It uses finite prime-support counting, not a search, and repairs an insufficient final inference in the source's exceptional k=30 argument. These are not unconditional 24-class or 30-class theorems inferred from our range through 16.

## Nonvacuous control

The unchanged base enumeration function accepts a gcd cap and a target length. Run `enumerate.py 7 --target-length 6` without the least-counterexample-only strong flag. It returns six copies of modulus 6, witnessed by residues `[0,1,2,3,4,5]`. These classes are pairwise disjoint; every pair gcd is 6, below the requested cap 7. The density is exactly one. The control uses the same finite domain, anchor enumeration, compatibility checks, density tests, and branching code as ordinary runs; it does not inject a preselected answer or disable a rejection because it happens to reject the desired example. The different cap and length are explicit inputs. Least-counterexample-only conditions cannot be imposed when those parameters differ, and the implementation rejects that invalid strong-mode combination.

The data are in [positive-control.jsonl](../audit/positive-control.jsonl), and fresh replay regenerates them. The control proves the machinery can return admissible objects; it is not a counterexample to the conjecture, whose cap and target size are equal.

## Complete survivor decisions and smallest obstructions

Within the C5 claim, at 9–12 and 14 the final modulus survivor lists are empty; at 13 there is one reduced list. The additional, separately scoped work at 15 and 16 has 30 and 77 reduced lists. Every list is written out in full in the linked JSONL data, not represented only by a count. The [C4 solution](../c4/solution.md) and [audit report](../audit/REPORT.md) identify the files and the distinction between raw density and reduced lists.

The 13-list has a seven-entry obstruction, with concrete realizations of every smaller submultiset. Its impossibility and minimum cardinality are also kernel-checked in Lean. For each of the other 107 lists, `global-minima-claims.jsonl` selects an obstruction, `minimum-refutations.jsonl` excludes all its residue assignments, and `global-minima-facts.jsonl` supplies actual residues for every smaller submultiset. The replay verifies inclusion, cardinality, every CRT inequality, full coverage of smaller submultisets, and all branches of each obstruction tree. This proves minimum cardinality inside each individual survivor, not merely that deleting one position repairs a chosen obstruction.

## Independent method and pruning comparison

The first enumeration grows nondecreasing occurrence lists after selecting an anchor triple with replacement. The second builds cliques of distinct compatible modulus values, then chooses positive multiplicities. Their divisor-generation routines also differ. Exact final lists are compared elementwise at every enumerated size. Different traversal node counts are expected; differences in final lists are not silently reconciled. The [reduction proof](../audit/reduction-proof.md) explains every mathematical pruning rule and every capacity or early-future check.

All numerical rules are necessary conditions proved in that document; an unfinished run is never interpreted as emptiness. For every computational size in the C5 claim, 9–14, completed runs with all three early strong rules enabled and disabled have identical final reduced survivor lists. The recorded comparisons turn off early feasibility checks while retaining the same proved complete-tuple conditions: they compare the same mathematical output set. Sizes 2–8 use complete direct Lean proofs, so there is no computational pruning or survivor list to compare there.
