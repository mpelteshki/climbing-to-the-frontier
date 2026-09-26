# C4: solved

[Complete solution](solution.md) proves the statement through 12 and reports exact method outcomes at every size 9–16, including the tested discrepancy with the published search claim.

- `ThroughTwelve.solution`: unconditional Lean proof for 2 ≤ k ≤ 12; fresh build and independent kernel replay passed.
- [Finite reduction and every pruning rule](../audit/reduction-proof.md): full reconstructed written proofs.
- Exact reduced survivor counts at 9–16: **0, 0, 0, 0, 1, 0, 30, 77**; every list appears in the [audit package](../audit/MANIFEST.md).
- Every survivor is decided negatively, with a minimum-cardinality obstruction and explicit realizations proving no smaller submultiset suffices. The complete method leaves no undecided list at 9–16.
- [Fresh full replay](../audit/rerun-full/replay-evidence-9-16.json): **500.013 seconds**, exact node-count reproduction, two distinct enumeration methods with equal lists, and all residue certificates passed.

Reproduce from repository root:

```sh
python3 -B cagent/p4/audit/replay.py --max-k 16
```

This writes fresh outputs to a temporary directory. Runtime is an observation on this laptop, not a guarantee for every machine. For Lean commands, see the [P4 README](../README.md).

The mathematical certificate extends through 16. Only 2–12 is claimed as a general Lean range theorem. C5's additional rule-off requirement has a separately stated boundary of 14. No platform submission or organizer acceptance is claimed.
