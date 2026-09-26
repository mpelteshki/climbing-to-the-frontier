# Reproducible audit manifest

The original 31 files below form the base data package; retain them together to replay the two finite enumerators,
the shared SAT-witness map, the global minimum obstruction claims, and all
59 finite UNSAT trees. The current package additionally includes the proof and replay files below.
All paths below are relative to this directory.

| Role | Required files |
| --- | --- |
| Explanation | `REPORT.md` |
| Search, checking, conversion code | `enumerate.py`, `clique.py`, `audit.py`, `global_minima.py`, `verify_global_minima.py`, `export_refutations.py`, `verify_refutations.py`, `encode_cert_strings.py`, `verify_cert_strings.py`, `compare_independent.py` |
| Lean k=11 certificate regeneration | `eleven_lean.py`, `eleven-regeneration.json` |
| Tuple-search results | `run-9-14.jsonl`, `run-15-strong-60.jsonl`, `run-16-strong-300.jsonl` |
| Independent value-clique results | `clique-9-12.jsonl`, `clique-13-14.jsonl`, `clique-15-strong.jsonl`, `clique-16-strong.jsonl`, `compare-independent-9-16.jsonl` |
| Thirteen-list and positive control | `audit-9-14.json`, `positive-control.jsonl` |
| Global cardinality minima | `global-minima-facts.jsonl`, `global-minima-claims.jsonl`, `global-minima-summary.json`, `global-minima-verification.json` |
| Refutation certificates | `minimum-refutations.jsonl`, `minimum-refutations-verification.json`, `cert-strings.json`, `cert-strings-verification.json` |

Do not copy `timed-out-*.jsonl`, `estimate_refutations.py`,
`refutation-size-estimates*.jsonl`, `obstructions.py`,
`obstructions-*.jsonl`, `compare.py`, `compare-9-14.jsonl`,
`compact_refutations.py`, `minimum-refutations-compact.jsonl`, or
`__pycache__/` into a proof package. They are development diagnostics,
intermediate superseded outputs, or depend on the separate exploratory
`solutions/p4/search.py`. The historical `solutions/p4/initial-search.jsonl`
is invalid and must not be copied as evidence.

Every production output in the list has a completeness or independent replay
check described in `REPORT.md`. Python checking is not a Lean theorem.

## Complete boundary-14 replay additions

- `reduction-proof.md`: reconstructed proofs of every finite reduction and pruning rule.
- `replay.py`: one-command fresh replay, defaulting to a new temporary output directory.
- `replay-evidence-9-14.json`: complete 16.109-second run and per-size node/wall-clock records.
- `rerun-tuple-9-14.jsonl`, `rerun-clique-9-14.jsonl`: regenerated exact search outputs.
- `rerun-rule-on-9-14.jsonl`: enabled early pruning compared with disabled baseline at every size.
- `rerun-positive-control-9-14.jsonl`, `rerun-audit-9-14.json`: corrected fresh control and direct audit.

Run from repository root: `python3 -B cagent/p4/audit/replay.py --max-k 14`. Saved outputs need not be deleted; choose `--output-dir` only for a fresh directory. The runner checks baseline counts as well as exact survivor lists.

## Complete C4 replay through 16

`rerun-full/` contains the complete 500.013-second run: `replay-evidence-9-16.json`, regenerated tuple and clique outputs, positive control, and the through-14 rule-on outputs. These are evidence artifacts, not required inputs to a new run. Run `python3 -B cagent/p4/audit/replay.py --max-k 16` to generate a new independent replay directory.
