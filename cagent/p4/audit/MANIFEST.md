# Reproducible audit manifest

Copy the following 31 files together to replay the two finite enumerators,
the shared SAT-witness map, the global minimum obstruction claims, and all
59 finite UNSAT trees. Total size before this manifest: **1,619,073 bytes**.
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
