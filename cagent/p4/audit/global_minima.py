#!/usr/bin/env python3
"""Certify globally smallest residue-obstruction size within each survivor.

Every distinct smaller submultiset is recorded with a concrete feasible
residue list. A minimal-size infeasible submultiset is recorded as a search
result, not a formal UNSAT proof; see REPORT.md for this distinction.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path
from time import monotonic

from audit import residues, valid_residues


def read_facts(path):
    facts = {}
    if path.exists():
        for line in path.read_text().splitlines():
            row = json.loads(line)
            key = tuple(row["moduli"])
            value = None if row["residues"] is None else tuple(row["residues"])
            if key in facts:
                assert facts[key] == value
            facts[key] = value
    return facts


def read_claims(path):
    claims = {}
    if path.exists():
        for line in path.read_text().splitlines():
            row = json.loads(line)
            key = (row["k"], row["ordinal"])
            assert key not in claims
            claims[key] = row
    return claims


def run(paths, fact_path, claim_path, summary_path, seconds):
    start = monotonic()
    deadline = start + seconds
    facts = read_facts(fact_path)
    claims = read_claims(claim_path)
    inputs = [json.loads(Path(path).read_text()) for path in paths]
    total = sum(len(data["reduced_survivors"]) for data in inputs)
    complete = True
    checked_new = 0
    with fact_path.open("a") as fact_file, claim_path.open("a") as claim_file:
        try:
            for data in inputs:
                assert data["complete"]
                for ordinal, values in enumerate(data["reduced_survivors"]):
                    key = (data["k"], ordinal)
                    if key in claims:
                        assert claims[key]["survivor"] == values
                        continue
                    xs = tuple(values)
                    first_bad = None
                    for size in range(1, len(xs) + 1):
                        for sub in sorted(set(combinations(xs, size))):
                            if monotonic() >= deadline:
                                raise TimeoutError("global deadline")
                            if sub not in facts:
                                found = residues(sub, deadline)
                                if found is not None:
                                    assert valid_residues(sub, found)
                                    facts[sub] = tuple(found)
                                else:
                                    facts[sub] = None
                                fact_file.write(json.dumps({"moduli": sub,
                                    "residues": facts[sub]}, separators=(",", ":")) + "\n")
                                fact_file.flush()
                                checked_new += 1
                            if facts[sub] is None:
                                first_bad = sub
                                break
                        if first_bad is not None:
                            break
                    assert first_bad is not None, "full survivor unexpectedly feasible"
                    row = {"k": data["k"], "ordinal": ordinal,
                           "survivor": xs, "minimum_size": len(first_bad),
                           "obstruction": first_bad}
                    claim_file.write(json.dumps(row, separators=(",", ":")) + "\n")
                    claim_file.flush()
                    claims[key] = row
        except TimeoutError:
            complete = False
    summary = {"complete": complete, "seconds": round(monotonic()-start, 3),
               "total_survivors": total, "completed_survivors": len(claims),
               "fact_count": len(facts), "new_facts": checked_new}
    summary_path.write_text(json.dumps(summary, sort_keys=True) + "\n")
    print(json.dumps(summary, sort_keys=True), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("runs", nargs="+")
    parser.add_argument("--facts", type=Path, required=True)
    parser.add_argument("--claims", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=300)
    args = parser.parse_args()
    run(args.runs, args.facts, args.claims, args.summary, args.seconds)
