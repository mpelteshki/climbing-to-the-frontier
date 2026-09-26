#!/usr/bin/env python3
"""Replay shared SAT witnesses and recompute minimal UNSAT submultisets."""

import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from audit import residues, valid_residues


def read_lines(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def verify(runs, facts_path, claims_path):
    source = {(row["k"], i): tuple(xs)
              for path in runs for row in read_lines(path)
              for i, xs in enumerate(row["reduced_survivors"])}
    fact_rows = read_lines(facts_path)
    facts = {}
    for row in fact_rows:
        xs = tuple(row["moduli"])
        assert xs not in facts and xs == tuple(sorted(xs))
        witness = row["residues"]
        if witness is not None:
            assert valid_residues(xs, witness)
        facts[xs] = witness
    claims = read_lines(claims_path)
    assert len(claims) == len(source)
    found_keys = set()
    hist = {}
    sat_fact_used = set()
    for row in claims:
        key = (row["k"], row["ordinal"])
        assert key in source and key not in found_keys
        found_keys.add(key)
        xs = source[key]
        assert tuple(row["survivor"]) == xs
        obstruction = tuple(row["obstruction"])
        size = row["minimum_size"]
        assert len(obstruction) == size
        assert not (Counter(obstruction) - Counter(xs))
        assert obstruction in facts and facts[obstruction] is None
        assert residues(obstruction) is None
        for smaller_size in range(1, size):
            for sub in set(combinations(xs, smaller_size)):
                assert sub in facts and facts[sub] is not None
                sat_fact_used.add(sub)
        hist.setdefault(row["k"], Counter())[size] += 1
    assert found_keys == set(source)
    return {"complete": True, "claims": len(claims), "facts": len(facts),
            "smaller_sat_facts_used": len(sat_fact_used),
            "minimum_sizes": {str(k): dict(sorted(c.items())) for k, c in sorted(hist.items())}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--runs", type=Path, nargs="+", required=True)
    parser.add_argument("--facts", type=Path, required=True)
    parser.add_argument("--claims", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.runs, args.facts, args.claims), sort_keys=True))
