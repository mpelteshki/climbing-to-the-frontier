#!/usr/bin/env python3
"""Compare exact survivor *sets* from tuple DFS and value-clique search."""

import argparse
import json
from pathlib import Path


def load(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines()]


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--tuple-runs", nargs="+", required=True)
    parser.add_argument("--clique-runs", nargs="+", required=True)
    args = parser.parse_args()
    first = {row["k"]: row for path in args.tuple_runs for row in load(path)}
    second = {row["k"]: row for path in args.clique_runs for row in load(path)}
    assert first.keys() == second.keys()
    for k in sorted(first):
        a, b = first[k], second[k]
        assert a["complete"] and b["complete"]
        field = "base_survivors" if k <= 14 else "reduced_survivors"
        left = {tuple(xs) for xs in a[field]}
        right = {tuple(xs) for xs in b[field]}
        result = {"k": k, "field": field, "tuple_count": len(left),
                  "clique_count": len(right),
                  "tuple_only": [list(xs) for xs in sorted(left-right)],
                  "clique_only": [list(xs) for xs in sorted(right-left)]}
        print(json.dumps(result, sort_keys=True), flush=True)
        assert left == right
