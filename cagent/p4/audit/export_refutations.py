#!/usr/bin/env python3
"""Export exhaustive residue-refutation trees for minimum obstructions.

Tree grammar: 0 is a dead leaf; [i, children] branches at variable i over
every currently admissible residue in increasing order. Values are implicit
and recomputed by verify_refutations.py. No SAT leaf is permitted.
"""

import argparse
import json
from math import gcd, lcm
from pathlib import Path


def export(xs):
    n = len(xs)
    pair = [[gcd(xs[i], xs[j]) for j in range(n)] for i in range(n)]
    limits = [lcm(*(pair[i][j] for j in range(n) if j != i)) for i in range(n)]
    chosen = [-1] * n
    chosen[0] = 0
    nodes = leaves = 0

    def options_for(i):
        out = []
        for value in range(limits[i]):
            if any(chosen[j] >= 0 and (value-chosen[j]) % pair[i][j] == 0
                   for j in range(n) if j != i):
                continue
            if any(xs[j] == xs[i] and chosen[j] >= 0 and
                   ((j<i and chosen[j] >= value) or (j>i and chosen[j] <= value))
                   for j in range(n) if j != i):
                continue
            out.append(value)
        return out

    def build():
        nonlocal nodes, leaves
        nodes += 1
        if all(value >= 0 for value in chosen):
            raise AssertionError("SAT leaf in claimed obstruction")
        best_i, best_options = None, None
        for i in range(n):
            if chosen[i] >= 0:
                continue
            options = options_for(i)
            if not options:
                leaves += 1
                return 0
            if best_options is None or len(options) < len(best_options):
                best_i, best_options = i, options
        children = []
        for value in best_options:
            chosen[best_i] = value
            children.append(build())
            chosen[best_i] = -1
        return [best_i, children]

    tree = build()
    return {"moduli": xs, "effective_moduli": limits, "root_residue_0": 0,
            "equal_moduli_strictly_increasing": True, "nodes": nodes,
            "dead_leaves": leaves, "tree": tree}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("claims", type=Path)
    args = parser.parse_args()
    claims = [json.loads(line) for line in args.claims.read_text().splitlines()]
    unique = sorted({tuple(row["obstruction"]) for row in claims},
                    key=lambda xs: (len(xs), xs))
    for xs in unique:
        print(json.dumps(export(xs), separators=(",", ":")), flush=True)
