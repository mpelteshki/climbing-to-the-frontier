#!/usr/bin/env python3
"""Replay complete residue decision trees without running the search heuristic."""

import argparse
import json
from math import gcd, lcm
from pathlib import Path


def verify(row):
    xs = tuple(row["moduli"])
    n = len(xs)
    assert n >= 2 and xs == tuple(sorted(xs))
    pair = [[gcd(xs[i], xs[j]) for j in range(n)] for i in range(n)]
    limits = [lcm(*(pair[i][j] for j in range(n) if j != i)) for i in range(n)]
    assert row["effective_moduli"] == limits
    assert row["root_residue_0"] == 0
    assert row["equal_moduli_strictly_increasing"] is True
    chosen = [-1] * n
    chosen[0] = 0
    nodes = leaves = 0

    def allowed(i):
        ans = []
        for value in range(limits[i]):
            if any(chosen[j] >= 0 and (value-chosen[j]) % pair[i][j] == 0
                   for j in range(n) if j != i):
                continue
            if any(xs[j] == xs[i] and chosen[j] >= 0 and
                   ((j<i and chosen[j] >= value) or (j>i and chosen[j] <= value))
                   for j in range(n) if j != i):
                continue
            ans.append(value)
        return ans

    def replay(tree):
        nonlocal nodes, leaves
        nodes += 1
        assert any(value < 0 for value in chosen), "a full assignment survived"
        if tree == 0:
            assert any(not allowed(i) for i in range(n) if chosen[i] < 0)
            leaves += 1
            return
        assert isinstance(tree, list) and len(tree) == 2
        i, children = tree
        assert isinstance(i, int) and 0 <= i < n and chosen[i] < 0
        assert isinstance(children, list)
        choices = allowed(i)
        assert len(choices) == len(children) and choices
        for value, child in zip(choices, children):
            chosen[i] = value
            replay(child)
            chosen[i] = -1

    replay(row["tree"])
    assert nodes == row["nodes"] and leaves == row["dead_leaves"]
    return nodes


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("claims", type=Path)
    parser.add_argument("trees", type=Path)
    args = parser.parse_args()
    claims = [json.loads(line) for line in args.claims.read_text().splitlines()]
    trees = [json.loads(line) for line in args.trees.read_text().splitlines()]
    expected = {tuple(row["obstruction"]) for row in claims}
    actual = {tuple(row["moduli"]) for row in trees}
    assert len(actual) == len(trees) and expected == actual
    total = sum(verify(row) for row in trees)
    print(json.dumps({"complete": True, "unique_obstructions": len(trees),
                      "checked_nodes": total}, sort_keys=True))
