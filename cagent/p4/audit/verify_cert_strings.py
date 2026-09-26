#!/usr/bin/env python3
"""Parse explicit-arity ASCII strings and compare to verified nested trees."""

import argparse
import json
from pathlib import Path

from verify_refutations import verify


def parse(proof):
    position = 0

    def subtree():
        nonlocal position
        assert position < len(proof)
        token = proof[position]
        position += 1
        if token == "A":
            return 0
        assert token == "B" and position + 2 <= len(proof)
        index = int(proof[position], 16)
        arity = int(proof[position+1], 16)
        position += 2
        assert arity >= 1
        return [index, [subtree() for _ in range(arity)]]

    result = subtree()
    assert position == len(proof), "trailing proof bytes"
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("trees", type=Path)
    parser.add_argument("compact", type=Path)
    args = parser.parse_args()
    nested = [json.loads(line) for line in args.trees.read_text().splitlines()]
    compact = json.loads(args.compact.read_text())
    assert len(nested) == len(compact)
    total = 0
    for source, entry in zip(nested, compact):
        assert source["moduli"] == entry["moduli"]
        assert source["nodes"] == entry["nodes"]
        tree = parse(entry["proof"])
        assert tree == source["tree"]
        replay = dict(source, tree=tree)
        total += verify(replay)
    print(json.dumps({"complete": True, "trees": len(compact),
                      "checked_nodes": total, "bytes": args.compact.stat().st_size},
                     sort_keys=True))
