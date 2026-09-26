#!/usr/bin/env python3
"""Export compact, self-delimiting preorder trees for a future Lean checker.

Grammar: A = dead leaf; B<hex-index><hex-arity><children...> = branch.
Index and arity are each one uppercase hexadecimal digit. Arity is explicit.
"""

import argparse
import json
from pathlib import Path


def encode(tree):
    if tree == 0:
        return "A"
    index, children = tree
    assert 0 <= index <= 15 and 1 <= len(children) <= 15
    return "B" + format(index, "X") + format(len(children), "X") + "".join(
        encode(child) for child in children)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("trees", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    rows = [json.loads(line) for line in args.trees.read_text().splitlines()]
    output = [{"moduli": row["moduli"], "nodes": row["nodes"],
               "proof": encode(row["tree"])} for row in rows]
    args.output.write_text(json.dumps(output, separators=(",", ":")) + "\n")
