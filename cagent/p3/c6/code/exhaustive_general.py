#!/usr/bin/env python3
"""Exact D_B(n) for arbitrary n by backward layering (same method as exhaustive_r3.py).

    python3 exhaustive_general.py N1 [N2 ...]

Writes evidence/exhaustive-n{N}.json with D_B(n), Griggs-Ho value, maximizer count.
"""
from __future__ import annotations

import json
import sys
import time

from bs_core import (L_formula, cyclic_states, depth_forward, is_boundary,
                     is_cyclic_direct, num_partitions, predecessors, rank_residue)


def run(n: int):
    t0 = time.perf_counter()
    layer = cyclic_states(n)
    for s in layer:
        assert sum(s) == n and is_cyclic_direct(s)
    sizes = [len(layer)]
    while True:
        nxt = []
        if len(sizes) == 1:
            for mu in layer:
                nxt.extend(q for q in predecessors(mu) if not is_boundary(q, n))
        else:
            for mu in layer:
                nxt.extend(predecessors(mu))
        if not nxt:
            break
        sizes.append(len(nxt))
        layer = nxt
    assert sum(sizes) == num_partitions(n)
    D = len(sizes) - 1
    for lam in layer[:50]:
        assert depth_forward(lam) == D
    k, r = rank_residue(n)
    return {"n": n, "k": k, "r": r, "partitions": num_partitions(n), "D_B": D,
            "griggs_ho_L": L_formula(n), "match": D == L_formula(n),
            "num_maximizers": len(layer), "sample_maximizers": [list(m) for m in sorted(layer, reverse=True)[:5]],
            "layer_sizes": sizes, "seconds": round(time.perf_counter() - t0, 2)}


if __name__ == "__main__":
    for a in sys.argv[1:]:
        row = run(int(a))
        print(f"n={row['n']} k={row['k']} r={row['r']} p(n)={row['partitions']} D_B={row['D_B']} "
              f"L={row['griggs_ho_L']} match={row['match']} maximizers={row['num_maximizers']} {row['seconds']}s", flush=True)
        with open(f"../evidence/exhaustive-n{row['n']}.json", "w") as fh:
            json.dump(row, fh, indent=1)
