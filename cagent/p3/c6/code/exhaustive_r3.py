#!/usr/bin/env python3
"""Exact D_B(T_{k-1}+3) by exhaustive backward layering.

    python3 exhaustive_r3.py KMIN KMAX

For each k, n = T(k-1)+3. Layer 0 = the C(k,3) cyclic states; layer j+1 =
predecessors of layer j (cyclic ones removed at the first step). Since every
partition has exactly one successor, each partition appears in exactly one
layer, and the layer sizes must sum to p(n): this is asserted, so the run is
exhaustive by construction. D_B(n) = number of the last nonempty layer.

The C1 boundary form is used only to seed layer 0 and to drop cyclic
predecessors at the first step; check_prereqs.py verifies that form against
direct cycle detection, and here we additionally verify every seed by
direct cycle detection and verify that no state of layer >= 1 is cyclic
(direct check on a random sample plus the full last layer).
"""

from __future__ import annotations

import json
import random
import sys
import time

from bs_core import (
    L_formula,
    T,
    cyclic_states,
    depth_forward,
    is_cyclic_direct,
    num_partitions,
    predecessors,
    is_boundary,
)


def run(k: int):
    n = T(k - 1) + 3
    t0 = time.perf_counter()
    layer = cyclic_states(n)
    for s in layer:
        assert sum(s) == n and is_cyclic_direct(s)
    sizes = [len(layer)]
    rng = random.Random(k)
    sample_checked = 0
    while True:
        nxt = []
        if len(sizes) == 1:
            for mu in layer:
                for lam in predecessors(mu):
                    if not is_boundary(lam, n):
                        nxt.append(lam)
        else:
            for mu in layer:
                nxt.extend(predecessors(mu))
        if not nxt:
            break
        # spot check: sampled states are non-cyclic and have the right depth
        for lam in rng.sample(nxt, min(3, len(nxt))):
            assert not is_cyclic_direct(lam)
            assert depth_forward(lam) == len(sizes)
            sample_checked += 1
        sizes.append(len(nxt))
        layer = nxt
    total = sum(sizes)
    pn = num_partitions(n)
    assert total == pn, (total, pn)
    D = len(sizes) - 1
    for lam in layer:
        assert depth_forward(lam) == D
    maximizers = sorted(layer, reverse=True)
    return {
        "k": k,
        "n": n,
        "partitions": pn,
        "D_B": D,
        "griggs_ho_L": L_formula(n),
        "small_residue_candidate_(k-1)(k-5)": (k - 1) * (k - 5),
        "match_L": D == L_formula(n),
        "num_maximizers": len(layer),
        "maximizers": [list(m) for m in maximizers] if len(layer) <= 40 else [list(m) for m in maximizers[:40]],
        "layer_sizes": sizes,
        "sampled_depth_checks": sample_checked,
        "seconds": round(time.perf_counter() - t0, 2),
    }


def main():
    kmin, kmax = int(sys.argv[1]), int(sys.argv[2])
    rows = []
    for k in range(kmin, kmax + 1):
        row = run(k)
        rows.append(row)
        print(
            f"k={k:2d} n={row['n']:3d} p(n)={row['partitions']:>9d} D_B={row['D_B']:3d} "
            f"L={row['griggs_ho_L']:3d} (k-1)(k-5)={row['small_residue_candidate_(k-1)(k-5)']:3d} "
            f"maximizers={row['num_maximizers']} {row['seconds']}s",
            flush=True,
        )
        with open(f"../evidence/exhaustive-r3-k{k}.json", "w") as fh:
            json.dump(row, fh, indent=1)


if __name__ == "__main__":
    main()
