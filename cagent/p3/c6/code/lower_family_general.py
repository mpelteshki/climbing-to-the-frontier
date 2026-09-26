#!/usr/bin/env python3
"""Griggs-Ho Theorem 4.5 case (1) family for general small residue r, checked by
direct iteration (classification-free cycle detection).

    python3 lower_family_general.py R KMIN KMAX

lambda: lambda_1 = k-2, lambda_i = k-i (2<=i<=k-r-1), lambda_i = k-i+1 (k-r<=i<=k).
Expected depth (k-1)(k-r-2) for r < floor((k-1)/2).
"""
import json
import sys
import time

from bs_core import T, depth_forward


def family(k, r):
    parts = [k - 2] + [k - i for i in range(2, k - r)] + [k - i + 1 for i in range(k - r, k + 1)]
    assert len(parts) == k and sum(parts) == T(k - 1) + r, (k, r, parts)
    assert parts == sorted(parts, reverse=True)
    return tuple(parts)


if __name__ == "__main__":
    r, kmin, kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    t0 = time.perf_counter()
    rows = []
    for k in range(kmin, kmax + 1):
        if not r < (k - 1) // 2:
            continue
        lam = family(k, r)
        d = depth_forward(lam)
        assert d == (k - 1) * (k - r - 2), (k, r, d)
        rows.append({"k": k, "n": T(k - 1) + r, "depth": d})
    out = {"r": r, "checked": rows, "seconds": round(time.perf_counter() - t0, 2), "status": "PASS"}
    print(f"r={r}: family depth (k-1)(k-r-2) confirmed for k={rows[0]['k']}..{rows[-1]['k']} ({out['seconds']}s)")
    with open(f"../evidence/lower-family-r{r}.json", "w") as fh:
        json.dump(out, fh, indent=1)
