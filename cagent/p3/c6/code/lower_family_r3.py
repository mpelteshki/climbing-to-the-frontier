#!/usr/bin/env python3
"""Griggs-Ho Theorem 4.5 case (1) family at r=3, checked against the real move.

lambda_k = (k-2, k-2, k-3, ..., 4, 4, 3, 2, 1)   (k parts, sum T(k-1)+3)

Relative to the staircase (k-1, ..., 1, 0): hole on diagonal k-1 at column 0,
extra cells on diagonal k at columns k-4, k-3, k-2, k-1.

Claim (proved in RESULT.md): for 0 <= t < F = (k-1)(k-5), with t = a(k-1)+b,
B^t(lambda) is the staircase with the hole at column b and extras at columns
(b-a-1-j) mod k, j=0..3; it is not cyclic. B^F(lambda) is cyclic.

This script checks the claim for k = KMIN..KMAX by following the actual
sorted move, and separately reports the family's depth for k = 5..8 where it
is not optimal.
"""

from __future__ import annotations

import json
import sys
import time

from bs_core import T, depth_forward, is_boundary, is_cyclic_direct, step


def family(k: int):
    parts = [k - 2] + [k - i for i in range(2, k - 3)] + [4, 3, 2, 1]
    assert len(parts) == k and sum(parts) == T(k - 1) + 3, parts
    return tuple(parts)


def predicted(k: int, t: int):
    a, b = divmod(t, k - 1)
    h = [k - 1 - j for j in range(k)]  # staircase, k columns, last is 0
    h[b] -= 1
    for j in range(4):
        h[(b - a - 1 - j) % k] += 1
    return tuple(x for x in h if x > 0), h


def check(k: int):
    lam = family(k)
    F = (k - 1) * (k - 5)
    cur = lam
    for t in range(F):
        pred, h = predicted(k, t)
        assert h == sorted(h, reverse=True), (k, t, h)  # no sorting needed
        assert cur == pred, (k, t, cur, pred)
        assert not is_boundary(cur), (k, t, cur)
        cur = step(cur)
    assert is_boundary(cur), (k, cur)
    assert cur == tuple(x for x in [k - 1, k - 2, k - 2, k - 3, k - 4] + list(range(k - 6, 0, -1)) if x > 0)
    return F


def main():
    kmin = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    t0 = time.perf_counter()
    for k in range(kmin, kmax + 1):
        check(k)
    # direct (classification-free) depth for a few small k
    direct = {}
    for k in range(9, 26):
        direct[k] = depth_forward(family(k))
        assert direct[k] == (k - 1) * (k - 5)
        assert is_cyclic_direct(step(family(k)) if False else family(k)) is False
    small = {}
    for k in range(5, 9):
        lam = family(k)
        small[k] = {"family": list(lam), "family_depth": depth_forward(lam), "n": T(k - 1) + 3}
    out = {
        "status": "PASS",
        "k_range_modular_trajectory": [kmin, kmax],
        "k_range_direct_depth": [9, 25],
        "small_k_family_not_optimal": small,
        "seconds": round(time.perf_counter() - t0, 2),
    }
    print(json.dumps(out, indent=1))
    with open("../evidence/lower-family-r3.json", "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
