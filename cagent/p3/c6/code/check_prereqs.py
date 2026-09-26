#!/usr/bin/env python3
"""Independent finite stress-test of every prerequisite reused from C1-C3.

This is finite evidence that the *statements* are right as stated (index
ranges included); the written proofs were audited separately in RESULT.md.

Checks, for every partition of every n <= MAXN:
  P1  C1 classification: is_cyclic_direct(lam) <=> binary-boundary form.
  P2  c_{i+1} <= c_i + 1 and c_{i+1} = c_i + 1 - (#intervals ending at i).
  P3  Card budget: sum_{j<m} c_{p+j} <= n + T(m-1) for all p, m.
  P4  Every sandwich (x-1, x..x, x+1) of width L=q-p>=2 has p <= x(L-1);
      width two has p <= x.
  P5  Special full-width type II (k-2,k-1..k-1,k) of width k: p+k <= n+1.
  P6  Final-pattern dichotomy: with t = smallest index such that
      c_t=k-1, c_{t+1}=k and the future is k-periodic (1<=r<k), d <= t-1,
      and if t >= k+1 then a type I pattern with t-k<=p<q<=t-1 or a type II
      pattern with t-k+1<=p<q<=t+1 exists.
  P7  Predecessor rule is exhaustive and sound: for every mu, the set of
      lam with step(lam)==mu (found by scanning all partitions of n)
      equals set(predecessors(mu)).
"""

from __future__ import annotations

import json
import sys
import time

from bs_core import (
    T,
    all_partitions,
    counts,
    depth_forward,
    is_boundary,
    is_cyclic_direct,
    predecessors,
    rank_residue,
    step,
)

MAXN = int(sys.argv[1]) if len(sys.argv) > 1 else 36


def sandwiches(cs):
    """Yield (p, q, x) (1-based indices) for every maximal-plateau sandwich."""
    m = len(cs)
    for p in range(m):
        x = cs[p] + 1
        q = p + 1
        if q >= m or cs[q] != x:
            continue
        while q < m and cs[q] == x:
            q += 1
        if q < m and cs[q] == x + 1:
            yield p + 1, q + 1, x


def main():
    t0 = time.perf_counter()
    stats = {"maxn": MAXN, "partitions": 0, "sandwiches": 0, "type1": 0, "type2": 0,
             "full_width_typeII": 0, "min_slack_retreat": None}
    for n in range(1, MAXN + 1):
        k, r = rank_residue(n)
        parts = list(all_partitions(n))
        stats["partitions"] += len(parts)
        succ = {}
        for lam in parts:
            succ[lam] = step(lam)
        # P7
        preds_scan = {}
        for lam, mu in succ.items():
            preds_scan.setdefault(mu, set()).add(lam)
        for mu in parts:
            assert set(predecessors(mu)) == preds_scan.get(mu, set()), ("P7", mu)
        for lam in parts:
            # P1
            assert is_cyclic_direct(lam) == is_boundary(lam, n), ("P1", lam)
            d = depth_forward(lam)
            horizon = d + 3 * k + 5
            cs = counts(lam, horizon)
            # P2 via explicit interval bookkeeping
            ends = {}
            for a in lam:
                ends[a] = ends.get(a, 0) + 1  # original pile of size a ends at time a
            for i in range(1, horizon):
                ci = cs[i - 1]
                e = i + ci  # newborn interval J_i = [i+1, i+ci]
                ends[e] = ends.get(e, 0) + 1
                di = ends.get(i, 0)
                assert cs[i] == ci + 1 - di, ("P2", lam, i)
            # P3
            for p in range(len(cs)):
                s = 0
                for m in range(1, min(len(cs) - p, 2 * k + 2) + 1):
                    s += cs[p + m - 1]
                    assert s <= n + T(m - 1), ("P3", lam, p + 1, m)
            # P4, P5
            for p, q, x in sandwiches(cs):
                stats["sandwiches"] += 1
                L = q - p
                assert p <= x * (L - 1), ("P4", lam, p, q, x)
                slack = x * (L - 1) - p
                if stats["min_slack_retreat"] is None or slack < stats["min_slack_retreat"]:
                    stats["min_slack_retreat"] = slack
                if L == 2:
                    assert p <= x, ("P4-w2", lam, p, q, x)
                if x == k - 1 and L == k:
                    stats["full_width_typeII"] += 1
                    assert p + k <= n + 1, ("P5", lam, p)
            # P6
            if 1 <= r < k:
                t = None
                for i in range(1, len(cs) - 2 * k):
                    if cs[i - 1] == k - 1 and cs[i] == k and all(
                        cs[i - 1 + j] == cs[i - 1 + k + j] for j in range(k + 1)
                    ):
                        # k-periodic future certified by the state, not just counts
                        st = lam
                        for _ in range(i - 1):
                            st = step(st)
                        if is_boundary(st, n):
                            t = i
                            break
                assert t is not None, ("P6-exists", lam)
                assert d <= t - 1, ("P6-depth", lam, d, t)
                if t >= k + 1:
                    found1 = found2 = False
                    for p, q, x in sandwiches(cs):
                        if x == k and t - k <= p < q <= t - 1:
                            found1 = True
                        if x == k - 1 and t - k + 1 <= p < q <= t + 1:
                            found2 = True
                    assert found1 or found2, ("P6-dichotomy", lam, t, cs[: t + k])
                    stats["type1"] += found1
                    stats["type2"] += found2
        print(f"n={n:2d} k={k:2d} r={r:2d} ok ({len(parts)} partitions)", flush=True)
    stats["seconds"] = round(time.perf_counter() - t0, 2)
    stats["status"] = "PASS"
    print(json.dumps(stats))
    with open("../evidence/prereqs-check.json", "w") as fh:
        json.dump(stats, fh, indent=1)


if __name__ == "__main__":
    main()
