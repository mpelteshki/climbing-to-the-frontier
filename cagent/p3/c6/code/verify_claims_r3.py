#!/usr/bin/env python3
"""Numerical verification of every symbolic claim used in the r=3 upper bound
(RESULT.md, Section 5), for k = KMIN..KMAX, plus finite tests of Lemmas D/D2.

    python3 verify_claims_r3.py [KMIN] [KMAX] [NMAX_LEMMA]

Nothing here is a proof for all k; it guards the written argument against
index slips. Lemma D/D2 are tested against exhaustive inverse trees for all
partitions of n <= NMAX_LEMMA.
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
    inverse_tree_height,
    is_boundary,
    predecessors,
    step,
)


def stair(k, top):
    """(top, top-1, ..., 1)"""
    return list(range(top, 0, -1))


def srt(*chunks):
    out = []
    for c in chunks:
        out.extend(c)
    return tuple(sorted(out, reverse=True))


def noncyc_preds(mu, n):
    return [q for q in predecessors(mu) if not is_boundary(q, n)]


def lemma_D_applies(mu):
    """unique largest part exceeding all others by >= 3 (or mu == (n,))."""
    if len(mu) == 1:
        return True
    return mu[0] - mu[1] >= 3


def lemma_D2_applies(mu):
    """two largest M >= M' (any gap), all other parts <= M'-3, M' >= 3."""
    if len(mu) < 2:
        return False
    M, Mp = mu[0], mu[1]
    rest = mu[2:]
    return Mp >= 3 and (not rest or rest[0] <= Mp - 3)


def rotation_orbit_has_diag_kplus1(S, k, moves):
    """Check B^j(S), j=0..moves, each has a cell on diagonal k+1 (=> not cyclic)
    and that no sorting is needed at any of these moves."""
    cur = S
    for j in range(moves + 1):
        # cell on diagonal k+1: some column c (0-based) with height >= k+1-c
        assert any(h >= k + 1 - c for c, h in enumerate(cur)), (S, j, cur)
        assert not is_boundary(cur), (S, j, cur)
        if j < moves:
            m = len(cur)
            unsorted = [m] + [x - 1 for x in cur if x > 1]
            assert unsorted == sorted(unsorted, reverse=True), ("sorting needed", S, j, cur)
            cur = step(cur)
    return True


def check_k(k):
    n = T(k - 1) + 3
    F = (k - 1) * (k - 5)
    rep = {"k": k, "n": n, "F": F}

    # ---- Section 5.3: type II width k-4 entry states (excess 6 among 4 piles of base k-4)
    base = [k - 2] + stair(k, k - 6)  # newborn k-2 and old piles 1..k-6
    states4 = {}
    from entry_states_r3 import partitions_into_at_most
    for exc in partitions_into_at_most(6, 4):
        S = srt(base, [k - 4 + e for e in exc])
        assert sum(S) == n
        states4[exc] = S
    cyc4 = {exc for exc, S in states4.items() if is_boundary(S, n)}
    assert cyc4 == {(4, 2, 0, 0), (4, 1, 1, 0), (3, 3, 0, 0), (3, 2, 1, 0)}, cyc4
    assert states4[(3, 2, 1, 0)] == tuple([k - 1, k - 2, k - 2, k - 3, k - 4] + stair(k, k - 6))
    # (6,0,0,0): Lemma D hypothesis with M = k+2
    S6 = states4[(6, 0, 0, 0)]
    assert S6 == srt([k + 2, k - 2, k - 4, k - 4, k - 4], stair(k, k - 6)) and lemma_D_applies(S6)
    rep["delta_6000"] = depth_forward(S6)
    # (5,1,0,0): Lemma D with M=k+1 (gap 3), B(S) cyclic
    S51 = states4[(5, 1, 0, 0)]
    assert S51 == srt([k + 1, k - 2, k - 3, k - 4, k - 4], stair(k, k - 6)) and lemma_D_applies(S51)
    assert is_boundary(step(S51), n) and not is_boundary(S51, n)
    # (3,1,1,1): orbit and count pattern
    S3111 = states4[(3, 1, 1, 1)]
    assert S3111 == srt([k - 1, k - 2, k - 3, k - 3, k - 3], stair(k, k - 6))
    orb = [S3111]
    for _ in range(k - 2):
        orb.append(step(orb[-1]))
    for j in range(k - 2):
        assert not is_boundary(orb[j], n)
        if j <= k - 6:
            assert orb[j] == tuple(stair(k, k - 1)[: j + 2] + [k - 3 - j] * 3 + stair(k, k - 6 - j)), (k, j, orb[j])
    assert orb[k - 5] == tuple(stair(k, k - 1)[: k - 3] + [2, 2, 2]) and len(orb[k - 5]) == k
    assert orb[k - 4] == tuple([k] + list(range(k - 2, 1, -1)) + [1, 1, 1]) and len(orb[k - 4]) == k + 1
    assert orb[k - 3] == tuple([k + 1, k - 1] + stair(k, k - 3)) and len(orb[k - 3]) == k - 1
    assert is_boundary(orb[k - 2], n) and orb[k - 2] == tuple([k, k - 1, k - 2] + stair(k, k - 4))
    assert [len(orb[k - 6]), len(orb[k - 5]), len(orb[k - 4])] == [k - 1, k, k + 1]
    rep["delta_3111"] = depth_forward(S3111)
    assert rep["delta_3111"] == k - 2
    # impossible ones: (2,2,2,0), (2,2,1,1) keep a cell on diagonal k+1 for k-2 moves
    for exc in ((2, 2, 2, 0), (2, 2, 1, 1)):
        rotation_orbit_has_diag_kplus1(states4[exc], k, k - 2)
        assert depth_forward(states4[exc]) == k - 1
    # the explicit states at j = k-4, k-3, k-2 listed in RESULT.md 5.4 / 5.5
    listed = {
        (2, 2, 2, 0): {k - 4: tuple([k] + list(range(k - 2, 3, -1)) + [2, 2, 2, 2]),
                       k - 3: tuple([k, k - 1] + list(range(k - 3, 2, -1)) + [1, 1, 1, 1]),
                       k - 2: tuple([k + 1, k - 1, k - 2] + list(range(k - 4, 1, -1)))},
        (2, 2, 1, 1): {k - 4: tuple([k] + list(range(k - 2, 3, -1)) + [2, 2, 2, 1, 1]),
                       k - 3: tuple([k + 1, k - 1] + list(range(k - 3, 2, -1)) + [1, 1, 1]),
                       k - 2: tuple([k, k, k - 2] + list(range(k - 4, 1, -1)))},
    }
    for exc, expect in listed.items():
        cur = states4[exc]
        for j in range(k - 1):
            if j in expect:
                assert cur == expect[j], (k, exc, j, cur, expect[j])
            cur = step(cur)

    # ---- Section 5.4: width k-3 (excess 4 among 3 piles of base k-3)
    base3 = [k - 2] + stair(k, k - 5)
    states3 = {exc: srt(base3, [k - 3 + e for e in exc]) for exc in partitions_into_at_most(4, 3)}
    for S in states3.values():
        assert sum(S) == n
    cyc3 = {exc for exc, S in states3.items() if is_boundary(S, n)}
    assert cyc3 == {(3, 1, 0), (2, 2, 0)}, cyc3
    S400 = states3[(4, 0, 0)]
    assert S400 == srt([k + 1, k - 2, k - 3, k - 3], stair(k, k - 5)) and lemma_D_applies(S400)
    assert is_boundary(step(S400), n)
    rotation_orbit_has_diag_kplus1(states3[(2, 1, 1)], k, k - 2)
    assert depth_forward(states3[(2, 1, 1)]) == k - 1
    listed211 = {k - 4: tuple(list(range(k - 1, 2, -1)) + [2, 2, 2]),
                 k - 3: tuple([k] + list(range(k - 2, 0, -1)) + [1, 1]),
                 k - 2: tuple([k + 1, k - 1] + list(range(k - 3, 0, -1)))}
    cur = states3[(2, 1, 1)]
    for j in range(k - 1):
        if j in listed211:
            assert cur == listed211[j], (k, j, cur)
        cur = step(cur)
    # S3 = (3,1,0) cyclic: its non-cyclic predecessors
    S3 = states3[(3, 1, 0)]
    assert S3 == tuple([k, k - 2, k - 2, k - 3] + stair(k, k - 5))
    P = tuple([k + 1, k - 1, k - 2] + list(range(k - 4, 1, -1)))
    assert noncyc_preds(S3, n) == [P], noncyc_preds(S3, n)
    Pp = noncyc_preds(P, n)
    Pa = tuple([k + 2, k] + list(range(k - 3, 2, -1)) + [1])      # remove k-2 (one 1 appended)
    Pb = tuple([k + 2, k - 1] + list(range(k - 3, 2, -1)) + [1, 1])  # remove k-1
    Q = tuple([k, k - 1] + list(range(k - 3, 2, -1)) + [1, 1, 1, 1])  # remove k+1
    assert set(Pp) == {Pa, Pb, Q}, (Pp, Pa, Pb, Q)
    assert lemma_D2_applies(Pa)
    Pb_preds = noncyc_preds(Pb, n)
    Pb1 = tuple([k + 3] + list(range(k - 2, 3, -1)) + [2, 2, 1])
    Pb2 = tuple([k] + list(range(k - 2, 3, -1)) + [2, 2, 1, 1, 1, 1])
    assert set(Pb_preds) == {Pb1, Pb2}, (Pb_preds, Pb1, Pb2)
    assert lemma_D_applies(Pb1) and Pb1[0] == k + 3 and noncyc_preds(Pb2, n) == []
    R = tuple([k] + list(range(k - 2, 3, -1)) + [2, 2, 2, 2])
    assert noncyc_preds(Q, n) == [R] and len(R) == k
    R3 = tuple(list(range(k - 1, 4, -1)) + [3, 3, 3, 3, 1])
    assert noncyc_preds(R, n) == [R3] and len(R3) == k
    assert all(len(x) == k - 1 for x in noncyc_preds(R3, n)) and noncyc_preds(R3, n)
    # S2 = (2,2,0) cyclic
    S2 = states3[(2, 2, 0)]
    assert S2 == tuple([k - 1, k - 1, k - 2, k - 3] + stair(k, k - 5))
    P2p = tuple([k, k, k - 2] + list(range(k - 4, 1, -1)))
    assert noncyc_preds(S2, n) == [P2p]
    Ya = tuple([k + 1, k + 1] + list(range(k - 3, 2, -1)) + [1])
    X1 = tuple([k + 1, k - 1] + list(range(k - 3, 2, -1)) + [1, 1, 1])
    assert set(noncyc_preds(P2p, n)) == {Ya, X1} and lemma_D2_applies(Ya)
    X1a = tuple([k + 2] + list(range(k - 2, 3, -1)) + [2, 2, 2])
    X2 = tuple([k] + list(range(k - 2, 3, -1)) + [2, 2, 2, 1, 1])
    assert set(noncyc_preds(X1, n)) == {X1a, X2} and lemma_D_applies(X1a) and len(X2) == k + 1
    X3 = tuple(list(range(k - 1, 4, -1)) + [3, 3, 3, 2, 2])
    assert noncyc_preds(X2, n) == [X3] and len(X3) == k
    assert all(len(x) == k - 1 for x in noncyc_preds(X3, n)) and noncyc_preds(X3, n)

    # ---- Section 5.5: width k-2 (excess 3 among 2 piles of base k-2)
    base2 = [k - 2] + stair(k, k - 4)
    states2 = {exc: srt(base2, [k - 2 + e for e in exc]) for exc in partitions_into_at_most(3, 2)}
    assert {exc for exc, S in states2.items() if is_boundary(S, n)} == {(2, 1)}
    S30 = states2[(3, 0)]
    assert S30 == tuple([k + 1, k - 2, k - 2] + stair(k, k - 4)) and lemma_D_applies(S30)
    assert is_boundary(step(S30), n)
    S21 = states2[(2, 1)]
    assert S21 == tuple([k, k - 1, k - 2] + stair(k, k - 4))
    P1 = tuple([k + 1, k - 1] + list(range(k - 3, 0, -1)))
    P2 = tuple([k + 1, k] + list(range(k - 3, 1, -1)))
    assert set(noncyc_preds(S21, n)) == {P1, P2} and lemma_D2_applies(P2)
    W = tuple([k + 2, k - 2] + stair(k, k - 3))
    Qp = tuple([k] + list(range(k - 2, 1, -1)) + [1, 1, 1])
    assert set(noncyc_preds(P1, n)) == {W, Qp} and lemma_D_applies(W) and len(Qp) == k + 1
    Rq = tuple(list(range(k - 1, 2, -1)) + [2, 2, 2])
    assert noncyc_preds(Qp, n) == [Rq] and len(Rq) == k
    assert all(len(x) == k - 1 for x in noncyc_preds(Rq, n)) and noncyc_preds(Rq, n)

    # ---- Section 5.6: full width: W = (k+2, k-2, ..., 1), depth 2
    assert not is_boundary(W, n) and not is_boundary(step(W), n) and is_boundary(step(step(W)), n)

    # ---- exact h values (small k only; trees grow) for the record
    if k <= 13:
        rep["h_S21"] = inverse_tree_height(S21)
        rep["h_W"] = inverse_tree_height(W)
        rep["h_S3"] = inverse_tree_height(S3)
        rep["h_S2"] = inverse_tree_height(S2)
        rep["h_S3111"] = inverse_tree_height(S3111)
        rep["h_S6000"] = inverse_tree_height(S6)
        assert rep["h_S21"] == n - k + 1 and rep["h_W"] == n - k - 1
        assert rep["h_S3"] <= n - k + 1 and rep["h_S2"] <= n - k + 2 and rep["h_S3111"] <= 5
        assert rep["h_S6000"] <= n - k - 1
    # generic inequalities used
    assert n - k + 1 <= F                      # k >= 9
    assert n - k + 2 <= F                      # k >= 9 (equality at k=9)
    assert (k < 10) or (n - 3 <= F)            # (6,0,0,0) via Lemma D, k >= 10
    assert (k < 14) or ((k - 1) + T(k - 7) + 6 * (k - 5) > n)  # type I width k-5 excluded, k>=14
    assert k * (k - 7) + k - 1 <= F - 6 if k >= 14 else True
    return rep


def test_lemmas(nmax):
    """Lemma D: unique largest M, others <= M-3  =>  h <= n-M+1.
       Lemma D2: largest M >= M', others <= M'-3, M' >= 3  =>  h <= (n-M-M')//2 + 2."""
    tested_D = tested_D2 = 0
    tight_D = tight_D2 = 0
    for n in range(1, nmax + 1):
        for mu in all_partitions(n):
            if is_boundary(mu, n):
                continue  # lemmas are applied to non-cyclic states; h counts non-cyclic ancestors
            if lemma_D_applies(mu):
                h = inverse_tree_height(mu)
                assert h <= n - mu[0] + 1, ("D", mu, h)
                tested_D += 1
                tight_D += h == n - mu[0] + 1
            if lemma_D2_applies(mu):
                h = inverse_tree_height(mu)
                assert h <= (n - mu[0] - mu[1]) // 2 + 2, ("D2", mu, h)
                tested_D2 += 1
                tight_D2 += h == (n - mu[0] - mu[1]) // 2 + 2
    return {"nmax": nmax, "lemmaD_tested": tested_D, "lemmaD_tight": tight_D,
            "lemmaD2_tested": tested_D2, "lemmaD2_tight": tight_D2}


def main():
    kmin = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    nmax = int(sys.argv[3]) if len(sys.argv) > 3 else 24
    t0 = time.perf_counter()
    reps = [check_k(k) for k in range(kmin, kmax + 1)]
    for r in reps:
        print(r, flush=True)
    lem = test_lemmas(nmax)
    print(lem)
    out = {"status": "PASS", "k_range": [kmin, kmax], "per_k": reps, "lemmas": lem,
           "seconds": round(time.perf_counter() - t0, 2)}
    with open("../evidence/verify-claims-r3.json", "w") as fh:
        json.dump(out, fh, indent=1)
    print("PASS", out["seconds"], "s")


if __name__ == "__main__":
    main()
