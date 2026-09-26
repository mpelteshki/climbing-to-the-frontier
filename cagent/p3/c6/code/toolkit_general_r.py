#!/usr/bin/env python3
"""Does the r=3 upper-bound toolkit reach residue r?  Automated case classification.

    python3 toolkit_general_r.py R KMIN KMAX

For n = T(k-1)+r with r < floor((k-1)/2), target F = (k-1)(k-r-2).
For every sandwich (type I level k, type II level k-1) and width L not already
closed by the generic bound  d <= retreat(p) + (k-1 or k-2) <= F, enumerate the
forced entry states S (Lemma E) and classify each S by the first rule that
proves d <= F, in this order:

  cyclic     : S cyclic and retreat bound p <= x(L-1) <= F           (d = p)
  rotation   : S has a cell on diagonal k+1 and the unsorted move stays a
               partition for k-3 (type II) / k-2 (type I) moves       (impossible)
  lemmaD     : unique largest M with gap >= 3;  n-M+1 + slack <= F, where
               slack = delta(S) if delta <= moves_allowed else generic k-2 / k-1
  lemmaD2    : two largest M>=M'>=3, rest <= M'-3; floor((n-M-M')/2)+2 + slack <= F
  sandwich   : forward orbit of S shows counts (k-1,k,k+1) (width two, level k)
               or a level-k sandwich of width w within the first k moves, so the
               time of S is bounded by k(w-1)+w+1; check + slack <= F
  cyc-branch : S cyclic, retreat insufficient; every non-cyclic predecessor P of S
               is itself classified by lemmaD/lemmaD2/rotation/dead-end/sandwich
               recursively to depth 4 with an explicit chain-length budget
  exact-h    : none of the above; report exhaustive h(S)+delta(S) vs F (k small)

Output: per (r,k) a list of unclassified states -- the genuine obstruction set.
"""
from __future__ import annotations

import json
import sys
import time

from bs_core import T, depth_forward, inverse_tree_height, is_boundary, predecessors, step
from entry_states_r3 import partitions_into_at_most


def lemma_D(mu):
    return len(mu) == 1 or mu[0] - mu[1] >= 3


USE_DPRIME = False  # conjectural Lemma D': mu_1 >= m+3  =>  h(mu) <= n - m - 2


def lemma_Dprime(mu):
    return USE_DPRIME and mu[0] >= len(mu) + 3


def lemma_Dq_bound(mu, n):
    """Lemma Dq (proved, RESULT.md 9.4): if the q largest parts M_1>=...>=M_q>=3 exceed
    all other parts by >= 3, then h(mu) <= (n - sum M_i)//q + q. Returns the best bound
    over admissible q, or None."""
    best = None
    S = 0
    m = len(mu)
    for q in range(1, m + 1):
        S += mu[q - 1]
        if mu[q - 1] < 3:
            break
        if q == m or mu[q] <= mu[q - 1] - 3:
            b = (n - S) // q + q
            if best is None or b < best:
                best = b
    return best


def lemma_D2(mu):
    return len(mu) >= 2 and mu[1] >= 3 and (len(mu) == 2 or mu[2] <= mu[1] - 3)


def rotation_excluded(S, k, moves):
    cur = S
    for j in range(moves + 1):
        if not any(h >= k + 1 - c for c, h in enumerate(cur)):
            return False
        if j < moves:
            m = len(cur)
            uns = [m] + [x - 1 for x in cur if x > 1]
            if uns != sorted(uns, reverse=True):
                return False
            cur = step(cur)
    return True


def forward_sandwich_bound(S, k, horizon):
    """If the counts of S, B(S), ... contain (k-1, k, ..., k, k+1) of width w starting
    j moves after S, then time(S) <= k(w-1) - j, i.e. p <= k(w-1) - j - 1.
    Return the best (smallest) such bound on p, or None."""
    cs = []
    cur = S
    for _ in range(horizon + 1):
        cs.append(len(cur))
        cur = step(cur)
    best = None
    for j in range(len(cs)):
        if cs[j] != k - 1:
            continue
        q = j + 1
        while q < len(cs) and cs[q] == k:
            q += 1
        if q < len(cs) and cs[q] == k + 1 and q - j >= 2:
            w = q - j
            bound = k * (w - 1) - j - 1
            if best is None or bound < best:
                best = bound
    return best


def chain_sandwich_bound(path, k):
    """path = [S, P1, P2, ...] backward from S. Forward counts are reversed.
    If a sandwich (x-1, x..x, x+1) of level x in {k-1, k} and width w >= 2 occurs in
    the forward count sequence, the retreat lemma bounds the time of its first
    state by x(w-1); return the implied bound on p (time of S minus one)."""
    counts = [len(s) for s in reversed(path)]
    m = len(counts)
    best = None
    for i in range(m):
        x = counts[i] + 1
        if x not in (k - 1, k):
            continue
        q = i + 1
        while q < m and counts[q] == x:
            q += 1
        if q < m and counts[q] == x + 1 and q - i >= 2:
            w = q - i
            # state at forward position i has time <= x(w-1); S is m-1-i steps later
            bound = x * (w - 1) + (m - 1 - i) - 1
            if best is None or bound < best:
                best = bound
    return best


def p_bound_dfs(S, n, k, budget, node_limit=600000):
    """Upper bound on p = distance from any non-cyclic ancestor to S, by DFS over
    inverse chains, closing each branch by: dead end, chain sandwich, Lemma D, or
    Lemma D2. Returns (bound, stats) or (None, stats) if some branch is not closed
    within the depth budget / node limit."""
    stats = {"nodes": 0, "leaves": {}}
    best_overall = 0
    stack = [[S]]
    while stack:
        path = stack.pop()
        stats["nodes"] += 1
        if stats["nodes"] > node_limit:
            return None, stats
        P = path[-1]
        depth = len(path) - 1  # P = B^{-depth}(S)
        if depth > 0:
            sb = chain_sandwich_bound(path, k)
            if sb is not None:
                best_overall = max(best_overall, sb)
                stats["leaves"]["chain-sandwich"] = stats["leaves"].get("chain-sandwich", 0) + 1
                continue
            if not is_boundary(P, n):
                if lemma_Dprime(P):
                    best_overall = max(best_overall, depth + n - len(P) - 2)
                    stats["leaves"]["D'"] = stats["leaves"].get("D'", 0) + 1
                    continue
                dq = lemma_Dq_bound(P, n)
                if dq is not None:
                    best_overall = max(best_overall, depth + dq)
                    stats["leaves"]["Dq"] = stats["leaves"].get("Dq", 0) + 1
                    continue
                if lemma_D(P):
                    best_overall = max(best_overall, depth + n - P[0] + 1)
                    stats["leaves"]["D"] = stats["leaves"].get("D", 0) + 1
                    continue
                if lemma_D2(P):
                    best_overall = max(best_overall, depth + (n - P[0] - P[1]) // 2 + 2)
                    stats["leaves"]["D2"] = stats["leaves"].get("D2", 0) + 1
                    continue
        preds = [q for q in predecessors(P) if not is_boundary(q, n)]
        if not preds:
            best_overall = max(best_overall, depth)
            stats["leaves"]["dead-end"] = stats["leaves"].get("dead-end", 0) + 1
            continue
        if depth >= budget:
            return None, stats
        for q in preds:
            stack.append(path + [q])
    return best_overall, stats


def classify(S, n, k, F, typ, L, retreat_p, depth_budget=40):
    moves_allowed = k - 1 if typ == 1 else k - 2
    delta = depth_forward(S)
    cyc = is_boundary(S, n)
    if cyc and retreat_p <= F:
        return "cyclic-retreat", {}
    impossible = (not cyc) and delta > moves_allowed
    if impossible and rotation_excluded(S, k, moves_allowed):
        return "rotation-excluded", {"delta": delta}
    # slack added to p:  d <= p + delta if the cyclic state is reached from S in
    # delta <= moves_allowed moves, otherwise the generic  d <= t-1 <= p + moves_allowed
    add = 0 if cyc else (delta if delta <= moves_allowed else moves_allowed)
    if not cyc and lemma_Dprime(S) and n - len(S) - 2 + add <= F:
        return "lemmaD'", {"h_bound": n - len(S) - 2, "delta": delta}
    dqS = lemma_Dq_bound(S, n) if not cyc else None
    if dqS is not None and dqS + add <= F:
        return "lemmaDq", {"h_bound": dqS, "delta": delta}
    if not cyc and lemma_D(S) and n - S[0] + 1 + add <= F:
        return "lemmaD", {"h_bound": n - S[0] + 1, "delta": delta}
    if not cyc and lemma_D2(S) and (n - S[0] - S[1]) // 2 + 2 + add <= F:
        return "lemmaD2", {"h_bound": (n - S[0] - S[1]) // 2 + 2, "delta": delta}
    if not cyc:
        sb = forward_sandwich_bound(S, k, moves_allowed)
        if sb is not None and sb + add <= F:
            return "forward-sandwich", {"p_bound": sb, "delta": delta}
    pb, stats = p_bound_dfs(S, n, k, depth_budget)
    if pb is not None and pb + add <= F:
        return "branch", {"p_bound": pb, "delta": delta, "dfs": stats}
    return ("UNCLASSIFIED-impossible" if impossible else "UNCLASSIFIED"), {
        "delta": delta, "cyclic": cyc, "dfs_p_bound": pb, "dfs": stats}


def analyse(r, k, exact_h=True):
    n = T(k - 1) + r
    F = (k - 1) * (k - r - 2)
    rows = []
    for typ, x in ((1, k), (2, k - 1)):
        Lmax = k - 1 if typ == 1 else k
        for L in range(2, Lmax + 1):
            gen_add = k - 1 if typ == 1 else k - 2
            if typ == 2 and L == k:
                # full width: forced single state
                s_extra = n - (k - 2) - T(k - 3)
                states = [((s_extra - k,), tuple(sorted([s_extra, k - 2] + list(range(1, k - 2)), reverse=True)))]
                retreat_p = n + 1 - k
            else:
                if L == x:
                    continue  # impossible (Lemma E)
                newborn = x - 1
                free = x - L + 1
                mn = newborn + T(L - 2) + free * L
                E = n - mn
                if E < 0:
                    continue
                retreat_p = x * (L - 1)
                if retreat_p + gen_add <= F:
                    continue
                states = []
                for exc in partitions_into_at_most(E, free):
                    S = tuple(sorted([newborn] + list(range(1, L - 1)) + [L + e for e in exc], reverse=True))
                    states.append((exc, S))
            for exc, S in states:
                assert sum(S) == n
                tag, info = classify(S, n, k, F, typ, L, retreat_p)
                row = {"type": typ, "L": L, "excess": list(exc), "S": list(S), "tag": tag, **{a: b for a, b in info.items() if a not in ("branches", "dfs")}}
                if tag.startswith("UNCLASSIFIED") and exact_h:
                    h = inverse_tree_height(S)
                    row["h_exact"] = h
                    row["h+delta"] = h + info["delta"]
                    row["closes_numerically"] = h + info["delta"] <= F
                rows.append(row)
    return {"r": r, "k": k, "n": n, "F": F, "cases": rows}


if __name__ == "__main__":
    r = int(sys.argv[1]); kmin = int(sys.argv[2]); kmax = int(sys.argv[3])
    if len(sys.argv) > 4 and sys.argv[4] == "dprime":
        USE_DPRIME = True
    t0 = time.perf_counter()
    allres = []
    for k in range(kmin, kmax + 1):
        if not r < (k - 1) // 2:
            print(f"k={k}: r={r} is not a small residue, skipped"); continue
        res = analyse(r, k, exact_h=(T(k - 1) + r <= 70))
        allres.append(res)
        tags = {}
        for c in res["cases"]:
            tags[c["tag"]] = tags.get(c["tag"], 0) + 1
        print(f"\n=== r={r} k={k} n={res['n']} F={res['F']}  tags={tags}")
        for c in res["cases"]:
            if c["tag"].startswith("UNCLASSIFIED"):
                print("  ", c)
    with open(f"../evidence/toolkit-r{r}-k{kmin}-{kmax}{'-dprime' if USE_DPRIME else ''}.json", "w") as fh:
        json.dump(allres, fh, indent=1)
    print(f"done {time.perf_counter()-t0:.1f}s")
