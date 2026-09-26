#!/usr/bin/env python3
"""Final-pattern case analysis for n = T(k-1)+3, F = (k-1)(k-5).

For each k, enumerate the sandwich cases left open by the card budget and the
retreat bound, derive the forced entry states S = B^p(lambda) (the state at
time p+1, right after the first rise of the pattern), and compute

  delta(S) = forward first-cyclic depth of S,
  h(S)     = exhaustive inverse-tree height of S over non-cyclic ancestors,

so that every trajectory through that case has d <= h(S) + delta(S).
Also records whether the case is impossible because delta(S) exceeds the
maximum number of moves allowed between S and the chosen cyclic state.

Derivation of entry states (written out in RESULT.md):
  type II, width L<=k-1: S has k-1 parts: newborn k-2, old piles 1..L-2,
      and k-L old piles of size >= L with excess E = n - min distributed.
  type I,  width L<=k-1: S has k parts: newborn k-1, old piles 1..L-2,
      and k-L+1 old piles of size >= L with excess E distributed.
  type II, width k: S = (k+2, k-2, ..., 1) (one old survivor; see RESULT.md).
"""

from __future__ import annotations

import json
import sys
import time

from bs_core import T, depth_forward, inverse_tree_height, is_boundary


def partitions_into_at_most(E: int, parts: int, maxv=None):
    """Weakly decreasing tuples of length `parts`, entries >= 0, sum E."""
    if maxv is None:
        maxv = E
    if parts == 0:
        if E == 0:
            yield ()
        return
    for a in range(min(E, maxv), -1, -1):
        for rest in partitions_into_at_most(E - a, parts - 1, a):
            yield (a,) + rest


def entry_states(k: int, typ: int, L: int):
    n = T(k - 1) + 3
    if typ == 2:
        newborn, base_count = k - 2, k - L
        old_small = list(range(1, L - 1))
    else:
        newborn, base_count = k - 1, k - L + 1
        old_small = list(range(1, L - 1))
    if L == k and typ == 2:
        # full width: k-3 old piles 1..k-3 die, newborn k-2 dies at p+k-2,
        # one old survivor of size >= k; card count forces k+2.
        S = tuple(sorted([k + 2, k - 2] + list(range(1, k - 2)), reverse=True))
        assert sum(S) == n
        return 0, [((k + 2 - k,), S)]
    minimum = newborn + sum(old_small) + base_count * L
    E = n - minimum
    if E < 0:
        return E, []
    out = []
    for exc in partitions_into_at_most(E, base_count):
        S = tuple(sorted([newborn] + old_small + [L + e for e in exc], reverse=True))
        assert sum(S) == n, (k, typ, L, S)
        out.append((exc, S))
    return E, out


def analyse(k: int, do_inverse: bool = True):
    n = T(k - 1) + 3
    F = (k - 1) * (k - 5)
    rows = []
    for typ, x, Lmax in ((1, k, k - 1), (2, k - 1, k)):
        for L in range(2, Lmax + 1):
            E, states = entry_states(k, typ, L)
            if E < 0:
                continue  # excluded by card budget
            retreat_p = x * (L - 1)
            if typ == 2 and L == k:
                retreat_p = n + 1 - k  # special lifetime bound p <= n+1-k
            # generic bound d <= t-1 <= p + (k-1 if type I else k-2)
            generic = retreat_p + (k - 1 if typ == 1 else k - 2)
            # moves from S (time p+1) to the cyclic state at time t (<= p+k for I, p+k-1 for II)
            max_moves = (k - 1) if typ == 1 else (k - 2)
            if generic <= F:
                rows.append({"type": typ, "L": L, "excess_total": E, "num_states": len(states),
                             "retreat_p_bound": retreat_p, "generic_d_bound": generic, "generic_ok": True})
                continue
            for exc, S in states:
                delta = depth_forward(S)
                cyc = is_boundary(S, n)
                impossible = delta > max_moves
                row = {
                    "type": typ, "L": L, "excess_total": E, "excess": list(exc),
                    "S": list(S), "S_cyclic": cyc, "delta": delta,
                    "impossible_case(delta>max_moves)": impossible,
                    "retreat_p_bound": retreat_p, "generic_d_bound": generic,
                    "generic_ok": generic <= F,
                }
                if do_inverse and not impossible:
                    t0 = time.perf_counter()
                    h, layers, top = inverse_tree_height(S, return_layers=True)
                    row.update({
                        "h": h, "h_plus_delta": h + delta, "closes(h+delta<=F)": h + delta <= F,
                        "inverse_layer_sizes": layers, "inverse_tree_size": sum(layers),
                        "top_ancestors": [list(a) for a in sorted(top, reverse=True)[:6]],
                        "inverse_seconds": round(time.perf_counter() - t0, 2),
                    })
                rows.append(row)
    return {"k": k, "n": n, "F": F, "cases": rows}


def main():
    kmin = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    for k in range(kmin, kmax + 1):
        res = analyse(k)
        with open(f"../evidence/entry-states-r3-k{k}.json", "w") as fh:
            json.dump(res, fh, indent=1)
        print(f"\n=== k={k} n={res['n']} F={res['F']} ===")
        for r in res["cases"]:
            if "S" not in r:
                print(f" type{r['type']} L={r['L']:2d} excess={r['excess_total']} states={r['num_states']} "
                      f"retreat_p<={r['retreat_p_bound']} generic_d<={r['generic_d_bound']} [generic-ok]")
                continue
            tag = "IMPOSSIBLE" if r["impossible_case(delta>max_moves)"] else (
                "generic-ok" if r["generic_ok"] else ("closed h+delta" if r.get("closes(h+delta<=F)") else "OPEN"))
            extra = f" h={r.get('h')} h+delta={r.get('h_plus_delta')} tree={r.get('inverse_tree_size')}" if "h" in r else ""
            print(f" type{r['type']} L={r['L']:2d} exc={tuple(r['excess'])!s:14} S={tuple(r['S'])} cyc={int(r['S_cyclic'])} "
                  f"delta={r['delta']:2d} retreat_p<={r['retreat_p_bound']} generic_d<={r['generic_d_bound']}{extra} [{tag}]", flush=True)


if __name__ == "__main__":
    main()
