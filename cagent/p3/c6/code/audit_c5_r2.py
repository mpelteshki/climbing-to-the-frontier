#!/usr/bin/env python3
"""Independent numerical audit of the reused Codex C5 (r=2) claims.

Does not import Codex code. Checks for k = 7..KMAX:
  * width k-3 excess states: (3,0,0),(2,1,0) cyclic; (1,1,1) = S_k noncyclic
    for k-2 moves (cell on diagonal k+1 throughout, no sorting).
  * width k-2 entry states A_k, B_k cyclic; their unique noncyclic
    predecessors are P_k=(k+1,k-1,k-3..2) and P'_k=(k,k,k-3..2).
  * full width state (k+1,k-2,...,1) has depth 1.
  * exact inverse-tree heights of A_k and B_k for k <= 12 satisfy the
    written bounds (A_k: <= n-k+1 ; B_k: <= 3 + F//4) and h <= F.
  * U_7, U_8 inverse layers 1,1,1,1,2,3,4,4,0 and 1,1,0; forward depths 5, 6.
  * D_B(T_{k-1}+2) for k=2..10 by exhaustive backward layering equals
    2,3,5,8,12 (k<=6) and (k-1)(k-4) (k>=7).
"""

from __future__ import annotations

import json
import sys
import time

from bs_core import (
    T,
    cyclic_states,
    depth_forward,
    inverse_tree_height,
    is_boundary,
    num_partitions,
    predecessors,
    step,
)

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 30


def exhaustive_D(n):
    layer = cyclic_states(n)
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
    return len(sizes) - 1


def main():
    t0 = time.perf_counter()
    out = {"k_range": [7, KMAX]}
    for k in range(7, KMAX + 1):
        n = T(k - 1) + 2
        F = (k - 1) * (k - 4)
        stair = list(range(k - 5, 0, -1))
        S = {
            (3, 0, 0): tuple(sorted([k - 2, k, k - 3, k - 3] + stair, reverse=True)),
            (2, 1, 0): tuple(sorted([k - 2, k - 1, k - 2, k - 3] + stair, reverse=True)),
            (1, 1, 1): tuple(sorted([k - 2, k - 2, k - 2, k - 2] + stair, reverse=True)),
        }
        for s in S.values():
            assert sum(s) == n
        assert is_boundary(S[(3, 0, 0)], n) and is_boundary(S[(2, 1, 0)], n)
        Sk = S[(1, 1, 1)]
        cur = Sk
        for j in range(k - 1):
            assert any(h >= k + 1 - c for c, h in enumerate(cur)) and not is_boundary(cur, n), (k, j)
            if j < k - 2:  # the k-2 moves inside the exclusion window need no sorting
                m = len(cur)
                uns = [m] + [x - 1 for x in cur if x > 1]
                assert uns == sorted(uns, reverse=True)
            cur = step(cur)
        A = tuple([k, k - 2, k - 2] + list(range(k - 4, 0, -1)))
        Bk = tuple([k - 1, k - 1, k - 2] + list(range(k - 4, 0, -1)))
        assert is_boundary(A, n) and is_boundary(Bk, n)
        Pk = tuple([k + 1, k - 1] + list(range(k - 3, 1, -1)))
        Ppk = tuple([k, k] + list(range(k - 3, 1, -1)))
        assert [q for q in predecessors(A) if not is_boundary(q, n)] == [Pk]
        assert [q for q in predecessors(Bk) if not is_boundary(q, n)] == [Ppk]
        Wfull = tuple([k + 1, k - 2] + list(range(k - 3, 0, -1)))
        assert depth_forward(Wfull) == 1
        if k <= 12:
            hA, hB = inverse_tree_height(A), inverse_tree_height(Bk)
            assert hA <= n - k + 1 and hA <= F, (k, hA)
            assert hB <= 3 + F // 4 and hB <= F, (k, hB)
            out[f"k{k}"] = {"h_A": hA, "h_B": hB, "F": F, "n-k+1": n - k + 1, "3+F//4": 3 + F // 4}
    # U_7, U_8
    for k, U, layers_expected, depth_expected in (
        (7, (6, 4, 3, 3, 3, 3, 1), [1, 1, 1, 1, 2, 3, 4, 4], 5),
        (8, (7, 4, 4, 4, 4, 4, 2, 1), [1, 1], 6),
    ):
        n = T(k - 1) + 2
        assert sum(U) == n
        h, layers, _ = inverse_tree_height(U, return_layers=True)
        assert layers == layers_expected, (k, layers)
        assert depth_forward(U) == depth_expected
        out[f"U{k}_layers"] = layers
    # exhaustive r=2 values
    vals = {}
    for k in range(2, 11):
        n = T(k - 1) + 2
        D = exhaustive_D(n)
        expected = {2: 2, 3: 3, 4: 5, 5: 8, 6: 12}.get(k, (k - 1) * (k - 4))
        assert D == expected, (k, D, expected)
        vals[k] = D
    out["exhaustive_r2_D"] = vals
    out["seconds"] = round(time.perf_counter() - t0, 2)
    out["status"] = "PASS"
    print(json.dumps(out, indent=1))
    with open("../evidence/audit-c5-r2.json", "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
