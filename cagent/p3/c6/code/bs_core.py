#!/usr/bin/env python3
"""Independent Bulgarian-solitaire core (Fable P3 C6, residue r=3 focus).

Written from the definitions only. Nothing here imports Grok or Codex code.

Conventions
-----------
* A partition is a tuple of positive ints in weakly decreasing order.
* step(lam): remove one card from every pile, drop zeros, add a pile equal
  to the old number of piles, sort decreasing.
* Count index i (i >= 1) refers to the state B^{i-1}(lam); c_i = #piles.
* T(k) = k(k+1)/2; rank k is T(k-1) < n <= T(k); residue r = n - T(k-1).
"""

from __future__ import annotations

from typing import Dict, Iterator, List, Tuple

Part = Tuple[int, ...]


def T(k: int) -> int:
    return k * (k + 1) // 2


def rank_residue(n: int) -> Tuple[int, int]:
    k = 1
    while T(k) < n:
        k += 1
    return k, n - T(k - 1)


def step(lam: Part) -> Part:
    m = len(lam)
    out = [x - 1 for x in lam if x > 1]
    out.append(m)
    out.sort(reverse=True)
    return tuple(out)


def predecessors(mu: Part) -> Iterator[Part]:
    """All lam with step(lam) == mu.

    The newborn pile of the move lam -> mu is a part s of mu, and lam had
    exactly s parts. The other len(mu)-1 parts of mu came from s parts of
    lam that survived; the remaining s-(len(mu)-1) parts of lam were ones
    that died. Hence s >= len(mu)-1 is necessary, and each admissible
    distinct value s gives exactly one lam.
    """
    m = len(mu)
    for s in sorted(set(mu), reverse=True):
        if s < m - 1:
            continue
        rest = list(mu)
        rest.remove(s)
        lam = [x + 1 for x in rest] + [1] * (s - m + 1)
        lam.sort(reverse=True)
        yield tuple(lam)


def is_cyclic_direct(lam: Part) -> bool:
    """Cycle detection by iteration only (no classification used)."""
    seen = {lam}
    cur = step(lam)
    while cur not in seen:
        if cur == lam:
            return True
        seen.add(cur)
        cur = step(cur)
    return cur == lam


def boundary_word(lam: Part, k: int):
    """If lam == (k-1+e0, k-2+e1, ..., 0+e_{k-1}) with bits e, return the
    bit tuple; else None. Trailing zero part omitted in lam."""
    padded = list(lam) + [0] * (k - len(lam))
    if len(padded) != k:
        return None
    bits = []
    for j in range(k):
        e = padded[j] - (k - 1 - j)
        if e not in (0, 1):
            return None
        bits.append(e)
    return tuple(bits)


def is_boundary(lam: Part, n: int | None = None) -> bool:
    if n is None:
        n = sum(lam)
    k, r = rank_residue(n)
    w = boundary_word(lam, k)
    return w is not None and sum(w) == r


def depth_forward(lam: Part) -> int:
    """First index i with B^i(lam) cyclic, by direct iteration: walk until a
    state repeats; the first repeated state is the cycle entry."""
    seen: Dict[Part, int] = {}
    cur = lam
    i = 0
    while cur not in seen:
        seen[cur] = i
        cur = step(cur)
        i += 1
    return seen[cur]


def trajectory(lam: Part, moves: int) -> List[Part]:
    out = [lam]
    for _ in range(moves):
        out.append(step(out[-1]))
    return out


def counts(lam: Part, length: int) -> List[int]:
    """c_1..c_length: pile counts of B^{i-1}(lam)."""
    cs = []
    cur = lam
    for _ in range(length):
        cs.append(len(cur))
        cur = step(cur)
    return cs


def num_partitions(n: int) -> int:
    p = [1] + [0] * n
    for part in range(1, n + 1):
        for s in range(part, n + 1):
            p[s] += p[s - part]
    return p[n]


def all_partitions(n: int, max_part: int | None = None) -> Iterator[Part]:
    if n == 0:
        yield ()
        return
    if max_part is None or max_part > n:
        max_part = n
    for a in range(max_part, 0, -1):
        for rest in all_partitions(n - a, a):
            yield (a,) + rest


def cyclic_states(n: int) -> List[Part]:
    """All cyclic partitions of n as binary boundaries (C1 / Brandt form).
    Cross-checked against is_cyclic_direct by check_prereqs.py."""
    k, r = rank_residue(n)
    out = []
    from itertools import combinations

    for ones in combinations(range(k), r):
        bits = [0] * k
        for j in ones:
            bits[j] = 1
        lam = tuple(x for x in (k - 1 - j + bits[j] for j in range(k)) if x > 0)
        out.append(lam)
    return out


def depth_layers(n: int, verbose: bool = False):
    """Backward BFS from the cyclic states.

    Layer 0 = cyclic states. Layer j+1 = non-cyclic predecessors of layer j.
    Every partition has a unique successor, so it lies in exactly one layer
    and predecessors of distinct states are distinct: no hash set is needed
    across or within layers. Returns (layer_sizes, last_layer_states).
    The total of the sizes must equal p(n); the caller checks that.
    """
    layer = cyclic_states(n)
    sizes = [len(layer)]
    while True:
        nxt: List[Part] = []
        if len(sizes) == 1:
            # exclude cyclic predecessors only at the first backward step
            for mu in layer:
                for lam in predecessors(mu):
                    if not is_boundary(lam, n):
                        nxt.append(lam)
        else:
            for mu in layer:
                nxt.extend(predecessors(mu))
        if not nxt:
            return sizes, layer
        sizes.append(len(nxt))
        if verbose:
            print(f"  layer {len(sizes)-1}: {len(nxt)}", flush=True)
        layer = nxt


def inverse_tree_height(S: Part, return_layers: bool = False):
    """h(S) = max p such that some lam has B^p(lam) = S (S itself: p=0).
    Exhaustive backward search; finite because the functional graph on
    partitions of n is finite and S is assumed non-cyclic or the search is
    restricted to non-cyclic predecessors."""
    n = sum(S)
    layer = [S]
    layers = [1]
    while True:
        nxt = []
        for mu in layer:
            for lam in predecessors(mu):
                if not is_boundary(lam, n):
                    nxt.append(lam)
        if not nxt:
            break
        layers.append(len(nxt))
        layer = nxt
    if return_layers:
        return len(layers) - 1, layers, layer
    return len(layers) - 1


def L_formula(n: int) -> int:
    """Griggs-Ho Theorem 4.5 lower bound / Conjecture 4.7 value, n >= 3."""
    if n <= 2:
        return 0
    k, r = rank_residue(n)
    lo, hi = (k - 1) // 2, (k + 1) // 2
    if r < lo:
        return (k - 1) * (k - r - 2)
    if r in (lo, hi):
        return n - k + 1
    return (r - 2) * k + r
