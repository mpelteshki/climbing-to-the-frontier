#!/usr/bin/env python3
"""Independent exact uphill-path and structural-budget check for a cube order.

The primary count sums, over valleys, the numbers of ascending path suffixes.
A second endpoint recurrence and a direct enumeration on small cubes cross-check it.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def parse_order(path: Path, dimension: int) -> list[int]:
    raw = path.read_text(encoding="utf-8").strip()
    try:
        obj = json.loads(raw)
    except json.JSONDecodeError:
        obj = raw.split()
    if not isinstance(obj, list):
        raise ValueError("expected a JSON array or whitespace-separated labels")
    if all(isinstance(value, int) and not isinstance(value, bool) for value in obj):
        order = obj
    elif all(isinstance(value, str) for value in obj):
        if not all(len(value) == dimension and set(value) <= {"0", "1"} for value in obj):
            raise ValueError("binary labels must have exactly d bits")
        order = [int(value, 2) for value in obj]
    else:
        raise ValueError("order entries must be integers or fixed-width bit strings")
    n = 1 << dimension
    if len(order) != n or sorted(order) != list(range(n)):
        raise ValueError(f"not a permutation of 0,...,{n - 1}")
    return order


def verify(dimension: int, order: list[int], direct: bool = False) -> dict:
    n = 1 << dimension
    if len(order) != n or sorted(order) != list(range(n)):
        raise ValueError("invalid permutation")
    rank = [0] * n
    for position, vertex in enumerate(order):
        rank[vertex] = position
    neighbors = [tuple(vertex ^ (1 << bit) for bit in range(dimension))
                 for vertex in range(n)]
    for vertex, row in enumerate(neighbors):
        assert len(set(row)) == dimension
        assert all(0 <= other < n and (vertex ^ other).bit_count() == 1
                   for other in row)
        assert all(vertex in neighbors[other] for other in row)
    if dimension <= 9:
        # Different construction: explicit Hamming-distance edge inventory.
        hamming_edges = {(u, v) for u in range(n) for v in range(u + 1, n)
                         if (u ^ v).bit_count() == 1}
        xor_edges = {(min(u, v), max(u, v)) for u in range(n)
                     for v in neighbors[u]}
        assert hamming_edges == xor_edges
        assert len(hamming_edges) == dimension * n // 2
    lower = [tuple(u for u in neighbors[v] if rank[u] < rank[v]) for v in range(n)]
    upper = [tuple(u for u in neighbors[v] if rank[u] > rank[v]) for v in range(n)]
    valleys = [v for v in range(n) if not lower[v]]

    # Suffix DAG recurrence counts one path that stops here plus every extension.
    suffix = [0] * n
    for v in reversed(order):
        suffix[v] = 1 + sum(suffix[w] for w in upper[v])
    total = sum(suffix[v] for v in valleys)

    # Independent endpoint decomposition, useful for exact budget diagnostics.
    ending = [0] * n
    for v in order:
        ending[v] = 1 if not lower[v] else sum(ending[u] for u in lower[v])
    assert sum(ending) == total
    B = {v for v in range(n) if ending[v] > 1}
    eB = sum(u in B and v in B for u in range(n) for v in neighbors[u] if u < v)
    edge_count = dimension * n // 2
    sources = len(valleys)
    assert sources == n - edge_count + (dimension - 1) * len(B) - eB
    extension_extra = sum((ending[v] - 1) * len(upper[v]) for v in B)
    assert total == sources + edge_count + extension_extra
    excess = total - (n + (dimension - 1) * len(B))
    assert excess == extension_extra - eB >= 0
    assert all(not (v in B and w not in B) for v in B for w in upper[v])
    if direct:
        if dimension > 4:
            raise ValueError("direct enumeration reserved for d <= 4")
        def walk(v: int) -> int:
            return 1 + sum(walk(w) for w in upper[v])
        assert sum(walk(v) for v in valleys) == total
    high_even = [v for v in range(n) if v.bit_count() % 2 == 0 and ending[v] >= 3]
    high_odd = [v for v in range(n) if v.bit_count() % 2 == 1 and ending[v] >= 3]
    return {
        "dimension": dimension, "vertices": n, "edges": edge_count,
        "total_paths": total, "sources": sources,
        "B_size": len(B), "e_B": eB,
        "budget_base": n + (dimension - 1) * len(B),
        "excess": excess, "extension_extra": extension_extra,
        "valley_vertices": valleys,
        "B_vertices": sorted(B),
        "high_path_vertices_even": high_even,
        "high_path_vertices_odd": high_odd,
        "high_path_count_even": len(high_even),
        "high_path_count_odd": len(high_odd),
        "max_endpoint_paths": max(ending),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dimension", type=int)
    parser.add_argument("order", type=Path)
    parser.add_argument("--direct", action="store_true")
    args = parser.parse_args()
    result = verify(args.dimension, parse_order(args.order, args.dimension), args.direct)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
