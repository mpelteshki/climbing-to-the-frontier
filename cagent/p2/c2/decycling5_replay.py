#!/usr/bin/env python3
"""Exact Q5 obstruction search. Uses only the Python standard library.

An induced forest after deleting at most 13 vertices would require exactly 13
deleted vertices and at most three edges among them. It would also require the
deleted set to meet every 4- and 6-cycle. This script exhausts those conditions.
The returned UNSAT result is a reproducible computation, not a Lean theorem.
"""

from functools import lru_cache
from hashlib import sha256
from pathlib import Path
from time import perf_counter

DIMENSION = 5
VERTICES = 1 << DIMENSION
MAX_DELETIONS = 13
MAX_INTERNAL_EDGES = 3


def adjacent(u: int, v: int) -> bool:
    return (u ^ v).bit_count() == 1


def edge_pairs() -> tuple[tuple[int, int], ...]:
    return tuple(
        (u, u ^ (1 << bit))
        for u in range(VERTICES)
        for bit in range(DIMENSION)
        if not (u & (1 << bit))
    )


def short_cycles() -> tuple[tuple[int, ...], ...]:
    by_vertex_set: dict[tuple[int, ...], tuple[int, ...]] = {}

    def visit(path: tuple[int, ...], length: int) -> None:
        if len(path) == length:
            if adjacent(path[-1], path[0]):
                key = tuple(sorted(path))
                reverse = (path[0],) + tuple(reversed(path[1:]))
                representative = min(path, reverse)
                old = by_vertex_set.get(key)
                if old is None or representative < old:
                    by_vertex_set[key] = representative
            return
        for bit in range(DIMENSION):
            neighbor = path[-1] ^ (1 << bit)
            if neighbor > path[0] and neighbor not in path:
                visit(path + (neighbor,), length)

    for start in range(VERTICES):
        for length in (4, 6):
            visit((start,), length)

    result = tuple(sorted(by_vertex_set.values(), key=lambda cycle: (len(cycle), cycle)))
    assert sum(len(cycle) == 4 for cycle in result) == 80
    assert sum(len(cycle) == 6 for cycle in result) == 640
    for cycle in result:
        assert len(set(cycle)) == len(cycle)
        assert all(0 <= vertex < VERTICES for vertex in cycle)
        assert all(adjacent(cycle[i], cycle[(i + 1) % len(cycle)])
                   for i in range(len(cycle)))
    return result


def main() -> None:
    started = perf_counter()
    edges = edge_pairs()
    cycles = short_cycles()
    assert len(edges) == 80 and len(set(edges)) == 80
    assert all(0 <= u < v < VERTICES and adjacent(u, v) for u, v in edges)

    neighbor_masks = tuple(
        sum(1 << (vertex ^ (1 << bit)) for bit in range(DIMENSION))
        for vertex in range(VERTICES)
    )
    cycle_masks = tuple(sum(1 << vertex for vertex in cycle) for cycle in cycles)
    visited = 0
    branch_calls = 0

    @lru_cache(maxsize=None)
    def search(deleted: int) -> int | None:
        nonlocal visited, branch_calls
        visited += 1
        if deleted.bit_count() > MAX_DELETIONS:
            return None
        internal_edges = sum(
            bool((deleted & (1 << u)) and (deleted & (1 << v))) for u, v in edges
        )
        if internal_edges > MAX_INTERNAL_EDGES:
            return None

        for cycle_mask in cycle_masks:
            if deleted & cycle_mask == 0:
                break
        else:
            return deleted

        if deleted.bit_count() == MAX_DELETIONS:
            return None

        remaining = cycle_mask
        while remaining:
            vertex_bit = remaining & -remaining
            remaining ^= vertex_bit
            vertex = vertex_bit.bit_length() - 1
            # Exact pruning: adding a vertex cannot remove an internal edge.
            if internal_edges + (deleted & neighbor_masks[vertex]).bit_count() > MAX_INTERNAL_EDGES:
                continue
            branch_calls += 1
            witness = search(deleted | vertex_bit)
            if witness is not None:
                return witness
        return None

    witness = search(0)
    elapsed = perf_counter() - started
    source_hash = sha256(Path(__file__).read_bytes()).hexdigest()
    inventory = repr((edges, cycles)).encode("ascii")
    print(f"edges={len(edges)} squares=80 hexagons=640")
    print(f"source_sha256={source_hash}")
    print(f"inventory_sha256={sha256(inventory).hexdigest()}")
    print(f"distinct_states={visited} recursive_branches={branch_calls}")
    print(f"result={'UNSAT' if witness is None else 'SAT'} elapsed_seconds={elapsed:.3f}")
    if witness is not None:
        print("counterexample_deletion_set=", [v for v in range(VERTICES) if witness & (1 << v)])
        raise SystemExit(1)


if __name__ == "__main__":
    main()
