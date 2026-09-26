"""Independent exhaustive Q5 decycling-13 replay (not a Lean proof).

The Hamming-weight parity classes have 16 vertices each. XOR 1 preserves every
edge and swaps the classes, so every 13-set has a representative whose smaller
class is even, of size k<=6. For a 13-set S, the 19-vertex complement has
80-5*13+e(S)=15+e(S) edges. A forest has at most 18, hence e(S)<=3.
For a fixed even subset A, an odd vertex contributes its number of neighbors
in A to the number of internal edges. Thus the cheapest 13-k odd vertices
give a rigorous lower bound on that edge count. Cases k=3..6 exceed three
edges. For k=0..2, enumerate every affordable odd subset and test the
19-vertex complement for a cycle using union-find on bit-flip edges.
"""

from hashlib import sha256
from itertools import combinations


def parity(vertex: int) -> int:
    return vertex.bit_count() % 2


even = tuple(vertex for vertex in range(32) if parity(vertex) == 0)
odd = tuple(vertex for vertex in range(32) if parity(vertex) == 1)
assert len(even) == len(odd) == 16


def neighbors_in(vertex: int, selected: tuple[int, ...]) -> int:
    return sum((vertex ^ other).bit_count() == 1 for other in selected)


def internal_edges(selected: set[int]) -> int:
    return sum(
        (vertex ^ (1 << bit)) in selected
        for vertex in selected
        for bit in range(5)
        if vertex < (vertex ^ (1 << bit))
    )


def complement_is_forest(selected: set[int]) -> bool:
    retained = set(range(32)) - selected
    parent = list(range(32))

    def root(vertex: int) -> int:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    for vertex in sorted(retained):
        for bit in range(5):
            neighbor = vertex ^ (1 << bit)
            if neighbor not in retained or neighbor < vertex:
                continue
            a, b = root(vertex), root(neighbor)
            if a == b:
                return False
            parent[a] = b
    return True


def affordable_odd_sets(
    degrees: tuple[int, ...], required: int, budget: int = 3
):
    def visit(index: int, chosen: tuple[int, ...], cost: int):
        if len(chosen) == required:
            yield chosen, cost
            return
        if index == 16 or len(chosen) + 16 - index < required:
            return
        if cost + degrees[index] <= budget:
            yield from visit(index + 1, chosen + (odd[index],), cost + degrees[index])
        yield from visit(index + 1, chosen, cost)

    yield from visit(0, (), 0)


digest = sha256()
total_candidates = 0
total_forests = 0
five_zero_cases = 0
max_one_at_five_zero = 0
for k in range(7):
    even_cases = 0
    candidates = 0
    forests = 0
    min_cost = 81
    max_zero = 0
    for selected_even in combinations(even, k):
        even_cases += 1
        degrees = tuple(neighbors_in(vertex, selected_even) for vertex in odd)
        min_cost = min(min_cost, sum(sorted(degrees)[: 13 - k]))
        max_zero = max(max_zero, degrees.count(0))
        if k == 5 and degrees.count(0) == 5:
            five_zero_cases += 1
            max_one_at_five_zero = max(max_one_at_five_zero, degrees.count(1))
        if k >= 3:
            continue
        for selected_odd, cost in affordable_odd_sets(degrees, 13 - k):
            selected = set(selected_even) | set(selected_odd)
            assert len(selected) == 13
            assert cost == internal_edges(selected) <= 3
            candidates += 1
            digest.update(bytes(sorted(selected)))
            if complement_is_forest(selected):
                forests += 1
    if k >= 3:
        assert min_cost >= 4
    print(
        f"k={k}: even_subsets={even_cases}, min_edges={min_cost}, "
        f"max_zero_neighbors={max_zero}, candidates_le3={candidates}, forests={forests}"
    )
    total_candidates += candidates
    total_forests += forests

assert five_zero_cases > 0 and max_one_at_five_zero == 0
assert total_forests == 0
print(f"k=5, zero_neighbors=5: cases={five_zero_cases}, max_one_neighbors={max_one_at_five_zero}")
print(f"total_candidates_le3={total_candidates}, forests={total_forests}")
print(f"candidate_stream_sha256={digest.hexdigest()}")
