"""Exact, small calibration experiments. No novelty or formal-proof claims."""
import itertools
import json
import random


def graph_experiment():
    results = []
    smallest_counterexample = None
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2))
        count = 0
        max_edges = 0
        for mask in range(1 << len(pairs)):
            adj = [0] * n
            edges = []
            for i, (u, v) in enumerate(pairs):
                if mask & (1 << i):
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
                    edges.append((u, v))
            if any(adj[u] & adj[v] for u, v in edges):
                continue
            count += 1
            max_edges = max(max_edges, len(edges))
            if smallest_counterexample is None:
                alpha = max(s.bit_count() for s in range(1 << n)
                            if all(not (s & (1 << u) and adj[u] & s)
                                   for u in range(n)))
                if 2 * alpha < n:
                    smallest_counterexample = {
                        "claim": "Every triangle-free graph has independence number at least n/2",
                        "n": n, "alpha": alpha, "edges": edges,
                    }
        results.append({"n": n, "triangle_free_labeled_graphs": count,
                        "maximum_edges": max_edges,
                        "mantel_bound": n * n // 4})
    return {"exhaustive_domain": "All labeled simple graphs on 1 through 6 vertices",
            "results": results, "smallest_counterexample": smallest_counterexample}


def cap_experiment():
    points = list(itertools.product(range(3), repeat=3))
    best = []
    for seed in range(100):
        order = points.copy()
        random.Random(seed).shuffle(order)
        cap = []
        forbidden = set()
        for x in order:
            if x in forbidden:
                continue
            for y in cap:
                forbidden.add(tuple((-a-b) % 3 for a, b in zip(x, y)))
            cap.append(x)
        if len(cap) > len(best):
            best = cap
    # Separate checker uses direct enumeration, not search's forbidden-point logic.
    violating_triples = [triple for triple in itertools.combinations(best, 3)
                         if all(sum(p[j] for p in triple) % 3 == 0 for j in range(3))]
    assert len(set(best)) == len(best)
    assert not violating_triples
    return {"dimension": 3, "baseline_binary_cube_size": 8,
            "trials": 100, "best_size": len(best), "points": best,
            "independently_checked_triples": len(list(itertools.combinations(best, 3))),
            "claim": "Explicit valid construction; no optimality or novelty claim"}


if __name__ == "__main__":
    print(json.dumps({"graphs": graph_experiment(), "cap_set": cap_experiment()}, indent=2))
