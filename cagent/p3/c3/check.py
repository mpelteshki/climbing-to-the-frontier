#!/usr/bin/env python3
"""Compare C3 inverse construction with exhaustive forward depths."""
import json
import time
from pathlib import Path
import runpy

helpers = runpy.run_path(str(Path(__file__).resolve().parents[1] / 'c4/check.py'))
partitions, step, cyclic = (helpers[name] for name in ('partitions', 'step', 'cyclic'))


def predecessors(state):
    for size in set(state):
        if size >= len(state) - 1:
            rest = list(state)
            rest.remove(size)
            yield tuple(sorted([x + 1 for x in rest] + [1] * (size - len(state) + 1), reverse=True))


def check(k):
    n, bound = k * (k + 1) // 2 - 1, k * k - 2 * k - 1
    depths = {}
    for start in partitions(n, n):
        state, path = start, []
        while state not in depths and not cyclic(state, k):
            path.append(state)
            state = step(state)
        distance = depths.get(state, 0)
        depths[state] = distance
        for state in reversed(path):
            distance += 1
            depths[state] = distance
    maximum = max(depths.values())
    forward = {s for s, d in depths.items() if d == maximum}
    seed = tuple(range(k, 3, -1)) + (2, 1, 1, 1)
    backward = {seed}
    for _ in range(bound - 2):
        backward = {p for s in backward for p in predecessors(s)}
    assert maximum == bound
    assert forward == backward, (k, forward ^ backward)
    for start in backward:
        state = start
        for _ in range(bound - 2):
            state = step(state)
        assert state == seed
    return dict(k=k, n=n, partitions=len(depths), maximum_depth=maximum,
                maximizing_partitions=len(forward), inverse_set_equals_forward_set=True,
                seed=list(seed), k4_maximizers=[list(s) for s in sorted(forward)] if k == 4 else None)


if __name__ == '__main__':
    start = time.monotonic()
    print(json.dumps(dict(scope='finite exhaustive cross-check', results=[check(k) for k in range(4, 8)],
                          seconds=round(time.monotonic()-start, 3)), indent=2))
