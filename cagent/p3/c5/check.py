#!/usr/bin/env python3
"""Exact finite C5 cross-check by detecting cycles directly; not a general proof."""
import argparse
import json
from pathlib import Path
import runpy
import time

helpers = runpy.run_path(str(Path(__file__).resolve().parents[1] / 'c4/check.py'))
partitions, step = helpers['partitions'], helpers['step']


def check(k):
    n = k * (k - 1) // 2 + 2
    expected = {2: 2, 3: 3, 4: 5, 5: 8, 6: 12}.get(k, (k - 1) * (k - 4))
    depths = {}

    def depth(start):
        path, seen, current = [], {}, start
        while current not in depths and current not in seen:
            seen[current] = len(path)
            path.append(current)
            current = step(current)
        if current in seen:
            boundary = seen[current]
            for state in path[boundary:]:
                depths[state] = 0
            path = path[:boundary]
            distance = 0
        else:
            distance = depths[current]
        for state in reversed(path):
            distance += 1
            depths[state] = distance
        return depths[start]

    count, maximum, maximizing = 0, -1, 0
    for state in partitions(n, n):
        count += 1
        value = depth(state)
        if value > maximum:
            maximum, maximizing = value, 1
        elif value == maximum:
            maximizing += 1
    if k >= 7:
        witness = (k - 2,) + tuple(k - i for i in range(2, k - 2)) + (3, 2, 1)
    elif k == 5:
        witness = (3, 3, 2, 2, 1, 1)
    else:
        witness = (1,) * n
    assert sum(witness) == n
    assert maximum == expected == depth(witness), (k, maximum, expected)
    return dict(k=k, n=n, partitions=count, maximum_depth=maximum,
                maximizing_partitions=maximizing, witness=list(witness), witness_depth=depth(witness))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-k', type=int, default=10)
    args = parser.parse_args()
    if args.max_k < 2:
        parser.error('--max-k must be at least 2')
    start = time.monotonic()
    rows = [check(k) for k in range(2, args.max_k + 1)]
    print(json.dumps(dict(scope='finite exhaustive cross-check by direct cycle detection, not a general proof',
                         results=rows, seconds=round(time.monotonic() - start, 3)), indent=2))
