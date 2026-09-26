#!/usr/bin/env python3
"""Independent finite check of C4. General proof is written-proof.md."""
import argparse
import json
import time


def partitions(n, cap):
    if n == 0:
        yield ()
    else:
        for first in range(min(n, cap), 0, -1):
            for rest in partitions(n - first, first):
                yield (first,) + rest


def step(state):
    return tuple(sorted((len(state),) + tuple(x - 1 for x in state if x > 1), reverse=True))


def cyclic(state, k):
    if len(state) > k:
        return False
    padded = state + (0,) * (k - len(state))
    return all(k - 1 - j <= x <= k - j for j, x in enumerate(padded))


def check(k):
    n = k * (k - 1) // 2 + 1
    expected = (k - 1) * (k - 3)
    depths = {}

    def depth(start):
        path, current = [], start
        while current not in depths and not cyclic(current, k):
            path.append(current)
            current = step(current)
        distance = depths.get(current, 0)
        depths[current] = distance
        for state in reversed(path):
            distance += 1
            depths[state] = distance
        return depths[start]

    count, maximum, extremals = 0, 0, 0
    for state in partitions(n, n):
        count += 1
        value = depth(state)
        if value > maximum:
            maximum, extremals = value, 1
        elif value == maximum:
            extremals += 1
    witness = (k - 2,) + tuple(k - i for i in range(2, k - 1)) + (2, 1)
    assert sum(witness) == n
    assert maximum == expected == depth(witness), (k, maximum, expected)
    return dict(k=k, n=n, partitions=count, maximum_depth=maximum,
                maximizing_partitions=extremals, witness=list(witness), witness_depth=depth(witness))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-k', type=int, default=9)
    args = parser.parse_args()
    if args.max_k < 5:
        parser.error('--max-k must be at least 5')
    start = time.monotonic()
    rows = [check(k) for k in range(5, args.max_k + 1)]
    print(json.dumps(dict(scope='finite exhaustive cross-check, not a general proof',
                         results=rows, seconds=round(time.monotonic() - start, 3)), indent=2))
