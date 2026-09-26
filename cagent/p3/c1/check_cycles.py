#!/usr/bin/env python3
"""Finite independent cross-check of the general written C1 counting proof."""
import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
from math import comb, gcd
from pathlib import Path
import time


def partitions(n, cap=None):
    if n == 0:
        yield ()
        return
    for first in range(min(n, n if cap is None else cap), 0, -1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


def step(state):
    return tuple(sorted([len(state)] + [a - 1 for a in state if a > 1], reverse=True))


def actual_cycles(n):
    states = set(partitions(n))
    finished = set()
    cycles = set()
    for start in states:
        if start in finished:
            continue
        path = []
        position = {}
        current = start
        while current not in finished and current not in position:
            assert current in states
            position[current] = len(path)
            path.append(current)
            current = step(current)
        if current in position:
            cycles.add(frozenset(path[position[current]:]))
        finished.update(path)
    assert finished == states
    return states, cycles


def totient(d):
    return sum(gcd(i, d) == 1 for i in range(1, d + 1))


def formula(k, r):
    numerator = sum(totient(d) * comb(k // d, r // d)
                    for d in range(1, gcd(k, r) + 1) if k % d == r % d == 0)
    assert numerator % k == 0
    return numerator // k


def boundary_cycles(k, r):
    cycles = set()
    for chosen in combinations(range(k), r):
        word = tuple(int(j in chosen) for j in range(k))
        cycle = set()
        for t in range(k):
            rotated = word[t:] + word[:t]
            state = tuple(k - 1 - j + bit for j, bit in enumerate(rotated)
                          if k - 1 - j + bit > 0)
            cycle.add(state)
        cycles.add(frozenset(cycle))
    return cycles


def check(n):
    k = 1
    while k * (k + 1) // 2 < n:
        k += 1
    r = n - k * (k - 1) // 2
    states, actual = actual_cycles(n)
    encoded = boundary_cycles(k, r)
    expected = formula(k, r)
    assert actual == encoded, (n, 'actual cycles differ from binary-boundary cycles')
    assert len(actual) == expected, (n, len(actual), expected)
    cyclic_states = set().union(*actual)
    assert len(cyclic_states) == comb(k, r)
    histogram = dict(sorted(Counter(map(len, actual)).items()))
    assert all(k % period == 0 for period in histogram)
    return dict(n=n, rank=k, weight=r, partitions=len(states), cyclic_partitions=len(cyclic_states),
                cycles=len(actual), formula=expected, cycle_length_histogram=histogram)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=40)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'evidence/cycle-counts.json')
    args = parser.parse_args()
    if args.max_n < 1:
        parser.error('--max-n must be positive')
    started = time.monotonic()
    records = [check(n) for n in range(1, args.max_n + 1)]
    report = dict(status='PASS', scope=f'Finite cross-check only: 1 <= n <= {args.max_n}',
                  general_count_formula_lean_verified=False,
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  partitions_checked=sum(row['partitions'] for row in records),
                  seconds=round(time.monotonic() - started, 3), records=records)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(f"PASS: n=1..{args.max_n}; {report['partitions_checked']} partitions; "
          f"{report['seconds']}s. General formula remains a written proof.")


if __name__ == '__main__':
    main()
