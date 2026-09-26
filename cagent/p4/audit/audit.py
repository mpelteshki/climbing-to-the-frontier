#!/usr/bin/env python3
"""Independent direct checks of finite-search output and small residue CSPs."""

import argparse
from itertools import combinations
import json
from math import gcd, lcm
from pathlib import Path
from collections import Counter
from time import monotonic


def direct_density_witness(xs):
    # Enumerates every position subset. It intentionally does not call the
    # branch-and-bound predicates from enumerate.py.
    for size in range(2, len(xs) + 1):
        for positions in combinations(range(len(xs)), size):
            ys = [xs[i] for i in positions]
            period = 1
            for a, b in combinations(ys, 2):
                period = lcm(period, gcd(a, b))
            occupied = sum(period // gcd(y, period) for y in ys)
            if occupied > period:
                return {"positions": positions, "moduli": ys,
                        "M": period, "total": occupied}
    return None


def residues(xs, deadline=None):
    """Exact finite-domain CSP, returning one residue list or None.

    The first residue can be zero by translating every congruence class.
    Equal moduli are ordered by residue, since their positions are symmetric.
    """
    if not xs:
        return []
    n = len(xs)
    pair = [[gcd(xs[i], xs[j]) for j in range(n)] for i in range(n)]
    limits = [lcm(*(pair[i][j] for j in range(n) if j != i)) for i in range(n)]
    chosen = [-1] * n
    chosen[0] = 0

    def search():
        if deadline is not None and monotonic() >= deadline:
            raise TimeoutError("residue search deadline")
        if all(value >= 0 for value in chosen):
            return chosen.copy()
        best_index = None
        best_options = None
        for i, modulus in enumerate(limits):
            if chosen[i] >= 0:
                continue
            options = []
            for value in range(modulus):
                if any(chosen[j] >= 0 and (value - chosen[j]) % pair[i][j] == 0
                       for j in range(n) if j != i):
                    continue
                if any(xs[j] == modulus and chosen[j] >= 0 and
                       ((j < i and chosen[j] >= value) or (j > i and chosen[j] <= value))
                       for j in range(n) if j != i):
                    continue
                options.append(value)
            if not options:
                return None
            if best_options is None or len(options) < len(best_options):
                best_index, best_options = i, options
        for value in best_options:
            chosen[best_index] = value
            found = search()
            if found is not None:
                return found
            chosen[best_index] = -1
        return None

    return search()


def maximal_power_failure(xs):
    for i, x in enumerate(xs):
        n = x
        p = 2
        while p * p <= n:
            if n % p == 0:
                q = 1
                while n % p == 0:
                    q *= p
                    n //= p
                if sum(y % q == 0 for y in xs) == 1:
                    return {"position": i, "modulus": x, "prime_power": q}
            p += 1
        if n > 1 and sum(y % n == 0 for y in xs) == 1:
            return {"position": i, "modulus": x, "prime_power": n}
    return None


def valid_residues(xs, rs):
    return rs is not None and len(rs) == len(xs) and all(0 <= r < m for r, m in zip(rs, xs)) and all(
        (rs[i] - rs[j]) % gcd(xs[i], xs[j]) != 0 for i, j in combinations(range(len(xs)), 2))


def audit(run_paths):
    positive = (6, 6, 6, 6, 6, 6)
    positive_residues = residues(positive)
    assert valid_residues(positive, positive_residues)
    minimal = (10, 10, 10, 10, 10, 12, 45)
    assert direct_density_witness(minimal) is None
    assert residues(minimal) is None
    deletions = []
    for i in range(len(minimal)):
        sub = minimal[:i] + minimal[i+1:]
        found = residues(sub)
        assert valid_residues(sub, found)
        deletions.append({"removed_position": i, "moduli": sub, "residues": found})
    full_candidate = (10,)*5 + (12,)*4 + (24, 36, 40, 45)
    small = []
    seen = set()
    for size in range(1, 7):
        for sub in combinations(full_candidate, size):
            if sub in seen:
                continue
            seen.add(sub)
            found = residues(sub)
            assert valid_residues(sub, found)
            small.append({"moduli": sub, "residues": found})
    small_counts = {str(size): sum(len(item["moduli"]) == size for item in small)
                    for size in range(1, 7)}
    output = {"positive_control": {"moduli": positive, "residues": positive_residues},
              "minimal_residue_obstruction": {"moduli": minimal,
                 "every_single_deletion_has_witness": deletions}, "runs": []}
    output["all_small_submultisets_of_full_13_candidate"] = {
        "counts_by_size": small_counts, "witnesses": small}
    for path in run_paths:
        for line in Path(path).read_text().splitlines():
            result = json.loads(line)
            k = result["k"]
            base = result["base_survivors"]
            reduced = result["reduced_survivors"]
            explanations = []
            for xs in base:
                assert len(xs) == k and list(sorted(xs)) == xs
                assert all(1 < gcd(a, b) < k for a, b in combinations(xs, 2))
                assert all(lcm(*range(1, k)) % x == 0 for x in xs)
                assert sum(x % (k-1) == 0 for x in xs) >= 3
                assert direct_density_witness(xs) is None
                failure = maximal_power_failure(xs)
                if failure is None:
                    assert xs in reduced
                    assert not (Counter(minimal) - Counter(xs))
                    failure = {"rule": "residue_obstruction", "submultiset": minimal}
                else:
                    assert xs not in reduced
                    failure = {"rule": "prime_power_support", **failure}
                explanations.append({"moduli": xs, "obstruction": failure})
            output["runs"].append({"k": k, "complete": result["complete"],
                                   "base_count": len(base), "reduced_count": len(reduced),
                                   "survivor_obstructions": explanations})
    return output


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("runs", nargs="+")
    args = parser.parse_args()
    print(json.dumps(audit(args.runs), sort_keys=True))
