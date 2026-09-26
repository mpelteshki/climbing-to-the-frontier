#!/usr/bin/env python3
"""Independent value-graph and multiplicity enumeration.

Unlike enumerate.py, this chooses distinct compatible modulus *values* first
and assigns their multiplicities. It does not choose anchor triples or grow a
sorted multiset one occurrence at a time.
"""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
import json
from math import gcd, isqrt, lcm
from time import monotonic


def divisors_with_two_primes(k):
    period = lcm(*range(1, k))
    out = [period]
    for d in range(2, isqrt(period)+1):
        if period % d == 0:
            out.extend((d, period//d))
    if isqrt(period)**2 == period:
        out.append(isqrt(period))
    result = []
    for d in set(out):
        factors = 0
        n = d
        for p in range(2, isqrt(n)+1):
            if n % p == 0:
                factors += 1
                while n % p == 0:
                    n //= p
        if n > 1:
            factors += 1
        if factors >= 2:
            result.append(d)
    return tuple(sorted(result))


@lru_cache(maxsize=400_000)
def density_bad(xs):
    if len(xs) < 2:
        return False
    m = 1
    for a, b in combinations(xs, 2):
        m = lcm(m, gcd(a, b))
    return sum(m // gcd(x, m) for x in xs) > m


def all_subsets_good(xs):
    for size in range(3, len(xs)+1):
        for sub in combinations(xs, size):
            if density_bad(sub):
                return False
    return True


def extra_good(xs, k):
    from audit import maximal_power_failure
    if maximal_power_failure(xs) is not None:
        return False
    if sum(x % (k-1) == 0 for x in xs) == 3 and sum(
            x % (k-2) == 0 for x in xs if x % (k-1)) < 2:
        return False
    if k <= 30:
        for p in range(2, k):
            if 2*p >= k and all(p % q for q in range(2, isqrt(p)+1)):
                if sum(x % p == 0 for x in xs) not in (0, 2):
                    return False
    return True


def search(k, seconds=60, strong=False):
    start = monotonic()
    values = divisors_with_two_primes(k)
    anchor = tuple(x for x in values if x % (k-1) == 0)
    other = tuple(x for x in values if x % (k-1))
    adjacent = {(a,b): 1 < gcd(a,b) < k for a in values for b in values}
    count = Counter()
    base, reduced = set(), set()

    class Deadline(Exception):
        pass

    def check_time():
        if monotonic()-start > seconds:
            raise Deadline

    def partial_possible(xs, future):
        if not strong:
            return True
        for p in range(2, k):
            if not all(p % q for q in range(2, isqrt(p)+1)):
                continue
            for x in xs:
                if x % p:
                    continue
                q = p
                while x % (q*p) == 0:
                    q *= p
                if sum(y % q == 0 for y in xs) == 1 and not any(y % q == 0 for y in future):
                    return False
            if 2*p >= k:
                count_p = sum(x % p == 0 for x in xs)
                if count_p > 2 or (count_p == 1 and not any(y % p == 0 for y in future)):
                    return False
        if sum(x % (k-1) == 0 for x in xs) == 3 and not any(y % (k-1) == 0 for y in future):
            have = sum(x % (k-2) == 0 for x in xs if x % (k-1))
            if have < 2 and not any(y % (k-2) == 0 for y in future):
                return False
        return True

    def expand_others(xs, candidates):
        check_time()
        count["other_nodes"] += 1
        if not partial_possible(xs, candidates):
            return
        if len(xs) == k:
            sorted_xs = tuple(sorted(xs))
            if all_subsets_good(sorted_xs):
                base.add(sorted_xs)
                if extra_good(sorted_xs, k):
                    reduced.add(sorted_xs)
            return
        if not candidates:
            return
        if len(xs) + sum(min(k, x) if x < k else 1 for x in candidates) < k:
            return
        for i, x in enumerate(candidates):
            allowed = tuple(y for y in candidates[i+1:] if adjacent[x,y])
            max_count = min(k-len(xs), x if x < k else 1)
            for c in range(1, max_count+1):
                new = tuple(sorted(xs + (x,)*c))
                if density_bad(new):
                    break
                # The density test is performed on all subsets at the leaf.
                # Early triple checks are exact hereditary exclusions.
                if any(density_bad(sub) for sub in combinations(new, 3)):
                    break
                expand_others(new, allowed)

    def expand_anchors(xs, candidates):
        check_time()
        count["anchor_nodes"] += 1
        possible_others = tuple(y for y in other if all(adjacent[x,y] for x in set(xs)))
        if not partial_possible(xs, candidates + possible_others):
            return
        if len(xs) >= 3:
            expand_others(xs, possible_others)
        if len(xs) == k or not candidates:
            return
        if len(xs) + sum(min(k, x) if x < k else 1 for x in candidates) < 3:
            return
        for i, x in enumerate(candidates):
            allowed = tuple(y for y in candidates[i+1:] if adjacent[x,y])
            max_count = min(k-len(xs), x if x < k else 1)
            for c in range(1, max_count+1):
                new = tuple(sorted(xs + (x,)*c))
                if density_bad(new):
                    break
                if any(density_bad(sub) for sub in combinations(new, 3)):
                    break
                expand_anchors(new, allowed)

    complete = True
    try:
        expand_anchors((), anchor)
    except Deadline:
        complete = False
    return {"k":k, "complete":complete, "strong_pruning":strong,
            "seconds":round(monotonic()-start,3),
            "domain_size":len(values), "counts":dict(count),
            "base_survivors":[list(xs) for xs in sorted(base)],
            "reduced_survivors":[list(xs) for xs in sorted(reduced)]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("k", type=int, nargs="+")
    parser.add_argument("--seconds", type=float, default=60)
    parser.add_argument("--strong", action="store_true")
    args = parser.parse_args()
    for k in args.k:
        print(json.dumps(search(k, args.seconds, args.strong), sort_keys=True), flush=True)
