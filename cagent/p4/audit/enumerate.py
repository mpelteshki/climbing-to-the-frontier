#!/usr/bin/env python3
"""Finite necessary-condition search for minimal DCCC counterexamples.

This is a reproducible Python experiment, not a Lean certificate.  See REPORT.md
for the mathematical reduction and the precise meaning of a survivor.
"""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
import json
from math import gcd, isqrt, lcm
from time import monotonic


def primes_below(k):
    return tuple(p for p in range(2, k) if all(p % q for q in range(2, isqrt(p) + 1)))


def prime_powers(k):
    out = []
    for p in primes_below(k):
        q = p
        while q * p < k:
            q *= p
        out.append((p, q))
    return tuple(out)


def domain(k):
    """All divisors of L_k with at least two distinct prime factors."""
    values = [1]
    for p, top in prime_powers(k):
        powers = [1]
        while powers[-1] < top:
            powers.append(powers[-1] * p)
        values = [n * q for n in values for q in powers]
    return tuple(sorted(n for n in values if sum(n % p == 0 for p in primes_below(k)) >= 2))


@lru_cache(maxsize=300_000)
def density_obstruction(xs):
    """Return integer witness (M, total) exactly when Lemma 5 rejects xs."""
    if len(xs) < 2:
        return None
    m = lcm(*(gcd(a, b) for a, b in combinations(xs, 2)))
    total = sum(m // gcd(x, m) for x in xs)
    return (m, total) if total > m else None


def first_bad_subset(xs):
    """Smallest-cardinality density obstruction, if one exists."""
    for size in range(3, len(xs) + 1):
        for sub in combinations(xs, size):
            witness = density_obstruction(sub)
            if witness is not None:
                return {"moduli": list(sub), "M": witness[0], "total": witness[1]}
    return None


def power_support(xs, powers):
    """A highest prime power in any m_i must occur in at least two moduli."""
    for p, _ in powers:
        for x in xs:
            if x % p:
                continue
            q = p
            while x % (q * p) == 0:
                q *= p
            if sum(y % q == 0 for y in xs) < 2:
                return {"prime_power": q, "modulus": x}
    return None


def special_obstruction(xs, k):
    """Other clauses of O'Bryant Lemma 6, applied to complete tuples."""
    anchors = sum(x % (k - 1) == 0 for x in xs)
    if anchors == 3 and sum(x % (k - 2) == 0 for x in xs if x % (k - 1)) < 2:
        return {"rule": "three_anchors_need_two_k_minus_two"}
    support = power_support(xs, prime_powers(k))
    if support is not None:
        return {"rule": "prime_power_support", **support}
    if 7 <= k <= 30:
        for p in primes_below(k):
            if 2 * p >= k:
                count = sum(x % p == 0 for x in xs)
                if count not in (0, 2):
                    return {"rule": "large_prime_exactly_two", "prime": p, "count": count}
    return None


def search(k, seconds=60, strong=False, target_length=None):
    if target_length is None:
        target_length = k
    if strong and target_length != k:
        raise ValueError("minimal-counterexample pruning requires target_length = gcd_cap")
    start = monotonic()
    ds = domain(k)
    anchors = tuple(x for x in ds if x % (k - 1) == 0)
    nonanchors = tuple(x for x in ds if x % (k - 1))
    compatible = {(a, b): 1 < gcd(a, b) < k for a in ds for b in ds}
    counts = Counter()
    base = []
    reduced = []

    class Deadline(Exception):
        pass

    def check_time():
        if monotonic() - start > seconds:
            raise Deadline

    def grow(xs, pool):
        check_time()
        counts[f"node_{len(xs)}"] += 1
        if strong:
            # Both tests are hereditary impossibilities for a *minimal*
            # counterexample. The pool already contains every future value.
            for p, _ in prime_powers(k):
                powers = []
                for x in xs:
                    if x % p == 0:
                        q = p
                        while x % (q * p) == 0:
                            q *= p
                        powers.append(q)
                for q in set(powers):
                    if sum(x % q == 0 for x in xs) == 1 and not any(y % q == 0 for y in pool):
                        counts["support_no_future"] += 1
                        return
                if 7 <= k <= 30 and 2 * p >= k:
                    found = sum(x % p == 0 for x in xs)
                    if found > 2 or (found == 1 and not any(y % p == 0 for y in pool)):
                        counts["large_prime_no_future"] += 1
                        return
            if sum(x % (k-1) == 0 for x in xs) == 3 and not any(y % (k-1) == 0 for y in pool):
                have = sum(x % (k-2) == 0 for x in xs if x % (k-1))
                if have < 2 and not any(y % (k-2) == 0 for y in pool):
                    counts["k_minus_two_no_future"] += 1
                    return
        if len(xs) == target_length:
            bad = first_bad_subset(xs)
            if bad is not None:
                counts["all_subset_reject"] += 1
                return
            ordered = tuple(sorted(xs))
            base.append(ordered)
            extra = special_obstruction(ordered, k) if target_length == k else None
            if extra is None:
                reduced.append(ordered)
            else:
                counts[extra["rule"]] += 1
            return
        for i, x in enumerate(pool):
            if not all(compatible[x, y] for y in xs):
                continue
            new = xs + (x,)
            if density_obstruction(new) is not None:
                counts["prefix_density_reject"] += 1
                continue
            if any(density_obstruction(tuple(sorted((a, b, x)))) is not None
                   for a, b in combinations(xs, 2)):
                counts["triple_density_reject"] += 1
                continue
            following = tuple(y for y in pool[i:] if compatible[x, y])
            grow(new, following)

    complete = True
    try:
        for triple in combinations_with_replacement(anchors, 3):
            check_time()
            counts["anchor_triples"] += 1
            if not all(compatible[a, b] for a, b in combinations(triple, 2)):
                continue
            if density_obstruction(triple) is not None:
                continue
            pool = tuple(x for x in nonanchors if all(compatible[x, a] for a in triple))
            pool += tuple(x for x in anchors if x >= triple[-1] and all(compatible[x, a] for a in triple))
            pool = tuple(sorted(pool))
            grow(triple, pool)
    except Deadline:
        complete = False
    return {"k": k, "target_length": target_length, "complete": complete, "strong_pruning": strong,
            "seconds": round(monotonic()-start, 3),
            "domain_size": len(ds), "anchor_count": len(anchors), "counts": dict(sorted(counts.items())),
            "base_survivors": [list(x) for x in sorted(set(base))],
            "reduced_survivors": [list(x) for x in sorted(set(reduced))]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("k", type=int, nargs="+")
    parser.add_argument("--seconds", type=float, default=60)
    parser.add_argument("--strong", action="store_true")
    parser.add_argument("--target-length", type=int)
    args = parser.parse_args()
    for k in args.k:
        print(json.dumps(search(k, args.seconds, args.strong, args.target_length), sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
