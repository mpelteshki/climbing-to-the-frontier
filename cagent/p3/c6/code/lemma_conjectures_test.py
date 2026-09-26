#!/usr/bin/env python3
"""Exhaustive tests of the two conjectural inverse-height lemmas (and the
intermediate case) for every non-cyclic partition of every n <= NMAX.

  D''  : mu_1 >= m+3            =>  h(mu) <= n - mu_1 + 1        (tight at (n))
  O    : at least 4 parts = 1   =>  h(mu) <= n - m               (tight at (1^n))
  O3   : mu_1 = m+2, >= 3 ones  =>  h(mu) <= n - mu_1 + 1
  D'   : mu_1 >= m+3            =>  h(mu) <= n - m - 2           (weaker form of D'')

Also records that the thresholds are sharp: the worst violations for mu_1 = m+2
(no ones condition) and for exactly 3 ones.

    python3 lemma_conjectures_test.py [NMAX]
"""
import json
import sys
import time

from bs_core import all_partitions, inverse_tree_height, is_boundary

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 32
t0 = time.perf_counter()
stats = {"nmax": NMAX, "tested": {"D''": 0, "O": 0, "O3": 0}, "tight": {"D''": 0, "O": 0, "O3": 0},
         "sharpness": {}}
worst_m2 = (-99,)
worst_3ones = (-99,)
for n in range(3, NMAX + 1):
    for mu in all_partitions(n):
        if is_boundary(mu, n):
            continue
        m, M, u = len(mu), mu[0], mu.count(1)
        need = (M >= m + 3) or (u >= 4) or (M == m + 2 and u >= 3) or (M == m + 2) or (u == 3)
        if not need:
            continue
        h = inverse_tree_height(mu)
        if M >= m + 3:
            assert h <= n - M + 1, ("D''", mu, h)
            assert h <= n - m - 2, ("D'", mu, h)
            stats["tested"]["D''"] += 1
            stats["tight"]["D''"] += h == n - M + 1
        if u >= 4:
            assert h <= n - m, ("O", mu, h)
            stats["tested"]["O"] += 1
            stats["tight"]["O"] += h == n - m
        if M == m + 2 and u >= 3:
            assert h <= n - M + 1, ("O3", mu, h)
            stats["tested"]["O3"] += 1
            stats["tight"]["O3"] += h == n - M + 1
        if M == m + 2 and h - (n - M + 1) > worst_m2[0]:
            worst_m2 = (h - (n - M + 1), n, mu, h)
        if u == 3 and h - (n - m) > worst_3ones[0]:
            worst_3ones = (h - (n - m), n, mu, h)
stats["sharpness"]["mu1=m+2_without_ones_condition_max_excess_over_n-M+1"] = [worst_m2[0], worst_m2[1], list(worst_m2[2]), worst_m2[3]]
stats["sharpness"]["exactly_3_ones_max_excess_over_n-m"] = [worst_3ones[0], worst_3ones[1], list(worst_3ones[2]), worst_3ones[3]]
stats["seconds"] = round(time.perf_counter() - t0, 2)
stats["status"] = "PASS"
print(json.dumps(stats, indent=1))
with open("../evidence/lemma-conjectures-test.json", "w") as fh:
    json.dump(stats, fh, indent=1)
