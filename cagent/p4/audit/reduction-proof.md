# Proof of the finite-search rejection rules

This note proves the mathematical implications used by [`enumerate.py`](enumerate.py), [`clique.py`](clique.py), and the modulus and residue checks in [`audit.py`](audit.py). The source is Kevin O’Bryant, [*On Z.-W. Sun's Disjoint Congruence Classes Conjecture*, arXiv:math/0604347v2](https://arxiv.org/pdf/math/0604347v2), especially Proposition 2 and Lemmas 5–6. The arguments are reconstructed below rather than delegated to that citation. They apply to a **least-size** counterexample, and the sum-minimal normalization applies after choosing, among counterexamples of that size, one minimizing the sum of the moduli. They do not by themselves prove a conjecture at a size whose smaller cases are unsettled. This document establishes pruning soundness; completeness of a particular finite run additionally requires its recorded `complete: true` result and replay of its output.

## Starting hypothesis and finite normalization

Assume $k\ge4$ is the least size of pairwise disjoint integer congruence classes $a_i\pmod{m_i}$, with positive moduli, for which every $\gcd(m_i,m_j)<k$. Choose such a system with minimal $\sum_i m_i$. By the two-class Chinese remainder theorem, classes $a_i\pmod{m_i}$ and $a_j\pmod{m_j}$ meet if and only if $\gcd(m_i,m_j)\mid a_i-a_j$. Thus all pair gcds are in $\{2,\ldots,k-1\}$; a gcd of 1 cannot occur in a disjoint system. This is the paper's [Proposition 2](https://arxiv.org/pdf/math/0604347v2).

Let

\[
  N=\operatorname{lcm}_{i<j}\gcd(m_i,m_j),\qquad
  L_k=\operatorname{lcm}(1,2,\ldots,k-1).
\]

Certainly $N\mid L_k$. If a maximal prime-power factor $p^e$ of some $m_i$ did not divide $N$, every other $m_j$ would have $p$-adic valuation below $e$: otherwise $p^e\mid\gcd(m_i,m_j)\mid N$. Dividing just $m_i$ by $p$ consequently leaves every $\gcd(m_i,m_j)$ unchanged, since its $p$-valuation was already less than $e$. All disjointness inequalities remain true by the Chinese remainder criterion, while the modulus sum decreases. This contradicts its choice. Every maximal prime-power factor of every $m_i$ therefore divides $N$, so $m_i\mid N\mid L_k$. Also $N=\operatorname{lcm}_i m_i$: every pair gcd divides its participating moduli, and every modulus divides $N$. This proves the finite reduction in [Lemma 6(1), pp. 3–4](https://arxiv.org/pdf/math/0604347v2).

Every prime divisor of any $m_i$ is therefore a prime below $k$. A modulus 1 is impossible because all its pair gcds would be 1. No modulus is a prime power. To prove the latter, suppose $m_i=p^e$. Every modulus is divisible by $p$, since it has gcd greater than 1 with $m_i$; also $p<k$. Among the $k$ residues, choose $t=\lceil k/p\rceil$ with one common residue modulo $p$, where $2\le t<k$. Subtract that common residue and divide these selected residues and moduli by $p$. For every selected pair, both its residue difference and pair gcd are divided by $p$, hence the divided classes remain disjoint. Minimality of $k$ forces a pair gcd at least $t$ among them, making the original pair gcd at least $pt\ge k$, a contradiction. This proves [Lemma 6(4), pp. 4–5](https://arxiv.org/pdf/math/0604347v2). Thus a complete finite *candidate* domain for modulus **values** is the set of divisors of $L_k$ having at least two distinct prime factors; later conditions may exclude individual values or combinations. Both `enumerate.domain` (prime-power product expansion) and `clique.divisors_with_two_primes` (divisor generation and trial division) compute that set; repetitions remain possible.

For every prime power $q\mid m_i$, also $q\mid N$. Since $N$ is the lcm of pair gcds, some pair gcd is divisible by $q$, so at least two moduli are divisible by $q$. Whether or not $i$ belongs to that pair, at least one of those two moduli is different from $i$. This proves the *prime-power support* rule, [Lemma 6(3)](https://arxiv.org/pdf/math/0604347v2). The code tests the maximal power of each prime in each modulus; testing these powers suffices because every lower power is then supported as well. `enumerate.power_support`, `audit.maximal_power_failure`, and `clique.extra_good` all implement this implication on complete multisets.

## Anchor counts

Call a modulus an anchor when $k-1\mid m_i$. There must be at least three anchors. If there were at most two, delete one anchor, or any class if there are none. The remaining $k-1$ classes would be disjoint and no pair gcd could equal $k-1$, since that would require two remaining anchors. Every pair gcd would be below $k-1$, contradicting the least-size choice. This is [Lemma 6(5)](https://arxiv.org/pdf/math/0604347v2), and justifies beginning both searches with at least three anchors.

If there are **exactly** three anchors, there must be at least two *other* moduli divisible by $d=k-2$. Here is a direct proof of [Lemma 6(6)](https://arxiv.org/pdf/math/0604347v2). Retain any one anchor and delete the other two. The remaining $k-2$ disjoint classes cannot have all pair gcds below $k-2$; otherwise they form a smaller counterexample. Their gcds are still below $k$, and a gcd of $k-1$ is impossible with only one anchor remaining. Hence some two remaining moduli are divisible by $d$. If no outside modulus is divisible by $d$, this is impossible. If exactly one outside modulus $x$ is divisible by $d$, repeating the deletion with each of the three possible retained anchors shows that all three anchors are divisible by $d$. Two anchors would then have gcd divisible by $\operatorname{lcm}(k-1,k-2)=(k-1)(k-2)\ge k$, impossible. Thus at least two outside moduli are $d$-divisible. `special_obstruction` and `extra_good` check exactly that outside count when the final anchor count is three.

## The large-prime rule, including its exceptional case

For $7\le k\le30$, let $p\ge k/2$ be a prime dividing a modulus. Prime-power support gives at least two $p$-divisible moduli, and pair-gcd bounds imply $p<k$. Suppose there are $\ell\ge3$ of them. For each such modulus $m_i$, let $P_i$ contain its prime divisors other than $p$. Each $P_i$ is nonempty by the prime-power exclusion. They are pairwise disjoint: a prime $q$ in two of them would give a pair gcd divisible by $pq\ge2p\ge k$. All these primes are below $k$ by finite normalization.

Each of the other $k-\ell$ moduli meets every anchor in gcd greater than 1. It is not divisible by $p$, so it shares some prime in each $P_i$. Choosing one shared prime per anchor gives a signature in $P_1\times\cdots\times P_\ell$. Equal signatures for two outside moduli would make their gcd divisible by the product of $\ell$ distinct primes. Because $\ell\ge3$, this product is at least $2\cdot3\cdot5=30\ge k$. The signature map is therefore injective, so

\[
  k-\ell\le\prod_{i=1}^{\ell}|P_i|. \tag{1}
\]

If $r$ is the number of primes below $k$, then $\sum_i|P_i|\le r-1$: $p$ is omitted and the $P_i$ are disjoint. For a fixed positive-integer sum, the product is maximal when sizes differ by at most one; moving one unit from $a$ to $b$ when $a\ge b+2$ raises the product by $a-b-1$. Using all $r-1$ available units gives the upper bounds below. A dash means $\ell>r-1$, already impossible because each support is nonempty.

| $r$ | smallest possible $k$ in $7\le k\le30$ | $\ell=3$ | 4 | 5 | 6 | 7 | 8 | 9 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 7 | — | — | — | — | — | — | — |
| 4 | 8 | 1 | — | — | — | — | — | — |
| 5 | 12 | 2 | 1 | — | — | — | — | — |
| 6 | 14 | 4 | 2 | 1 | — | — | — | — |
| 7 | 18 | 8 | 4 | 2 | 1 | — | — | — |
| 8 | 20 | 12 | 8 | 4 | 2 | 1 | — | — |
| 9 | 24 | 18 | 16 | 8 | 4 | 2 | 1 | — |
| 10 | 30 | 27 | 24 | 16 | 8 | 4 | 2 | 1 |

For rows $r=3,\ldots,9$, each numeric bound is strictly below $k-\ell$, even using the row's smallest possible $k$. For $r=10$, $k=30$; every entry with $\ell\ge4$ is below $30-\ell$. The one equality is $k=30,\ell=3$, where (1) forces all three $P_i$ to have size 3, to partition all nine primes other than $p$, and to realize all 27 signatures on the 27 outside moduli. Of the four primes $17,19,23,29$, precisely one can be $p$, so some $q\ge17$ belongs to one support. Choose a prime $q'$ in another support; $qq'\ge34>30$. Fix the signature coordinates $q,q'$. The third coordinate has three choices, each realized by a distinct outside modulus. Any two of those moduli have gcd at least $qq'>30$, a contradiction. Hence $\ell$ cannot exceed 2, and support forces $\ell=2$. This is [Lemma 6(8), pp. 5–6](https://arxiv.org/pdf/math/0604347v2), with its final exceptional-case inference made explicit.

The paper's final sentence says two of $17,19,23,29$ must lie in separate $P_i$. That statement does not follow literally when the excluded prime $p$ is one of the four: the other three could occupy one size-three support. The $q,q'$ argument above covers this configuration. `enumerate.py` applies the rule only for $7\le k\le30$. `clique.py` currently tests `k <= 30` without the lower bound; its published runs begin at $k=9$, so they are inside the proved range. Its generic strong-mode pruning for $k<7$ is not justified by this argument.

## Density for every position subset

For any subset $S$ of at least two *positions*, define $M_S=\operatorname{lcm}_{i<j\in S}\gcd(m_i,m_j)$. Modulo $M_S$, the class $a_i\pmod{m_i}$ occupies exactly $M_S/\gcd(m_i,M_S)$ residue classes. These occupied sets for distinct $i\in S$ must be disjoint: a common residue modulo $M_S$ would make $a_i-a_j$ divisible by $\gcd(m_i,m_j)$, since that gcd divides $M_S$, and the original two classes would meet. Counting the $M_S$ available residues gives

\[
  \sum_{i\in S}\frac{M_S}{\gcd(m_i,M_S)}\le M_S. \tag{2}
\]

Thus an exact integer total greater than $M_S$ rejects the tuple, as in [Lemma 5 and Lemma 6(7), pp. 2–3](https://arxiv.org/pdf/math/0604347v2). If $M$ is any multiple of $M_S$, then $\gcd(m_i,M_S)\mid\gcd(m_i,M)$, so each reciprocal term for $M$ is no larger than for $M_S$. Testing $M_S$ therefore covers every larger permitted period. For a pair, (2) follows automatically from pair gcd at least 2: its two terms total $2/M_S\le1$. It suffices for the scripts to enumerate subset sizes at least three. Repeated values still represent different positions, so their multiplicities are retained in the sum.

`density_obstruction`, `density_bad`, and `direct_density_witness` compute (2) with integer `lcm`, `gcd`, and division. A bad prefix, triple, or other selected position subset stays in every extension, making each early density rejection hereditary. In `clique.py`, once $c$ copies of a value form a bad prefix or triple, increasing $c$ cannot repair that already-present subset; the loop's `break` is sound. At a leaf, `first_bad_subset` and `all_subsets_good` enumerate every position subset of size at least three. In particular, rejection does not depend on a floating-point threshold or on a density heuristic.

## Search-path and partial-pool coverage

`enumerate.py` constructs every nondecreasing anchor triple with replacement. For any eligible $k$-multiset, its first three anchors give exactly one such triple; the remaining occurrences can then be appended in nondecreasing order from `pool`. The initial pool contains every nonanchor compatible with the triple and every compatible anchor no smaller than its third value, **including equal values**. At each extension, `following = pool[i:]` preserves exactly the allowed nondecreasing suffix, intersected with compatibility with the newly chosen value. Thus rejecting `gcd <= 1` or `gcd >= k` at the triple or extension level removes only impossible pairs, and every eligible multiset has a search path. The `--target-length` option is used for diagnostics; strong minimal-counterexample pruning is explicitly forbidden by the code when `target_length != k`.

`clique.py` independently enumerates distinct compatible modulus values, gives each a positive multiplicity, and sorts the result. A repeated value $x\ge k$ is impossible because its pair gcd would be $x\ge k$. A repeated value $x<k$ has multiplicity at most $x$: for $c$ identical classes, (2) with $M_S=x$ says $c/x\le1$. These are the `max_count` bounds. Candidate distinct values form a clique under pair compatibility. Selecting all anchor values first and then all nonanchor values loses no multiset, since order of modulus positions has no mathematical effect. At the anchor stage, `possible_others` contains every nonanchor compatible with the chosen anchors; at the other stage, each recursive `allowed` suffix contains every later distinct compatible value. The capacity rejection

`len(xs) + sum(min(k,x) if x < k else 1 for x in candidates) < k`

uses an **upper** bound on how many positions the remaining values can supply. If even that bound cannot reach $k$, no completion exists. The analogous anchor-stage inequality with right side 3 only rejects states unable to reach the required three anchors. `expand_others` is called at each anchor state of length at least three, so all possible final anchor counts are covered. Its and `expand_anchors`'s density and triple `break`s have the hereditary justification above.

Both strong modes use an overapproximation of future choices, which makes their three no-future rejections safe:

1. **Prime-power support.** If a maximal power $q$ now appears once and no value in the future pool is divisible by $q$, it can never attain the required second occurrence.
2. **Large-prime count.** For $7\le k\le30$, more than two current multiples of $p\ge k/2$ cannot be removed. Exactly one current multiple with no future $p$-multiple cannot reach the required two. (`clique.py` has the lower-bound caveat noted above.)
3. **Exactly three anchors.** If there are exactly three current anchors, no future anchor, fewer than two current **outside** $k-2$-multiples, and no future $k-2$-multiple, the final tuple violates the proved exact-three rule.

In `enumerate.py`, `pool` is the complete sorted suffix of compatible future values. In `clique.py`, `candidates` is the complete suffix of distinct future values in `expand_others`; at an anchor state, `candidates + possible_others` is a possibly larger-than-real set of future values. Missing support from these pools therefore implies missing support from every actual continuation. The strong partial rules need no estimate of remaining positions; overlooking an impossible branch is harmless, while every branch they reject violates a necessary condition. At complete tuples, `special_obstruction` and `extra_good` apply the same three conditions directly.

## Residue-checking caveat and audit scope

For a fixed modulus tuple, pairwise disjointness depends only on residues modulo $R_i=\operatorname{lcm}_{j\ne i}\gcd(m_i,m_j)$, and $R_i\mid m_i$. Common translation can set the first residue to zero; equal original moduli can be permuted so their residues increase with index. These are sound finite-domain reductions for an exact residue search. A branch is impossible if a proposed residue has pair-gcd divisibility with an assigned one, if an equal-original-modulus order is violated, or if an unassigned variable has no admissible residue. The separately exported trees in [`export_refutations.py`](export_refutations.py) and independently replayed trees in [`verify_refutations.py`](verify_refutations.py) use the equal-original-modulus condition `xs[j] == xs[i]` and check every admissible child and each dead leaf.

An earlier `audit.py` version compared `xs[j]` to the effective bound $R_i$, rather than to `xs[i]`. Our first audit called this unsound because the original moduli could differ. **That diagnosis was too strong and is withdrawn.** The old comparison also describes a valid compressed symmetry: if $m_j=R_i=q$, then $q\mid m_i$ and every $\gcd(m_i,m_\ell)$ divides $q$. For every other position $\ell$, therefore,

$$\gcd(m_i,m_\ell)=\gcd(q,m_\ell)=\gcd(m_j,m_\ell).$$

Moreover $\gcd(m_i,m_j)=q$ and $R_j=q$. The two finite residue variables have identical bounds and identical constraints with all other variables. They may be exchanged even if their original moduli differ. Within each such effective-modulus group, residues are distinct modulo $q$ and can be sorted by index; this satisfies all comparisons imposed by the old code. Thus we found a mismatch between the documented symmetry and its implementation, not a counterexample to search soundness.

The current code uses the simpler equal-original-modulus comparison, matching the proof above and the independent tree verifier. A fresh run from empty output files reproduced all 107 claims, all 20,436 fact keys and statuses, and every explicit SAT witness unchanged. The minimum verifier checked all 19,704 required smaller SAT facts; the tree verifier replayed all 59 refutations and 40,292 nodes. Both versions have sound symmetry reductions; the package relies on the current version and these independent certificates. Modulus enumeration never calls this residue solver.
