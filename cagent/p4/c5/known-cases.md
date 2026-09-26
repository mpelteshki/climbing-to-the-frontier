# Conditional exclusions of least counterexamples at 24 and 30

Kevin O’Bryant's [*On Z.-W. Sun's Disjoint Congruence Classes Conjecture*, arXiv:math/0604347v2](https://arxiv.org/pdf/math/0604347v2), Theorem 3 and Lemma 6, states that a **least-size** counterexample cannot have size 24 or 30. The following reconstructs the needed part of Lemma 6, including its finite prime-count argument. It does **not** prove the conjecture independently at either size: the argument assumes the conjecture at every smaller size. No computer search or Lean proof is claimed here.

Suppose, for contradiction, that \(k\in\{24,30\}\) is the least number of pairwise disjoint integer congruence classes \(a_i\pmod{m_i}\) with positive moduli and

\[
  \gcd(m_i,m_j)<k\qquad(i\ne j).
\]

Among counterexamples of this size, choose one minimizing \(\sum_i m_i\). The Chinese remainder criterion says that two classes are disjoint exactly when their pair gcd does **not** divide their residue difference ([Proposition 2, p. 2](https://arxiv.org/pdf/math/0604347v2)). Consequently every pair gcd is greater than 1: a gcd of 1 would make those two classes meet.

## Normalization and prime support

Put \(N=\operatorname{lcm}_{i<j}\gcd(m_i,m_j)\) and \(L_k=\operatorname{lcm}(1,\ldots,k-1)\). Since every pair gcd is a positive integer below \(k\), \(N\mid L_k\). Moreover, each \(m_i\mid N\). To see the latter without assuming it, take a maximal prime power \(p^e\mid m_i\). If \(p^e\nmid N\), every other \(m_j\) has \(p\)-adic valuation below \(e\). Replacing \(m_i\) by \(m_i/p\) therefore preserves **every** pair gcd involving \(i\), hence preserves all disjointness conditions by the Chinese remainder criterion. It also lowers \(\sum_i m_i\), a contradiction. Applying this to each prime-power factor of \(m_i\) proves \(m_i\mid N\). Thus every prime dividing any modulus is below \(k\). In fact \(N=\operatorname{lcm}_i m_i\), because each pair gcd divides each participating modulus, while every modulus divides \(N\). This is [Lemma 6(1), pp. 3–4](https://arxiv.org/pdf/math/0604347v2).

Any prime power \(q\mid m_i\) divides \(N\), so by the definition of an lcm it divides at least one pair gcd. Hence it divides at least two moduli; in particular, another modulus besides \(m_i\) is divisible by \(q\). This is [Lemma 6(3)](https://arxiv.org/pdf/math/0604347v2). The moduli cannot be prime powers. Indeed, if \(m_i=p^e\), every \(m_j\) is divisible by \(p\), since all \(\gcd(m_i,m_j)>1\). Also \(p<k\). At least \(t=\lceil k/p\rceil\) of the residues have one common value modulo \(p\); select exactly \(t\) such classes. Here \(2\le t<k\). Subtract their common residue and divide the selected residues and moduli by \(p\). The resulting \(t\) classes are pairwise disjoint: for two selected indices, both the residue difference and the pair gcd are divided by \(p\), so nondivisibility is preserved. The conjecture at size \(t<k\), available from the least-size assumption, forces a divided pair gcd at least \(t\). Its original pair gcd is then at least \(pt\ge k\), a contradiction. This reconstructs [Lemma 6(4), pp. 4–5](https://arxiv.org/pdf/math/0604347v2). A modulus 1 is already excluded by the pair-gcd bound, so every modulus divisible by a prime \(p\) has another distinct prime factor.

Now let \(p=k-1\), which is respectively 23 or 29 and is prime. At least three moduli are divisible by \(p\). Otherwise delete one of the at most two \(p\)-divisible classes (or any class if there are none). The remaining \(k-1\) classes are disjoint. Their pair gcds are below \(k\), and none can equal \(k-1=p\), because no two remaining moduli are divisible by \(p\). They would be a smaller counterexample. This is the relevant instance of [Lemma 6(5), p. 5](https://arxiv.org/pdf/math/0604347v2).

## Counting the possible supports

Write \(m_1,\ldots,m_\ell\) for **all** the moduli divisible by \(p\), so \(\ell\ge3\), and let \(P_i\) be the set of prime divisors of \(m_i\) other than \(p\), for \(1\le i\le\ell\). Every \(P_i\) is nonempty by the prime-power exclusion above. These \(P_i\) are pairwise disjoint: if distinct anchors both contained \(q\ne p\), their gcd would be divisible by \(pq\ge2(k-1)>k\). Every prime in every \(P_i\) is below \(k\), by \(m_i\mid N\mid L_k\).

For each outside modulus \(m_j\), \(j>\ell\), and each anchor \(i\le\ell\), the pair gcd is greater than 1 but \(p\nmid m_j\). Thus \(m_i\) and \(m_j\) share some prime in \(P_i\). Choose one such prime \(q_i(j)\), for instance the smallest, and assign \(m_j\) the signature \((q_1(j),\ldots,q_\ell(j))\in P_1\times\cdots\times P_\ell\). If two outside indices had the same signature, their gcd would be divisible by the product of those \(\ell\) **distinct** primes. As \(\ell\ge3\), that product is at least \(2\cdot3\cdot5=30\ge k\). Hence the signature map is injective, and

\[
  k-\ell\ \le\ \prod_{i=1}^{\ell}|P_i|. \tag{1}
\]

These are the support and injection steps in the proof of [Lemma 6(8), pp. 5–6](https://arxiv.org/pdf/math/0604347v2). There are nine primes below 24 and ten below 30. Excluding \(p\), the disjoint nonempty supports have total size at most 8 or 9 respectively. For positive integers \(s_i=|P_i|\) of fixed sum, the product is maximized when the sizes differ by at most one: replacing \((a,b)\) with \((a-1,b+1)\) when \(a\ge b+2\) increases the product by \(a-b-1>0\). Using the entire available prime budget can only increase the maximum. The resulting bounds are:

| \(\ell\) | maximum \(\prod s_i\), \(k=24\) | \(24-\ell\) | maximum \(\prod s_i\), \(k=30\) | \(30-\ell\) |
|---:|---:|---:|---:|---:|
| 3 | 18 | 21 | 27 | 27 |
| 4 | 16 | 20 | 24 | 26 |
| 5 | 8 | 19 | 16 | 25 |
| 6 | 4 | 18 | 8 | 24 |
| 7 | 2 | 17 | 4 | 23 |
| 8 | 1 | 16 | 2 | 22 |
| 9 | impossible | — | 1 | 21 |

For \(k=24\), every row contradicts (1). For \(k=30\), every row except \(\ell=3\) contradicts (1). In that exceptional row, equality throughout is forced: each of the three supports has size 3, together they partition all nine primes \(2,3,5,7,11,13,17,19,23\), and the 27 outside indices realize **every** one of the \(3^3=27\) signatures.

The prime 17 lies in one support; choose any prime \(q\) in a different support. Then \(17q\ge34>30\). Fix 17 and \(q\) in their two signature coordinates. The third coordinate has three choices, all realized by distinct outside moduli. Any two of those moduli both contain 17 and \(q\), so their gcd is at least \(17q>30\), the final contradiction.

The paper's last sentence on this exceptional case says that two of \(17,19,23,29\) must lie in separate \(P_i\). Taken literally for \(p=29\), this does not follow: \(p\) is excluded from every \(P_i\), and \(17,19,23\) could occupy the same three-element support. The preceding 17-and-\(q\) argument covers that arrangement and supplies the needed conclusion. The paper's theorem statement is thus supported here by a corrected final counting step, rather than by that particular sentence.
