# P3 C5: explicit lower-bound family

For every $k\ge5$, the partition

$$
\lambda_k=(k-2,k-2,k-3,\ldots,3,3,2,1)
$$

has first cyclic depth exactly $(k-1)(k-4)$. To remove any ambiguity in the short tail, its $k$ entries are $\lambda_1=k-2$, $\lambda_i=k-i$ for $2\le i\le k-3$, and $(\lambda_{k-2},\lambda_{k-1},\lambda_k)=(3,2,1)$. Their sum is $T_{k-1}+2$.

This proves the **general lower bound**; the complete upper-bound proof below establishes equality for every $k\ge7$. The family is the $r=2$ specialization of [Griggs and Ho, Theorem 4.5](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf); the detailed modular trajectory below supplies the omitted calculation. For $k=5,6$ this family is not optimal. The [Lean finite cases](README.md) give the exact depths $2,3,5,8,12$ for $k=2,3,4,5,6$ respectively.

Use columns numbered from zero and rows numbered from one. Relative to the staircase of height $k-1$, the initial diagram has one hole on diagonal $k-1$ at column $0$, and three extra cards on diagonal $k$ at columns $k-3,k-2,k-1$.

Let $F=(k-1)(k-4)$. Before sorting, a Bulgarian move rotates diagonal $w$ one column forward modulo $w$. At a time $0\le t<F$, write $t=a(k-1)+b$ with $0\le a\le k-5$ and $0\le b\le k-2$. The hole rotates to column $b$. The extra cards rotate to

$$
(b-a-3)\bmod k,\quad(b-a-2)\bmod k,\quad(b-a-1)\bmod k.
$$

Each unreduced value is either nonnegative and strictly less than $b$, or negative and becomes at least $b+2$ after adding $k$: the smallest wrapped difference is $k-a-3\ge2$. Thus none of the extras occupies the hole's column or the column immediately to its right. There is no vertical gap, and the column heights remain decreasing. Away from the hole, a staircase with distinct extra columns cannot have an adjacent inversion; at the hole, only an extra immediately to its right could cause one. Sorting therefore does nothing before time $F$, so induction proves this trajectory formula at every such time.

At $t=F$, the unsorted diagram has the hole at column $0$ and extra cards at columns $1,2,3$. The first four heights are $k-2,k-1,k-2,k-3$. Sorting swaps the first two, giving

$$
(k-1,k-2,k-2,k-3,k-5,k-6,\ldots,1).
$$

The tail is empty when $k=5$. This is a complete staircase of height $k-1$ plus one card in each of columns $2,3$, hence a cyclic partition by [C1](../c1/written-proof.md). Before time $F$, a hole remained below that boundary, so no earlier state was cyclic. The witness therefore has first cyclic depth exactly $F$.

The matching upper bound for every $k\ge7$ is proved by the complete uniform argument in the companion upper-bound proof; finite agreement is only a cross-check.
