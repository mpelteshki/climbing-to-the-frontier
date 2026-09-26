# C3: nontriangular upper bound and extremal size

Let $T_j=j(j+1)/2$, and write every nontriangular card count as

$$
n=T_{k-1}+r,\qquad 1\le r\le k-1.
$$

For $k\ge4$, the maximum first-cyclic depth satisfies

$$
D_B(n)\le k^2-2k-1.
$$

(A)

At $n=T_k-1$, equality holds. The section below also gives an exact, computable criterion for **every** maximizing starting partition at that size. This is a written proof; the general C3 statements have not been formalized in Lean. The existing Lean files verify the finite rank-4-through-rank-6 values. The published source is [Griggs and Ho, Theorem 4.4](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf); the argument here supplies the pile-lifetime details behind its upper bound and an explicit trajectory-count classification of equality.

## Sequence facts carried over from C2

For a starting partition $\lambda$, let $c_i$ be the number of piles in $B^{i-1}(\lambda)$. The new pile born on move $i$ has size $c_i$ and lives at times $i+1,\ldots,i+c_i$. Denote its lifetime interval by $J_i=[i+1,i+c_i]$. At time $m$, exactly $c_m$ intervals, including those of the original piles, are alive. Hence $c_{i+1}\le c_i+1$; a rise by one means no pile dies on move $i$.

The [C2 upper-bound proof](../c2/upper-bound-proof.md) proves three sequence lemmas without using the C2 conclusion:

1. If $c_i\le x-1$ and $c_j\ge x+1$ for $i<j$, a *sandwich pattern* $(c_p,\ldots,c_q)=(x-1,x,\ldots,x,x+1)$ occurs inside $[i,j]$.
2. Every such pattern of width $L=q-p\ge2$ obeys $p\le x(L-1)$. This follows from the explicit retreat to a shorter earlier pattern, stopping when $p\le x$, as is forced at width two.
3. If $(c_p,\ldots,c_{p+k})=(k-2,k-1,\ldots,k-1,k)$, then $p+k\le n+1$. The proof counts live intervals at time $p+k$ and rules out an extra pile born after move 1.

We also need two elementary links between a pile-count sequence and its state. First, its entire future determines its starting partition. At relative time $m$, subtract from $c_m$ the number of known new intervals $J_i$ covering $m$. The result is the number of original piles of size at least $m$, for every $m$, and these counts determine the partition. Thus, if $c_{t+i}=c_{t+k+i}$ for all $i\ge0$, the states at times $t$ and $t+k$ are equal; the state at time $t$ is cyclic.

Second, let $m\ge1$ satisfy

$$
c_m=k-1,\quad c_{m+1}=k,\quad
c_{m+a}\in\{k-1,k\}\ (2\le a<k),\quad c_{m+k}=k-1.
$$

(B)

The state at time $m$ is already cyclic. Indeed, for $1\le a\le k$, all the $a-1$ piles born on moves $m,\ldots,m+a-2$ remain alive at time $m+a-1$. If $H_a$ counts the piles of the time $m$ state that have size at least $a$, then

$$
H_a=c_{m+a-1}-(a-1)\in\{k-a,k-a+1\}.
$$

(C)

At time $m+k$, the $k-1$ piles $J_{m+1},\ldots,J_{m+k-1}$ already fill all $c_{m+k}=k-1$ places, so no time $m$ pile has size above $k$. Formula (C) says the conjugate diagram lies between the staircases of sizes $k-1$ and $k$; transposing gives the same containment for the original diagram. Its column heights therefore have the form $k-1+\varepsilon_0,k-2+\varepsilon_1,\ldots,\varepsilon_{k-1}$, with bits $\varepsilon_j$, so it is cyclic by the [C1 classification](../c1/written-proof.md).

## Finding a late sandwich

The C1 boundary classification also says every cyclic state at rank $k$ has pile counts in $\{k-1,k\}$ and period dividing $k$. Because $1\le r<k$, its boundary word contains both a zero and a one, so the cyclic count sequence has a rise $k-1$ to $k$. Choose the **smallest** positive index $t$ for which

$$
c_t=k-1,\quad c_{t+1}=k,\quad
c_{t+i}=c_{t+k+i}\quad\text{for all }i\ge0.
$$

(D)

This $t$ exists. Let $d_B(\lambda)$ be the first-cyclic depth. The future-count argument above gives $d_B(\lambda)\le t-1$. If $t\ge k+1$, minimality means the preceding block $(c_{t-k},\ldots,c_{t-1})$ differs from $(c_t,\ldots,c_{t+k-1})$; otherwise the periodicity and the rise in (D) would already begin at $t-k$.

Assume $t\ge k+1$. Since $c_t=k-1$, one of the $k$ recent intervals $J_{t-k},\ldots,J_{t-1}$ is absent at time $t$. Let $u$ be the largest absent index. The rise $c_t\to c_{t+1}$ entails no death, so the same lifetime calculation as in C2 gives

$$
c_u=t-u-1,\qquad c_{u+1}=t-u.
$$

(E)

If $u\ge t-k+1$, then $c_u\le k-2$, and the sandwich rule between $u$ and $t+1$ produces a **type II** pattern

$$
(c_p,\ldots,c_q)=(k-2,k-1,\ldots,k-1,k),\quad
t-k+1\le p<q\le t+1,\quad q-p\le k.
$$

(II)

Otherwise $u=t-k$, so $c_{t-k}=k-1$ and $c_{t-k+1}=k$. If one of $c_{t-k+2},\ldots,c_{t-1}$ is at most $k-2$, the same rule gives (II). If one is at least $k+1$, the rule between $t-k$ and that index produces a **type I** pattern

$$
(c_p,\ldots,c_q)=(k-1,k,\ldots,k,k+1),\quad
t-k\le p<q\le t-1,\quad q-p\le k-1.
$$

(I)

In the remaining case all intermediate counts lie in $\{k-1,k\}$. Since (D) also gives $c_t=k-1$, condition (B) holds at $m=t-k$, so that earlier state is cyclic. Its future counts must then be $k$-periodic, contrary to the minimality of $t$. Thus (I) or (II) always occurs.

## The upper bound

For $k=4$, the exact [Lean checks for $n=7,8,9$](../c3/README.md) give depths $4,5,7$, all at most $4^2-2\cdot4-1=7$. Let $k\ge5$, and put $B=k^2-2k-1$. If $t\le k$, then $d_B(\lambda)\le t-1\le k-1<B$. Otherwise take the pattern just found.

For type II of full width $k$, its index range forces $(p,q)=(t-k+1,t+1)$. The special sequence lemma gives

$$
d_B(\lambda)\le t-1=p+k-2\le n-1<B.
$$

The last inequality follows from $n\le T_k-1$ and $T_k-2<B$ for $k\ge5$.

Width $k-1$ is impossible for either type. For type I, the index range forces $q=t-1$, so $c_{t-1}=k+1$. Move $t-1$ then creates a pile of size $k+1$ in the cyclic state at time $t$, impossible because every rank $k$ cyclic pile has size at most $k$. For type II, the index range and $c_t=k-1$ force $(p,q)=(t-k+2,t+1)$: the only other possible placement would have $q=t$ and $c_t=k$. But $c_p=k-2$ makes $J_p$ end at $p+k-2=t$, whereas $c_t=k-1\to c_{t+1}=k$ permits no pile to end at $t$.

Every remaining pattern has width $L\le k-2$, level $x\in\{k-1,k\}$, and $p\ge t-k$. The C2 retreat bound yields

$$
d_B(\lambda)\le t-1\le p+k-1
\le x(L-1)+k-1
\le k(k-3)+k-1=B.
$$

This proves (A).

## Equality at $T_k-1$

For every $k\ge4$, begin with the staircase $(k,k-1,\ldots,1)$, delete its two cells on diagonal $k$ in columns $0,1$, and add one cell on diagonal $k+1$ in column $k$. The resulting partition of $T_k-1$ is

$$
\lambda^*=(k-1,k-2,k-2,k-3,\ldots,1,1).
$$

(F)

This is the witness of [Griggs and Ho, Theorem 4.4(2)](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf). Put $B=k^2-2k-1$. For $0\le t<B$, define a diagram $D_t$ by deleting the diagonal $k$ cells in columns

$$
p_t=t\bmod k,\qquad p'_t=(p_t+1)\bmod k,
$$

and adding the diagonal $(k+1)$ cell in column $q_t=(k+t)\bmod(k+1)$. Here a cell on diagonal $w$ in column $j$ has row $w-j$. We check that every $D_t$ is a Ferrers partition. If $p_t\le k-2$, the only invalid added-column positions are $q_t\in\{p_t,p_t+1,p_t+2\}$: they create a vertical gap or reverse adjacent heights. If $p_t=k-1$, the holes wrap to columns $k-1,0$, and the invalid positions are $q_t\in\{k-1,k,0,1\}$.

Write $t=ak+b$, $0\le b<k$. For $t<B$, we have $a\le k-3$, excluding $(a,b)=(k-3,k-1)$, and

$$
q_t=\begin{cases}
b-a-1,&b\ge a+1,\\
k+b-a,&b\le a.
\end{cases}
$$

(G)

If $b\le k-2$, the first branch gives $q_t<b$, while the second gives $q_t\ge b+3$, so all three forbidden positions are avoided. If $b=k-1$, then $a\le k-4$ and $q_t=k-a-2\in\{2,\ldots,k-2\}$, avoiding all four wrapped forbidden positions. Thus every $D_t$ before $B$ is Ferrers. Before sorting, a Bulgarian move rotates each diagonal's column coordinates by one, so $B(D_t)=D_{t+1}$ whenever $t+1<B$. Since $D_0=\lambda^*$, induction gives $B^t(\lambda^*)=D_t$ for all $t<B$.

For the Ferrers check above, when the added column differs from both deleted columns, its heights are explicitly $h_j=k-j-\mathbf1_{j=p_t}-\mathbf1_{j=p'_t}+\mathbf1_{j=q_t}$ for $0\le j\le k$. Adding at a deleted column leaves a vertical gap. In all other cases, inspecting adjacent differences $h_j-h_{j+1}$ gives exactly the forbidden positions stated above; no other pair of heights reverses.

At $t=B-1$, the holes are in columns $k-2,k-1$ and the added cell is in column $0$, giving

$$
B^{B-1}(\lambda^*)=(k+1,k-1,k-2,\ldots,3,1).
$$

Its next unsorted move has column heights $(k-1,k,k-2,\ldots,2)$; sorting the first two yields $(k,k-1,k-2,\ldots,2)$, a rank $k$ cyclic boundary partition of $T_k-1$. Every earlier $D_t$ has an occupied cell on diagonal $k+1$, while a rank $k$ cyclic partition has none, by C1. Hence $d_B(\lambda^*)=B$, and the upper bound proves $D_B(T_k-1)=B$.

## Which starting partitions attain the maximum?

There is an exact pile-count signature for all maximizers. For $k\ge5$, set $n=T_k-1$, $B=k^2-2k-1$, and $P=k(k-3)$. A partition $\lambda\vdash n$ has depth $B$ **if and only if**

$$
\boxed{(c_P,c_{P+1},\ldots,c_{P+k-2})
       =(k-1,k,\ldots,k,k+1).}
$$

(H)

The right side has $k-1$ terms: one $k-1$, then $k-3$ copies of $k$, then one $k+1$. For necessity, equality in the upper-bound chain forces type I (type II has $t\le p+k-1$), level $x=k$, width $L=k-2$, and start $p=k(k-3)$, giving (H). For sufficiency, its last term is $c_{B-1}=k+1$. Move $B-1$ creates a pile of size $k+1$ in $B^{B-1}(\lambda)$, so that state is not cyclic. Once a trajectory enters a cycle it never leaves; hence $d_B(\lambda)\ge B$, and (A) gives equality. For $k=4$, direct enumeration of the 30 partitions of $9$ gives depth counts $4,3,6,7,4,3,2,1$ at depths $0,1,\ldots,7$, respectively. The unique depth-seven partition is $(3,2,2,1,1)$, which also satisfies (H) with $P=4$. The exact Lean certificate verifies the maximum depth; the identifying enumeration can be replayed from recurrence (I) and the four cyclic boundary partitions.

The signature in fact fixes a particular late state. Let $q=P+k-2=B-1$. At time $q$, the piles born on moves $P,\ldots,q-1$ are all alive. The pile $J_P$, born with size $k-1$, now has size $2$; those born on moves $P+1,\ldots,q-1$, each with initial size $k$, have sizes $4,5,\ldots,k$. These are $k-2$ piles containing $2+4+5+\cdots+k=T_k-4$ cards. Since $c_q=k+1$ and $n=T_k-1$, the other three piles have three cards in total, so each has size $1$. Therefore every maximizer satisfies

$$
B^{B-2}(\lambda)=Q_k:=(k,k-1,\ldots,4,2,1,1,1).
$$

(J)

Conversely, $Q_k$ has depth exactly two. It has $k+1$ piles, so its first move produces

$$
P_k=(k+1,k-1,k-2,\ldots,3,1),
$$

whose next move is the cyclic boundary $(k,k-1,\ldots,2)$. Both $Q_k$ and $P_k$ are noncyclic: the former has too many piles for a rank $k$ cyclic partition, and the latter has a pile larger than $k$. Thus (J) is another necessary and sufficient condition for depth $B$.

Equation (J) gives a finite **inverse construction of all starting maximizers**, using only a fixed seed and an explicit rule on partitions. For a partition $\mu$ with $m$ parts, choose any distinct part value $s$ of $\mu$ such that $s\ge m-1$. Remove one occurrence of $s$, add $1$ to each remaining part, append $s-m+1$ parts of size $1$, and sort; call the result $R_s(\mu)$. It has exactly $s$ parts and $B(R_s(\mu))=\mu$. Conversely every predecessor of $\mu$ arises this way, because its new pile must have size $s$, one of the parts of $\mu$.

Start with $\mathcal S_0=\{Q_k\}$ and repeat

$$
\mathcal S_{j+1}=\bigcup_{\mu\in\mathcal S_j}
  \{R_s(\mu):s\text{ is a distinct part of }\mu,\ s\ge\ell(\mu)-1\},
  \qquad 0\le j<B-2.
$$

(K)

Then $\mathcal S_{B-2}$ is **exactly** the set of all maximizing partitions of $T_k-1$. Every state in that final set reaches $Q_k$ after $B-2$ moves, so has depth $B$; every maximizer belongs to the set by (J) and the exhaustive predecessor rule. The construction never tests whether a state is cyclic and does not use a depth oracle. It can merge duplicate branches as sets. For $k=4$, it yields the sole partition $(3,2,2,1,1)$; for larger $k$, the witness (F) is one member among many.

Criterion (H) is a compact membership test for the same set. Its counts can be computed directly from the initial parts by the finite recurrence

$$
c_m=|\{j:\lambda_j\ge m\}|
  +|\{1\le i<m:i+c_i\ge m\}|,\qquad m\ge1.
$$

(I)

The inverse construction (K) and count recurrence (I) are exact constructive answers to which partitions attain the maximum. They do not give a closed-form number of maximizers or a single static Ferrers-inequality description; neither is needed to generate or recognize every one.

## Exhaustive finite replay

Run `python3 cagent/p3/c3/check.py` from the repository root. It independently computes forward depths and constructs the complete inverse sets for $k=4,5,6,7$, then compares the sets elementwise. [Recorded results](finite-check.json) have respectively 1, 6, 34, and 175 maximizing partitions. This also supplies the finite $k=4$ classification used above.
