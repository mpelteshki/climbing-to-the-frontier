# P3 — Bulgarian solitaire: consolidated proof write-up

This item contains complete written proofs for **C1–C4**, together with independently checkable Lean results and finite cross-checks. **C5 is partial:** its matching general upper bound is not proved. C6 is intentionally excluded. No platform submission or organizer acceptance is claimed.

[Problem and cell statements](https://hackathon.bainsa.ai/p/p3). A move removes one card from every pile, discards empty piles, adds a pile equal to the previous pile count, and sorts. Write $B$ for this map, $T_k=k(k+1)/2$, and $D_B(n)$ for the maximum, over partitions of $n$, of the first time a periodic state is reached. Depth excludes subsequent travel around a cycle.

## Answers and assurance

| Cell | Established answer | Assurance |
| --- | --- | --- |
| C1 | Rank $k$ cyclic states are binary staircase boundaries; cycles are binary necklaces of weight $n-T_{k-1}$. The exact count is proved below. Triangular sizes have one fixed staircase. | General classification, rotation correspondence and triangular convergence in Lean; numerical necklace count in writing. |
| C2 | $D_B(T_k)=k(k-1)$ for every $k\ge1$, with explicit attaining partitions. | General upper/lower written proof; finite cases and abstract descent arithmetic in Lean. |
| C3 | For nontriangular rank $k\ge4$, $D_B(n)\le k^2-2k-1$; equality at $T_k-1$. An explicit finite inverse construction gives every maximizer at that size. | General written proof; Lean finite cases; independent exhaustive cross-check of maximizer sets for $k=4,5,6,7$. |
| C4 | $D_B(T_{k-1}+1)=(k-1)(k-3)$ for every $k\ge5$, with explicit attaining partitions. | General upper/lower written proof; Lean instances $k=5,6,7$; exhaustive cross-check through $k=9$. |
| C5 | Exact values $2,3,5,8,12,18$ at $k=2,3,4,5,6,7$. A family has depth $(k-1)(k-4)$ for every $k\ge5$; it is not optimal at $k=5,6$. The proposed formula for all $k\ge7$ remains unproved. | Exact listed finite maxima in Lean; general lower bound and partial upper bound in writing. |
| C6 | Not attempted in this item. | Open-conjecture work paused. |

The following sections include the complete arguments, not merely citations to their target results. Sources and proof limitations remain attached to each result. The C5 gap is not used in any C1–C4 proof.

## C1: complete mathematical argument

This document gives the general mathematical proof, including the numerical cycle count. The classification, rotation correspondence, and triangular convergence are also formalized in Lean. The final counting argument below is a **written proof**, not yet a Lean theorem. **C1 is Solved under the task criteria**; the numerical counting step remains outside the Lean formalization.

Write $T_k=k(k+1)/2$. For $n>0$, let $k$ be its unique rank, so $T_{k-1}<n\le T_k$, and put $r=n-T_{k-1}$. Thus $1\le r\le k$.

The cyclic partitions are exactly

$$
(k-1+\varepsilon_0,\ k-2+\varepsilon_1,\ldots,\varepsilon_{k-1}),
\qquad \varepsilon_j\in\{0,1\},\qquad \sum_j\varepsilon_j=r,
$$

with a final zero omitted. Their distinct cycles are counted by

$$
\boxed{\displaystyle
C(n)=\frac1k\sum_{d\mid\gcd(k,r)}\varphi(d)
  \binom{k/d}{r/d}.}
$$

Here $\varphi(d)$ is Euler's totient, with $\varphi(1)=1$. The separate empty case is $C(0)=1$, represented by the fixed empty partition. At triangular sizes $n=T_k$, every partition eventually reaches $(k,k-1,\ldots,1)$, which is the only cyclic partition.

### 1. Energy and the shape of a cyclic orbit

Draw a partition as columns of heights $\lambda_0\ge\cdots\ge\lambda_{\ell-1}>0$. A card in column $j\ge0$, row $i\ge1$, lies on diagonal $i+j$. Let $E(\lambda)$ be the sum of these diagonal indices over all cards.

Before sorting, a move produces the column list

$$
(\ell,\lambda_0-1,\ldots,\lambda_{\ell-1}-1).
$$

This has the same energy as the original diagram. Indeed, move each card with $i>1$ to $(i-1,j+1)$, and each top card $(1,j)$ to $(j+1,0)$. These moves preserve $i+j$ and give exactly that new column list.

The zero columns are trailing and can be deleted without changing the energy. Sorting the remaining columns into decreasing order cannot increase energy: swapping adjacent heights $a<b$ decreases the column-index contribution by exactly $b-a>0$, while preserving the within-column contribution. Therefore $E(B\lambda)\le E(\lambda)$.

On a cyclic orbit, energy must stay constant at every move. In particular, the unsorted first two columns cannot satisfy $\ell<\lambda_0-1$. Every nonempty cyclic partition therefore satisfies

$$
\lambda_0\le\ell+1.
$$

The rest of the unsorted list is already decreasing. Thus on a cyclic orbit no sorting is needed at all: each diagonal undergoes exactly the rotation described above. On diagonal $w$, column indices advance by one modulo $w$.

### 2. A higher occupied diagonal forces the lower one to be full

Suppose a cyclic partition has a hole on diagonal $w>0$, at column $j<w$, and a card on diagonal $w+1$, at column $q<w+1$. Choose

$$
t=(w+1)(w-1-j)+wq.
$$

Then $j+t\equiv w-1\pmod w$, whereas $q+t\equiv0\pmod{w+1}$. After $t$ moves, the hole is in row 1, column $w-1$, so the new partition has fewer than $w$ columns. The card is in row $w+1$, column 0, so its largest pile has size at least $w+1$. This contradicts the preceding bound: its largest pile is at most its number of columns plus one, hence at most $w$.

Therefore an occupied cell on diagonal $w+1$ forces **every** cell on diagonal $w$ to be occupied.

Let $K$ be the highest occupied diagonal of a nonempty cyclic partition. Diagonal $K-1$ is full when $K>1$; the partition property also fills every lower diagonal. All diagonals above $K$ are empty. Consequently its column heights are

$$
K-1+\varepsilon_0,\ K-2+\varepsilon_1,\ldots,\varepsilon_{K-1}
$$

for bits $\varepsilon_j$. At least one bit is 1, since diagonal $K$ is occupied. Thus

$$
T_{K-1}<n=T_{K-1}+\sum_j\varepsilon_j\le T_K.
$$

Uniqueness of rank gives $K=k$, and the bit sum is $r$. This proves necessity of the asserted form.

### 3. Every asserted boundary is cyclic

Conversely, take any length $k$ bit word of weight $r$. The asserted pile list is decreasing: adjacent differences are $1+\varepsilon_j-\varepsilon_{j+1}\ge0$. Its only possible zero is the last entry, and its total is $T_{k-1}+r=n$.

Its number of positive piles is $k-1+\varepsilon_{k-1}$. One move therefore changes its boundary word to

$$
(\varepsilon_{k-1},\varepsilon_0,\ldots,\varepsilon_{k-2}).
$$

After $k$ moves it returns. This proves sufficiency. The word-to-partition map at fixed $k$ is injective: pad the partition with a final zero when needed and subtract $(k-1,k-2,\ldots,0)$. Hence two such partitions belong to the same cycle exactly when their words are rotations of one another.

### 4. Counting the cycles

Let $W$ be the set of binary words of length $k$ and weight $r$. Count pairs $(w,t)$, where $w\in W$, $0\le t<k$, and rotation by $t$ fixes $w$.

If a rotation orbit has $h$ distinct words, each word has exactly $k/h$ fixing rotations: the map from the $k$ rotations to that orbit has equal-sized fibres, since any two fibres differ by a rotation. Thus each orbit contributes exactly $h(k/h)=k$ pairs. Writing $F(t)$ for the number of words fixed by rotation $t$, we obtain

$$
kC(n)=\sum_{t=0}^{k-1}F(t).
$$

For a fixed $t$, set $g=\gcd(k,t)$ and $d=k/g$. Translation by $t$ on the $k$ positions has $g$ orbits, each of length $d$. To see the orbit length, $ht\equiv0\pmod k$ is equivalent to $d\mid h$, after dividing by $g$ and using $\gcd(k/g,t/g)=1$.

A fixed binary word must be constant on each position orbit. It therefore exists only when $d\mid r$; then exactly $r/d$ of the $g=k/d$ position orbits must be assigned 1. Consequently

$$
F(t)=\begin{cases}
\binom{k/d}{r/d},&d\mid r,\\
0,&d\nmid r.
\end{cases}
$$

For each $d\mid k$, there are $\varphi(d)$ values $t\in\{0,\ldots,k-1\}$ with $k/\gcd(k,t)=d$. For $d>1$, write $t=(k/d)u$, where $1\le u<d$ and $\gcd(u,d)=1$. For $d=1$, the sole value is $t=0$. Grouping the preceding sum by $d$ proves the displayed formula. Its numerator is divisible by $k$, as the pair count already proves.

### 5. Triangular convergence

For $n=T_k$, we have $r=k$. The only weight-$k$ binary word of length $k$ is the all-1 word, encoding the staircase. Thus the staircase is the only cyclic partition; the move description proves it is fixed.

There are finitely many partitions of $n$, and a move preserves $n$. Every forward trajectory therefore eventually repeats and enters a cycle. That cycle must be the staircase, proving eventual convergence. For $n=0$, the empty partition is fixed, so the same assertion holds with $k=0$.

### Verification boundary and provenance

The general statements in Sections 1–3 and 5 have corresponding Lean proofs in [Energy](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/lean/ProofPursuit/P3/Energy.lean), [DiagonalOrder](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/lean/ProofPursuit/P3/DiagonalOrder.lean), [RankedClassification](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/lean/ProofPursuit/P3/RankedClassification.lean), [Necklace](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/lean/ProofPursuit/P3/Necklace.lean), and [TriangularGeneral](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/lean/ProofPursuit/P3/TriangularGeneral.lean). Section 4 is the remaining **unformalized counting argument**.

The independent [cycle-count checker](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c1/check_cycles.py) enumerates actual solitaire trajectories and compares their cycle counts with the formula and boundary encodings for each checked card count. This finite replay is a cross-check of the definitions and formula, not a substitute for the general written argument. [Recorded evidence](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/evidence/cycle-counts.json).

These are classical results, not novelty claims. See [Griggs and Ho, *The Cycling of Partitions and Compositions under Repeated Shifts*](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf) for context. The proof above makes the energy, alignment, and counting steps explicit; it does not use a cited target theorem as a premise.


## C2: triangular upper bound

For every $k\ge1$ and every partition $\lambda$ of $T_k=k(k+1)/2$, Bulgarian solitaire reaches the staircase $(k,k-1,\ldots,1)$ in at most $k(k-1)$ moves. Together with the explicit [lower-bound witness](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c2/lower-bound-proof.md), this proves $D_B(T_k)=k(k-1)$ as a **written mathematical proof**. The general upper bound in this document has not been formalized in Lean; the Lean package establishes the triangular destination and finite cases.

The argument reconstructs the upper-bound half of [Griggs and Ho, Theorem 3.7](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf). It proves the needed timing facts directly using pile lifetimes. These correspond to their Proposition 3.2(1),(3) and Lemmas 3.3–3.6; their Proposition 3.2(2) is not needed for this route. We do not use Theorem 3.7 as a premise.

### Pile lifetimes and a sequence bound

Write $c_i$ for the number of piles in $B^{i-1}(\lambda)$, with $i\ge1$. An original pile of size $a$ exists at times $1,\ldots,a$. The pile created by move $i$ has size $c_i$ and exists at times

$$
J_i=[i+1,i+c_i].
$$

Its last time is $e_i=i+c_i$. At any time $m$, precisely $c_m$ of these original-pile and created-pile intervals contain $m$. One new interval starts between times $i$ and $i+1$; if $d_i$ intervals end at $i$, then

$$
c_{i+1}=c_i+1-d_i.
$$

(1)

In particular $c_{i+1}\le c_i+1$; a rise by one means **no** pile dies, and a constant pair means **exactly one** pile dies.

We use a *sandwich pattern* of level $x$ and width $L=q-p\ge2$:

$$
(c_p,c_{p+1},\ldots,c_q)=(x-1,x,\ldots,x,x+1).
$$

(2)

The two rises occur at its ends. The following elementary sandwich rule will locate one. If $i<j$, $c_i\le x-1$, and $c_j\ge x+1$, choose $p$ as the last index before $j$ with $c_p\le x-1$, and $q$ as the first subsequent index with $c_q\ge x+1$. Equation (1) forces $c_p=x-1$, $c_{p+1}=\cdots=c_{q-1}=x$, and $c_q=x+1$. Thus (2) occurs within $[i,j]$.

### The retreat lemma

Suppose (2) occurs and $p>x$. Among the $x$ recent created piles $J_{p-x},\ldots,J_{p-1}$, at least one is absent at time $p$, since $c_p=x-1$. The last, $J_{p-1}$, is present. Let $u\in[p-x,p-2]$ be the largest index whose interval is absent. All of $J_{u+1},\ldots,J_{p-1}$ are present at $p$. Since $c_{p+1}=c_p+1$, none dies at $p$, so they remain present at $p+1$.

Put $h=p-u-1$ and $y=h+1=p-u\le x$. The absence of $J_u$ at $p$ gives $c_u\le h$. The presence of $J_{u+1}$ at $p+1$ gives $c_{u+1}\ge h+1$. Applying $c_{u+1}\le c_u+1$ shows

$$
c_u=h=y-1,\qquad c_{u+1}=h+1=y.
$$

(3)

Moreover $J_{u+1}$ ends at time $u+1+y=p+1$.

If $L=2$, the pattern also has $c_{p+2}=c_{p+1}+1$, so no interval ends at $p+1$, a contradiction. Hence every width-two pattern satisfies

$$
p\le x.
$$

(4)

Now let $L\ge3$. As long as no later value $c_{u+s}$ has risen from $y$ to $y+1$, the consecutive intervals

$$
J_{u+s},J_{u+s+1},\ldots,J_{p+s-1}
$$

are all present at time $p+s$, for $1\le s\le L-1$. This holds for $s=1$ by the choice of $u$ and the lack of a death at $p$. If $c_{u+s}=y$, then $J_{u+s}$ ends at $(u+s)+y=p+s$. For $s\le L-2$, the pair $c_{p+s}=c_{p+s+1}=x$ permits exactly one death. It must be this interval; all the others survive, and $J_{p+s}$ is born. This proves the induction. At each stage the active $J_{u+s}$ implies $c_{u+s}\ge y$, while (1) and the preceding value $y$ imply $c_{u+s}\le y+1$. Hence it either stays at $y$ or supplies the desired rise.

At $s=L-1$, the transition from $c_{q-1}=x$ to $c_q=x+1$ permits no death. Thus $J_{u+L-1}$ cannot have size $y$, which would make it end at $q-1$. A first rise occurs at some $v$ with

$$
u+2\le v\le u+L-1,
\qquad(c_u,\ldots,c_v)=(y-1,y,\ldots,y,y+1).
$$

(5)

It occurs by $p+1$: otherwise both $c_p$ and $c_{p+1}$ would equal $y$, contradicting their values $x-1,x$. Thus $u\ge p-x$, $v\le p+1$, $y\le x$, and the new width $v-u<L$. This is the retreat step.

Each retreat decreases the positive integer width. It therefore stops either at a pattern with start at most its level or at width two, where (4) gives the same bound. Working backward through $p\le u+x$, while levels never increase, gives the explicit bound

$$
\boxed{p\le x(L-1)}
$$

(6)

for every sandwich pattern (2). More formally, if $p\le x$, then $p\le x(L-1)$ since $L\ge2$. Otherwise induction on $L$ gives $p\le u+x\le y(L'-1)+x\le x(L-2)+x=x(L-1)$ for the smaller width $L'<L$. This abstract induction is also kernel-checked as [`sandwich_start_bound`](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/lean/ProofPursuit/P3/C2SandwichBound.lean); the lifetime argument above proves its application hypotheses in writing.

### A special full-width pattern

We also need one bound that uses the number $n$ of cards. Suppose

$$
(c_p,\ldots,c_{p+k})=(k-2,k-1,\ldots,k-1,k).
$$

(7)

Here $k\ge3$. The interval $J_p$ ends at $p+k-2$. Since $c_{p+k-2}=c_{p+k-1}=k-1$, it is the **only** interval ending then. No interval ends at $p+k-1$, since the next count rises from $k-1$ to $k$.

At time $p+k$, the $k-1$ intervals $J_{p+1},\ldots,J_{p+k-1}$ are all present. There is exactly one other pile. If it is original, its original size is at least $p+k$, and hence $n\ge p+k$. If it is $J_1$, then $1+c_1\ge p+k$, and $c_1\le n$ gives $n+1\ge p+k$.

The only other possibility would be $J_i$ for some $2\le i\le p-1$; $J_p$ has already died. Such a $J_i$ is also the unique extra pile at time $p+k-1$, alongside $J_{p+1},\ldots,J_{p+k-2}$. Hence $J_{i-1}$ is absent at that time, so $(i-1)+c_{i-1}\le p+k-2$. But $J_i$ survives to $p+k$, and (1) yields

$$
(i-1)+c_{i-1}\ge(i-1)+(c_i-1)\ge p+k-2.
$$

Equality follows, making $J_{i-1}$ a second interval ending at $p+k-2$, contrary to the uniqueness of $J_p$. We have proved

$$
\boxed{p+k\le n+1}.
$$

(8)

### Finding the final pattern

Every trajectory at triangular size eventually reaches the staircase, by [triangular convergence](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/lean/ProofPursuit/P3/TriangularGeneral.lean). Let $t$ be the **first** move at which it does, so $B^t(\lambda)$ is the staircase. If $t=0$, there is nothing to prove. Otherwise $c_{t+1}=k$. The fresh pile made on move $t$ has size $c_t$, so $c_t\le k$. If $c_t=k$, then its predecessor has $k$ piles and must itself be the staircase: after removing one from each, its surviving piles must be exactly $k-1,k-2,\ldots,1$, with one exhausted pile. This contradicts minimality of $t$. Equation (1) now forces $c_t=k-1$, and the rise to $c_{t+1}=k$ entails no death at time $t$.

Assume $t\ge k+1$. Of the $k$ intervals $J_{t-k},\ldots,J_{t-1}$, at least one is absent at time $t$, because only $k-1$ piles exist. The last, $J_{t-1}$, is present. Choose the largest absent index $u\in[t-k,t-2]$. Repeating the argument leading to (3), now with $p=t$ and $x=k$, gives

$$
c_u=t-u-1,\qquad c_{u+1}=t-u.
$$

(9)

If $u\ge t-k+1$, then $c_u\le k-2$. Apply the sandwich rule between $u$ and $t+1$ at level $k-1$. It produces a type-II pattern $k-2,k-1,\ldots,k-1,k$ with endpoints $p\ge t-k+1$, $q\le t+1$, and width $q-p\le k$. When that width is exactly $k$, it is the special pattern (7).

The remaining case is $u=t-k$, giving $c_{t-k}=k-1$ and $c_{t-k+1}=k$. If some $c_j\le k-2$ for $t-k+2\le j\le t-1$, the same sandwich rule again produces a type-II pattern within $[t-k+1,t+1]$. If instead some such $c_j\ge k+1$, the rule at level $k$, between $t-k$ and $j$, produces a pattern

$$
(c_p,\ldots,c_q)=(k-1,k,\ldots,k,k+1),
\quad t-k\le p<q\le t-1,
\quad q-p\le k-1.
$$

(10)

Finally suppose every intermediate $c_j$ is $k-1$ or $k$. By the choice $u=t-k$, all $J_{t-k+1},\ldots,J_{t-1}$ are present at time $t$. They account for all $k-1$ piles, and all survive to $t+1$; the only new pile is $J_t$, of size $k-1$. At time $t+1$, each older $J_j$ has remaining size $j+c_j-t\le (t-1)+k-t=k-1$. No pile can have size $k$, contradicting the staircase. Thus either (10) occurs, or a type-II pattern occurs with width at most $k$.

### The deadline

For $k=1$, the only partition is fixed. For $k=2$, the three partitions of $3$ have depths $1,0,2$, respectively: $(3)\to(2,1)$, $(2,1)$ is fixed, and $(1,1,1)\to(3)\to(2,1)$. Now let $k\ge3$. If $t\le k$, then $t\le k(k-1)$.

Suppose $t\ge k+1$. If a type-II pattern has full width $k$, it is (7), and its allowed index range forces $p=t-k+1$, $q=t+1$. By (8), $t=p+k-1\le n=T_k\le k(k-1)$, the last inequality holding for $k\ge3$.

For every other pattern just found, its level $x$ is $k$ or $k-1$, its width $L$ is at most $k-1$, and its start satisfies $p\ge t-k$. Equation (6) gives

$$
t\le p+k\le x(L-1)+k\le k(k-2)+k=k(k-1).
$$

The lower-bound witness attains this deadline, so the maximum first cyclic depth at $T_k$ is exactly $k(k-1)$.


## C2: triangular lower bound

Let $k\ge2$, $n=T_k=k(k+1)/2$, and $B$ be the Bulgarian-solitaire move. The partition

$$
\lambda^{(0)}=(k-1,k-1,k-2,\ldots,2,1,1)
$$

has first cyclic depth exactly $k(k-1)$. The notation includes three copies of $1$ when $k=2$, so $\lambda^{(0)}=(1,1,1)$ in that case. Consequently the maximum depth satisfies $D_B(T_k)\ge k(k-1)$. For $k=1$, the sole partition $(1)$ is fixed and gives the same lower bound $0$. This proves the lower-bound half only; it does not establish an upper bound for arbitrary starting partitions.

Use zero-based columns $j$ and one-based rows $i$. A cell has diagonal index $i+j$. Let $S_k$ be the staircase diagram: every cell on diagonals $1,\ldots,k$ is occupied, so column $j<k$ has height $k-j$. For $0\le p<k$ and $0\le q\le k$, form $D(p,q)$ by deleting the cell $(p,k-p)$ on diagonal $k$ and adding $(q,k+1-q)$ on diagonal $k+1$. It has $T_k$ cells. The added cell leaves a vertical gap when $q=p$. Otherwise its column heights, including a possible zero at the end, are

$$
h_j=k-j-\mathbf1_{j=p}+\mathbf1_{j=q}\qquad(0\le j\le k).
$$

These heights are weakly decreasing exactly when $q\ne p+1$. Indeed the only way the deletion and addition can reverse an adjacent pair is to decrease column $p$ and increase column $p+1$. Thus $D(p,q)$ is a Ferrers partition whenever $q\notin\{p,p+1\}$. In particular, $D(0,k)=\lambda^{(0)}$.

Before sorting, a Bulgarian move maps a card $(i,j)$ with $i>1$ to $(i-1,j+1)$, and a top card $(1,j)$ to $(j+1,0)$. Hence on diagonal $w$ it rotates column $j$ to $j+1\pmod w$. Every full diagonal of $D(p,q)$ remains full. The hole and added card move respectively to columns $p+1\pmod k$ and $q+1\pmod{k+1}$. If the resulting $D$ is Ferrers, it is already in decreasing pile order, so the sorting part of $B$ changes nothing.

Put $T=k(k-1)$ and, for $0\le t<T$, set

$$
p_t=t\bmod k,\qquad q_t=(k+t)\bmod(k+1).
$$

Write $t=ak+b$, where $0\le a\le k-2$ and $0\le b<k$. Then $p_t=b$ and, because $k\equiv-1\pmod{k+1}$,

$$
q_t=\begin{cases}
b-a-1,&b\ge a+1,\\
k+b-a,&b\le a.
\end{cases}
$$

In the first case $q_t<b$; in the second $q_t-b=k-a\ge2$. Therefore $q_t\ne p_t$ and $q_t\ne p_t+1$ throughout $0\le t<T$. Each $D(p_t,q_t)$ is thus a partition. Starting with $D(p_0,q_0)=\lambda^{(0)}$, the diagonal rotation and the Ferrers criterion give, by induction,

$$
B^t(\lambda^{(0)})=D(p_t,q_t)\qquad(0\le t<T).
$$

At $t=T-1=(k-2)k+(k-1)$, we have $p_t=k-1$ and $q_t=0$, so the partition is $(k+1,k-1,k-2,\ldots,2)$, with the descending tail empty for $k=2$. Its next *unsorted* move is $(k-1,k,k-2,\ldots,1)$: this is $D(0,1)$, since $p_T=0$ and $q_T=1$. Sorting its first two entries yields the staircase $(k,k-1,\ldots,1)$, which is fixed by $B$. This also shows explicitly that the first sorting change occurs on the move numbered $T$.

For every $t<T$, $D(p_t,q_t)$ still has an occupied cell on diagonal $k+1$, whereas the staircase has none. The staircase is the **only cyclic partition** of $T_k$, by the general triangular uniqueness theorem proved in [TriangularGeneral.lean](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/lean/ProofPursuit/P3/TriangularGeneral.lean) and explained in the [C1 proof](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c1/written-proof.md). Thus no earlier state is cyclic, and the first cyclic depth of this witness is exactly $T=k(k-1)$.

The witness and lower-bound result appear in [Griggs and Ho, Theorem 3.1](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf). The modular calculation above supplies an explicit check that the unsorted diagonal rotations remain valid partitions at every earlier step.


## C3: nontriangular upper bound and extremal size

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

### Sequence facts carried over from C2

For a starting partition $\lambda$, let $c_i$ be the number of piles in $B^{i-1}(\lambda)$. The new pile born on move $i$ has size $c_i$ and lives at times $i+1,\ldots,i+c_i$. Denote its lifetime interval by $J_i=[i+1,i+c_i]$. At time $m$, exactly $c_m$ intervals, including those of the original piles, are alive. Hence $c_{i+1}\le c_i+1$; a rise by one means no pile dies on move $i$.

The [C2 upper-bound proof](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c2/upper-bound-proof.md) proves three sequence lemmas without using the C2 conclusion:

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

At time $m+k$, the $k-1$ piles $J_{m+1},\ldots,J_{m+k-1}$ already fill all $c_{m+k}=k-1$ places, so no time $m$ pile has size above $k$. Formula (C) says the conjugate diagram lies between the staircases of sizes $k-1$ and $k$; transposing gives the same containment for the original diagram. Its column heights therefore have the form $k-1+\varepsilon_0,k-2+\varepsilon_1,\ldots,\varepsilon_{k-1}$, with bits $\varepsilon_j$, so it is cyclic by the [C1 classification](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c1/written-proof.md).

### Finding a late sandwich

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

### The upper bound

For $k=4$, the exact [Lean checks for $n=7,8,9$](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c3/README.md) give depths $4,5,7$, all at most $4^2-2\cdot4-1=7$. Let $k\ge5$, and put $B=k^2-2k-1$. If $t\le k$, then $d_B(\lambda)\le t-1\le k-1<B$. Otherwise take the pattern just found.

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

### Equality at $T_k-1$

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

### Which starting partitions attain the maximum?

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

### Exhaustive finite replay

Run `python3 cagent/p3/c3/check.py` from the repository root. It independently computes forward depths and constructs the complete inverse sets for $k=4,5,6,7$, then compares the sets elementwise. [Recorded results](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c3/finite-check.json) have respectively 1, 6, 34, and 175 maximizing partitions. This also supplies the finite $k=4$ classification used above.


## P3 C4: one above a triangular number

For every integer $k\ge5$,

$$
D_B(T_{k-1}+1)=(k-1)(k-3).
$$

This is a written mathematical proof of both bounds. It uses the general cycle classification already proved in [C1](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c1/written-proof.md) and Lean, and the pile-lifetime descent bound proved in [C2](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c2/upper-bound-proof.md). The complete C4 argument is not formalized in Lean.

The pile-count pattern method comes from [Griggs and Ho, Sections 3–4](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf). Their Theorem 4.5 supplies this extremal family and a lower bound; the upper-bound argument below is supplied explicitly, not inferred from their conjecture about arbitrary card counts. No novelty claim is made.

### Lifetimes and the last pattern

Put $n=T_{k-1}+1$ and let $c_i$ be the number of piles in $B^{i-1}(\lambda)$. The pile born on move $i$ exists at integer times $i+1,\ldots,i+c_i$; call its lifetime $J_i$. Thus

$$
c_{i+1}=c_i+1-d_i,
$$

where $d_i$ is the number of piles dying at time $i$. In particular, a rise by one permits no death, and a constant consecutive pair permits exactly one death. A block of $m$ pile counts satisfies

$$
\sum_{j=0}^{m-1}c_{p+j}\le n+T_{m-1}.
$$

(1)

Indeed, the piles existing at time $p$ contribute at most their total $n$ remaining cards to these counts. The successive new piles contribute at most $m-1,m-2,\ldots,1$ further occurrences.

A pattern of level $x$ and width $L\ge2$ is

$$
(c_p,\ldots,c_{p+L})=(x-1,x,\ldots,x,x+1).
$$

[C2's retreat argument](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c2/upper-bound-proof.md) proves

$$
p\le x(L-1).
$$

(2)

It also proves that a level $k-1$ pattern of width $k$ satisfies

$$
p+k\le n+1.
$$

(3)

Both are statements about arbitrary solitaire trajectories, not just triangular card counts. Their lifetime proofs precede the triangular application in C2. Equation (2)'s abstract induction is additionally [checked in Lean](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/lean/ProofPursuit/P3/C2SandwichBound.lean).

Choose the earliest index $t$ such that $B^{t-1}(\lambda)$ is cyclic and $(c_t,c_{t+1})=(k-1,k)$. Such an index exists: C1 identifies the cycle with a rotating length $k$ word containing exactly one $1$. The count is $k$ in one phase and $k-1$ in the others. Write $d$ for the first cyclic depth. Then $d\le t-1$.

If $t\ge k+1$, there is either

* a type-I pattern with level $k$, endpoints $t-k\le p<q\le t-1$, hence width $L\le k-1$; or
* a type-II pattern with level $k-1$, endpoints $t-k+1\le p<q\le t+1$, hence width $L\le k$.

Here is a direct proof of that dichotomy. Among $J_{t-k},\ldots,J_{t-1}$ at least one is absent at $t$, since $c_t=k-1$; the last is present. Let $u$ be the latest absent index. The rise at $t$ allows no death. Hence $J_{u+1}$ survives through $t+1$, whereas $J_u$ ends before $t$. The bound $c_{u+1}\le c_u+1$ forces

$$
c_u=t-u-1,\qquad c_{u+1}=t-u.
$$

If $u>t-k$, then $c_u\le k-2$, and the rise from that value to $c_{t+1}=k$ contains a type-II pattern: take the last value at most $k-2$ and the first subsequent value at least $k$. Otherwise $u=t-k$ and $(c_{t-k},c_{t-k+1})=(k-1,k)$. Any subsequent value at most $k-2$ before $t$ gives type II; any value at least $k+1$ gives type I by the same last-crossing construction.

It remains to rule out all those intermediate values lying in $\{k-1,k\}$. Put $m=t-k$. In the state at time $m$, let $H_a$ be the number of piles of height at least $a$. For $1\le a\le k$, every one of the $a-1$ piles born since time $m$ is still alive at time $m+a-1$, since its birth size is at least $k-1$. Therefore

$$
H_a=c_{m+a-1}-(a-1)\in\{k-a,k-a+1\}.
$$

At time $m+k=t$, the $k-1$ piles $J_{m+1},\ldots,J_{t-1}$ already fill every slot, so no pile from time $m$ has height greater than $k$. These conjugate-height bounds place the earlier state between the two consecutive staircases. Moreover, $\sum_a H_a=n=T_{k-1}+1$, so exactly one height exceeds its lower staircase value by one. Conjugating gives the binary-boundary form of C1, hence the state is cyclic. Since $(c_m,c_{m+1})=(k-1,k)$, this contradicts minimality of $t$ and proves the dichotomy.

### Upper bound

Set $F=(k-1)(k-3)$. If $t\le k$, then $d\le k-1\le F$. Otherwise use the dichotomy above.

For type I, applying (1) to its $L+1$ entries gives

$$
n\ge k(L+1)-T_L.
$$

The right side is nondecreasing for integer $L<k$ (its successive difference is $k-L-1$). If $L\ge k-3$, it is at least $T_{k-1}+k-3>n$, since $k\ge5$. Hence $L\le k-4$, and (2) gives

$$
d\le t-1\le p+k-1\le k(k-5)+k-1=k^2-4k-1<F.
$$

For type II consider its width $L$.

**If $L\le k-3$**, then (2) and $p\ge t-k+1$ give

$$
d\le p+k-2\le(k-1)(k-4)+k-2=F-1.
$$

**Width $L=k-1$ is impossible.** The pile born on move $p$ has size $k-2$, so it dies at $p+k-2=q-1$. The final rise from $c_{q-1}=k-1$ to $c_q=k$ permits no death there.

**Suppose $L=k-2$.** Inspect the state at time $p+1$, immediately after the first rise. It has $k-1$ piles, including the new pile of size $k-2$. At times $p+1,\ldots,p+k-4$, exactly one pile dies each time; none dies at $p+k-3$. No pile born on or after move $p$ can die at those times. Thus the old piles have sizes exactly $1,2,\ldots,k-4$, together with two sizes at least $k-2$. Their total, including the new pile, is at least

$$
T_{k-4}+3(k-2)=T_{k-1}.
$$

There is just one extra card, and the newly born pile has fixed size $k-2$. The two remaining old sizes must therefore be $k-1$ and $k-2$. The state is exactly

$$
(k-1,k-2,k-2,k-4,k-5,\ldots,1),
$$

which is a cyclic binary boundary by C1. Consequently $d\le p$, and (2) gives $d\le(k-1)(k-3)=F$.

**Finally suppose $L=k$.** At time $p+1$ there are again $k-1$ piles, including the new pile of size $k-2$. Exactly one pile dies at each time $p+1,\ldots,p+k-2$, and none at $p+k-1$. The new pile dies at $p+k-2$; no later-born pile dies this early. Thus the old piles have sizes $1,\ldots,k-3$ and one size at least $k$. The total is at least

$$
T_{k-3}+(k-2)+k=T_{k-1}+1=n.
$$

Equality forces the state $(k,k-2,k-3,\ldots,1)$, again cyclic. Therefore (3) gives

$$
d\le p\le n+1-k\le F.
$$

The last inequality follows from $2(F-(n+1-k))=k^2-5k+2\ge2$ for $k\ge5$. This exhausts the possible widths and proves the upper bound.

### Matching explicit family

Take

$$
\lambda_k=(k-2,k-2,k-3,\ldots,2,2,1).
$$

Equivalently, in $k$ columns its entries are $\lambda_1=k-2$, $\lambda_i=k-i$ for $2\le i\le k-2$, and $(\lambda_{k-1},\lambda_k)=(2,1)$. Its sum is $T_{k-1}+1$.

Use zero-based columns and one-based rows; a card at row $i$, column $j$ has diagonal index $i+j$. Relative to the full staircase of height $k-1$, this diagram has one hole on diagonal $k-1$ at column $0$, and two additional cards on diagonal $k$ at columns $k-2,k-1$.

Before sorting, every move rotates diagonal $w$ by one column modulo $w$. Let $0\le s<F$ and write $s=a(k-1)+b$, where $0\le a\le k-4$ and $0\le b\le k-2$. The hole is at $b$; the two added cards are at

$$
(b-a-2)\bmod k,\qquad (b-a-1)\bmod k.
$$

For either expression, if its representative before reduction is nonnegative it is strictly less than $b$. Otherwise reduction adds $k$, giving a column at least $b+2$. Thus neither extra card is above the hole, nor immediately to its right. The diagram has no vertical gap and its heights remain decreasing: away from the hole, adding at most one card per column cannot reverse the staircase's adjacent order; only an extra card immediately right of the hole could do so. Therefore sorting changes nothing for all these times, and induction proves this exact trajectory description.

Every state with $s<F$ still has its hole below the boundary, so C1 shows it is not cyclic. At $s=F$, the unsorted diagram has its hole at column $0$ and its extra cards at columns $1,2$. Its first three heights are $k-2,k-1,k-2$; sorting swaps the first two. The result is

$$
(k-1,k-2,k-2,k-4,\ldots,1),
$$

which is cyclic. Thus the first cyclic depth of $\lambda_k$ is exactly $F$, proving the matching lower bound and the formula.

### Finite cross-check

Run `python3 cagent/p3/c4/check.py` from the repository root. The independent checker exhausts every partition for $k=5,\ldots,9$, confirms maxima $8,15,24,35,48$, and verifies the displayed witnesses. [Recorded output](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c4/finite-check.json) covers 27,491 partitions. This finite replay supports the audit; the argument above proves the unrestricted formula.


## P3 C5: explicit lower-bound family

For every $k\ge5$, the partition

$$
\lambda_k=(k-2,k-2,k-3,\ldots,3,3,2,1)
$$

has first cyclic depth exactly $(k-1)(k-4)$. To remove any ambiguity in the short tail, its $k$ entries are $\lambda_1=k-2$, $\lambda_i=k-i$ for $2\le i\le k-3$, and $(\lambda_{k-2},\lambda_{k-1},\lambda_k)=(3,2,1)$. Their sum is $T_{k-1}+2$.

This proves a **general lower bound**, not yet the matching general upper bound. The family is the $r=2$ specialization of [Griggs and Ho, Theorem 4.5](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf); the detailed modular trajectory below supplies the omitted calculation. For $k=5,6$ this family is not optimal. The [Lean finite cases](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c5/README.md) give the exact depths $2,3,5,8,12$ for $k=2,3,4,5,6$ respectively.

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

The tail is empty when $k=5$. This is a complete staircase of height $k-1$ plus one card in each of columns $2,3$, hence a cyclic partition by [C1](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c1/written-proof.md). Before time $F$, a hole remained below that boundary, so no earlier state was cyclic. The witness therefore has first cyclic depth exactly $F$.

The matching upper-bound claim for all $k\ge7$ remains a separate proof obligation; finite agreement alone does not establish it.


## P3 C5: upper-bound reduction for two above a triangular number

Let $k\ge7$, $n=T_{k-1}+2$, and $F=(k-1)(k-4)$. The proposed equality $D_B(n)=F$ has the [general lower-bound witness](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c5/lower-bound-proof.md). The argument below proves the upper bound for most trajectories and identifies the single family still requiring an all $k$ estimate. **It is not a proof of the general C5 upper bound.** In particular, the Griggs–Ho [Theorem 4.5](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf) gives the lower bound, while the assertion that it is always sharp is their Conjecture 4.7.

### Sequence facts

For a trajectory from a partition of $n$, let $c_i$ be the pile count in $B^{i-1}(\lambda)$, and let $d$ be its first cyclic depth. Use the [C2 lifetime and retreat lemmas](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c2/upper-bound-proof.md) and [C3 final-pattern dichotomy](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c3/written-proof.md). Choose the earliest count rise $c_t=k-1,c_{t+1}=k$ occurring in a cyclic state. Then $d\le t-1$. If $t>k$, one of two patterns occurs:

* Type I: $(c_p,\ldots,c_q)=(k-1,k,\ldots,k,k+1)$, with $t-k\le p<q\le t-1$.
* Type II: $(c_p,\ldots,c_q)=(k-2,k-1,\ldots,k-1,k)$, with $t-k+1\le p<q\le t+1$.

Write $L=q-p\ge2$. Every level $x$ pattern satisfies $p\le x(L-1)$. A block of $m$ consecutive counts satisfies 

$$
\sum_{j=0}^{m-1}c_{p+j}\le n+T_{m-1}.
$$

(1)

The last inequality counts the remaining lives of piles present at time $p$, plus at most $m-1,m-2,\ldots,1$ appearances by subsequent newborn piles. For a type-II pattern of full width $k$, the special lifetime lemma also gives $p+k\le n+1$.

If $t\le k$, then $d\le k-1<F$. The rest assumes $t>k$.

### Type I

Equation (1) gives $n\ge k(L+1)-T_L$. The right side is nondecreasing over the allowed widths $L\le k-1$. At $L=k-3$ it exceeds $n$ by $k-5>0$, so $L\le k-4$. At $L=k-4$ it exceeds $n$ by $k-8$. Consequently, for $k\ge9$, $L\le k-5$, and

$$
d\le t-1\le p+k-1\le k(k-6)+k-1=F-5.
$$

(2)

For $k=7,8$, (2) also applies whenever $L\le k-5$. The only further type-I case is $L=k-4$ at these two values. At time $p+1$, the new pile has size $k-1$. Each constant count on the plateau forces exactly one death, so $k-6$ old piles have sizes $1,\ldots,k-6$. The remaining five old piles survive the final rise and have size at least $k-4$. Their minimum card total, including the new pile, is $(k-1)+T_{k-6}+5(k-4)$, equal to $22$ at $k=7$ and $30$ at $k=8$. The actual totals are $23$ and $30$. Thus the state immediately after the first rise, $B^p(\lambda)$, is respectively

$$
U_7=(6,4,3,3,3,3,1),\qquad U_8=(7,4,4,4,4,4,2,1).
$$

These two finite cases can be closed by reversing the move. For a partition $\mu$ of length $m$, each predecessor is obtained by choosing a distinct part $s\ge m-1$, removing that part, adding one to every other part, and appending $s-m+1$ ones. This is exhaustive because the removed part must be the newly created pile. Starting from $U_7$, the numbers of states in successive inverse layers $j=0,1,\ldots,8$ are

$$
1,1,1,1,2,3,4,4,0.
$$

At layer $7$, the four states are

$$
\begin{gathered}
(5,3,3,3,3,2,2,1,1),\quad(5,4,4,2,2,2,2,1,1),\\
(5,4,4,3,3,1,1,1,1),\quad(5,4,4,3,3,2,2).
\end{gathered}
$$

Each has largest part below its length minus one, so layer $8$ is empty. Thus $p\le7$. Five forward moves take $U_7$ to the cyclic boundary $(6,5,4,4,3,1)$, giving $d\le p+5\le12<F=18$. For $U_8$, its sole predecessor is $(5,5,5,5,5,3,2)$, which has no predecessor because its largest part $5$ is less than $7-1$. Hence $p\le1$; six forward moves take $U_8$ to the cyclic boundary $(7,6,5,4,4,3,1)$, and $d\le7<F=28$. This settles type I for all $k\ge7$.

### Type II: narrow and forbidden widths

If $L\le k-4$, then

$$
d\le t-1\le p+k-2\le(k-1)(k-5)+k-2=F-1.
$$

(3)

Width $k-1$ is impossible. The pile born on move $p$ has size $k-2$, so it dies at $p+k-2=q-1$; the final rise $c_{q-1}=k-1\to c_q=k$ allows no death then.

At full width $L=k$, exactly one old pile survives the initial plateau. The deaths determine the other old sizes as $1,\ldots,k-3$, and the new pile has size $k-2$. The card sum $T_{k-1}+2$ forces the surviving old size to be $k+1$. Thus

$$
B^p(\lambda)=(k+1,k-2,k-3,\ldots,1).
$$

Its next move is a cyclic binary-boundary partition. Hence the special lifetime bound gives

$$
d\le p+1\le n+2-k\le F,
$$

since $2(F-(n+2-k))=k(k-7)\ge0$.

### Type II: width $k-3$

Here $B^p(\lambda)$ has $k-1$ piles. The new pile has size $k-2$. The plateau deaths force $k-5$ old piles of sizes $1,\ldots,k-5$, leaving three old piles of size at least $k-3$. Their total has only three cards above this minimum. The three possible excess multisets are $(3,0,0),(2,1,0),(1,1,1)$. The first two give cyclic binary-boundary states, so $d\le p\le(k-1)(k-4)=F$.

The third gives the state

$$
S_k=((k-2)^4,k-5,k-6,\ldots,1).
$$

(4)

This state cannot belong to the final pattern. To see its delay directly, use zero-based columns and one-based rows. Relative to the full staircase of height $k-1$, $S_k$ has one missing cell on diagonal $k-1$ at column $0$, two added cells on diagonal $k$ at columns $2,3$, and one added cell on diagonal $k+1$ at column $3$. Under the unsorted move, diagonal $w$ advances one column modulo $w$. For $0\le j\le k-2$, place the missing cell at column $j$, the two diagonal $k$ cells at $(j+2)\bmod k,(j+3)\bmod k$, and the diagonal $(k+1)$ cell at $(j+3)\bmod(k+1)$. These diagrams are Ferrers:

* For $0\le j\le k-4$, all displayed columns are unwrapped. The missing cell makes columns $j,j+1$ equal, while the extra cells make columns $j+1,j+2,j+3$ equal; all other adjacent staircase differences remain nonnegative.
* At $j=k-3$, the diagonal $k$ extras wrap to $k-1,0$, and the diagonal $(k+1)$ extra is in column $k$. The right tail has heights $1,1,1,1$, and the increased column $0$ preserves the leftmost inequality.
* At $j=k-2$, the extras occupy columns $0,1$ on diagonal $k$ and column $0$ on diagonal $k+1$; the missing cell deletes the rightmost staircase column. The first two heights become $k+1,k-1$, and the rest decrease.

Thus sorting does nothing during these $k-2$ moves, and every one of $S_k,B(S_k),\ldots,B^{k-2}(S_k)$ still has a cell on diagonal $k+1$. The [C1 classification](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c1/written-proof.md) rules out cyclicity at all these times. But $t\le p+k-1$, so the chosen cyclic state at time $t-1$ would occur at most $k-2$ moves after $B^p(\lambda)=S_k$, a contradiction. Therefore width $k-3$ also obeys $d\le F$.

### Width $k-2$: two possible cyclic entry states

At this width, the same death-and-card calculation leaves exactly two possible states immediately after the first rise:

$$
A_k=(k,k-2,k-2,k-4,k-5,\ldots,1),\qquad
B_k=(k-1,k-1,k-2,k-4,k-5,\ldots,1).
$$

(5)

Both are cyclic by C1. The preceding state has $c_p=k-2$ piles, whereas a rank $k$ cyclic state has $k-1$ or $k$ piles. Thus this is the first cyclic entry and $d=p$. Their only immediate predecessors compatible with the initial rise and no deaths are, respectively,

$$
(k+1,k-1,k-3,k-4,\ldots,2),\qquad
(k,k,k-3,k-4,\ldots,2).
$$

(6)

### The $B_k$ family is bounded

For a partition $\mu$ with $m$ parts, every predecessor under Bulgarian solitaire is obtained by choosing a distinct part $s\ge m-1$, removing it, incrementing every other part, and appending $s-m+1$ ones. This is exhaustive: $s$ is the newborn pile in $\mu$, and the ones are precisely the predecessor piles that die in the move.

The only eligible values in $B_k$ are $k-1$ and $k-2$. Removing $k-1$ gives another cyclic binary-boundary state. Removing $k-2$ gives the unique noncyclic immediate predecessor

$$
P_k=(k,k,k-3,k-4,\ldots,2).
$$

Thus $p=0$ or the reverse path passes through $P_k$ after its first step.

In every state reached by reversing from $P_k$ while retaining both displayed largest piles, they remain equal, say of size $M=k+j$, and every other part is at most $M-3$. This holds initially. If the inverse rule selects a smaller part, both largest parts gain one and every other surviving part gains one; appended ones also satisfy the gap. Since the two large parts contain $2(k+j)$ cards, card conservation gives

$$
j\le\left\lfloor\frac{n-2k}{2}\right\rfloor
 =\left\lfloor\frac{F}{4}\right\rfloor.
$$

If the inverse rule instead selects one of the equal largest parts of size $M$, the next state has exactly $M$ parts, one part of size $M+1$, and all other parts at most $M-2$. Its inverse eligibility threshold is $M-1$, so the $M+1$ part is its only eligible choice. Selecting it gives a state with $M+1$ parts and all parts at most $M-1$, below the new threshold $M$. No further predecessor exists. Therefore at most two reverse moves follow the last twin-retaining state.

Including the initial $B_k\to P_k$ reverse move gives $p\le1+j+2\le3+\lfloor F/4\rfloor\le F$, since $F\ge18$ for $k\ge7$. This proves the $B_k$ first-entry bound without a high-birth-deadline lemma or a finite-rank assumption.

### The $A_k$ family remains unresolved

The retreat bound gives only $p\le(k-1)(k-3)=F+k-1$ for $A_k$. A uniform first-entry estimate $p\le F$ is still needed. Finite enumeration suggests $p\le T_{k-2}$, but does not prove this for all ranks.

One precise sufficient lemma would be the following **unproved high-birth deadline** for this card count:

$$
c_i\ge k+1\quad\Longrightarrow\quad i+c_i\le n+1.
$$

(7)

Indeed, at $A_k$ the pile of size $k$ is old, since the newest pile has size $k-2$. If it is original, its initial size was $k+p\le n$, giving $p\le n-k$. Otherwise, if born on move $i<p$, its birth size satisfies $c_i=k+p-i\ge k+1$; (7) gives $p\le n+1-k$. At $B_k$, two old piles have size $k-1$. An original one likewise gives $p\le n+1-k$. If both were born during play, at most one could have birth size exactly $k$, because that would force the common birth index $i=p-1$. The other has $c_i\ge k+1$ and $i+c_i=p+k-1$; (7) gives $p\le n+2-k\le F$ for $k\ge7$. Thus proving (7) would close this final case. It has been checked on all trajectories for the finite ranks $k=7,8,9$, but that evidence does not establish its general validity.

Thus this note settles type I, every other type-II width, and the $B_k$ family at width $k-2$. Only the $A_k$ entry family remains unresolved, so the general C5 upper bound remains unproved. It also explains why the [C3 bound](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c3/written-proof.md), $k^2-2k-1$, does not imply the sharper target $F=k^2-5k+4$: their difference is $3k-5$.


## Reproduction and trust boundaries

Repository: [climbing-to-the-frontier](https://github.com/mpelteshki/climbing-to-the-frontier). The repository is private; a judge must have repository access to follow evidence links. This Markdown includes the mathematical arguments directly.

From its root, run:

```sh
python3 cagent/p3/verify.py
python3 cagent/p3/c1/check_cycles.py
python3 cagent/p3/c3/check.py
python3 cagent/p3/c4/check.py --max-k 9
```

The Lean project pins **Lean 4.34.1** and uses its standard library. The [verification script](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/verify.py) checks 41 files, exact source hashes, warnings, and printed axiom dependencies. Recorded successful runtime: **28.203 seconds**. There are no `sorry`, custom axioms, `native_decide`, or external solver assumptions. The permitted standard dependencies are `propext`, `Classical.choice`, and `Quot.sound`. See [full verification evidence](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/evidence/verification.json) and [independent kernel checks](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/evidence/kernel-checks.json).

The finite maxima cover **every card count 1–23**, with a proved complete partition enumeration, universal finite upper bound, and explicit attaining witness for each count. They do not prove an unbounded formula. General C1 classification and triangular convergence are formalized; the C2 lifetime arguments, C3/C4 general bounds, and C5 general lower bound are written mathematical proofs rather than full Lean theorems.

The independent Python cross-checks use exact integers and exhaustive enumeration. Their recorded runs are:

- C1: actual cycles, binary rotation orbits, and the necklace formula agree for all $n=1$ through $40$: **215,307 partitions**, **0.463 seconds**. [Code](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c1/check_cycles.py) · [record](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/evidence/cycle-counts.json).
- C3: forward maximizer sets equal the inverse construction for $k=4,5,6,7$, with **1, 6, 34, 175** maximizers; **0.010 seconds**. [Code](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c3/check.py) · [record](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c3/finite-check.json).
- C4: all **27,491** partitions at $n=11,16,22,29,37$ give maxima **8,15,24,35,48**; **0.051 seconds**. [Code](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c4/check.py) · [record](https://github.com/mpelteshki/climbing-to-the-frontier/blob/main/cagent/p3/c4/finite-check.json).

These timings describe recorded local runs, not a hardware-independent guarantee. The Python experiments cross-check complete written arguments; they are not substituted for general proofs. The C5 inverse trees displayed above are small enough to check by hand with the exhaustive predecessor rule. The unproved deadline remains an explicit research question, even where finite experiments support it.
