# C2: triangular upper bound

For every $k\ge1$ and every partition $\lambda$ of $T_k=k(k+1)/2$, Bulgarian solitaire reaches the staircase $(k,k-1,\ldots,1)$ in at most $k(k-1)$ moves. Together with the explicit [lower-bound witness](lower-bound-proof.md), this proves $D_B(T_k)=k(k-1)$ as a **written mathematical proof**. The general upper bound in this document has not been formalized in Lean; the Lean package establishes the triangular destination and finite cases.

The argument reconstructs the upper-bound half of [Griggs and Ho, Theorem 3.7](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf). It proves the needed timing facts directly using pile lifetimes. These correspond to their Proposition 3.2(1),(3) and Lemmas 3.3–3.6; their Proposition 3.2(2) is not needed for this route. We do not use Theorem 3.7 as a premise.

## Pile lifetimes and a sequence bound

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

## The retreat lemma

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

for every sandwich pattern (2). More formally, if $p\le x$, then $p\le x(L-1)$ since $L\ge2$. Otherwise induction on $L$ gives $p\le u+x\le y(L'-1)+x\le x(L-2)+x=x(L-1)$ for the smaller width $L'<L$. This abstract induction is also kernel-checked as [`sandwich_start_bound`](../lean/ProofPursuit/P3/C2SandwichBound.lean); the lifetime argument above proves its application hypotheses in writing.

## A special full-width pattern

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

## Finding the final pattern

Every trajectory at triangular size eventually reaches the staircase, by [triangular convergence](../lean/ProofPursuit/P3/TriangularGeneral.lean). Let $t$ be the **first** move at which it does, so $B^t(\lambda)$ is the staircase. If $t=0$, there is nothing to prove. Otherwise $c_{t+1}=k$. The fresh pile made on move $t$ has size $c_t$, so $c_t\le k$. If $c_t=k$, then its predecessor has $k$ piles and must itself be the staircase: after removing one from each, its surviving piles must be exactly $k-1,k-2,\ldots,1$, with one exhausted pile. This contradicts minimality of $t$. Equation (1) now forces $c_t=k-1$, and the rise to $c_{t+1}=k$ entails no death at time $t$.

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

## The deadline

For $k=1$, the only partition is fixed. For $k=2$, the three partitions of $3$ have depths $1,0,2$, respectively: $(3)\to(2,1)$, $(2,1)$ is fixed, and $(1,1,1)\to(3)\to(2,1)$. Now let $k\ge3$. If $t\le k$, then $t\le k(k-1)$.

Suppose $t\ge k+1$. If a type-II pattern has full width $k$, it is (7), and its allowed index range forces $p=t-k+1$, $q=t+1$. By (8), $t=p+k-1\le n=T_k\le k(k-1)$, the last inequality holding for $k\ge3$.

For every other pattern just found, its level $x$ is $k$ or $k-1$, its width $L$ is at most $k-1$, and its start satisfies $p\ge t-k$. Equation (6) gives

$$
t\le p+k\le x(L-1)+k\le k(k-2)+k=k(k-1).
$$

The lower-bound witness attains this deadline, so the maximum first cyclic depth at $T_k$ is exactly $k(k-1)$.
