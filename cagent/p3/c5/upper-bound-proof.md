# P3 C5: uniform upper bound for two above a triangular number

For every $k\ge7$, put $n=T_{k-1}+2$ and $F=(k-1)(k-4)$. This proof establishes the uniform upper bound $D_B(n)\le F$. Together with the [explicit lower-bound family](lower-bound-proof.md), it proves

$$
D_B(T_{k-1}+2)=(k-1)(k-4)\qquad(k\ge7).
$$

The exceptional values for $k=2,3,4,5,6$ are respectively $2,3,5,8,12$, proved by the exhaustive Lean certificates linked in the [cell summary](README.md). The general proof below is written mathematics, not a full Lean formalization.

[Griggs and Ho, Theorem 4.5](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf) supplies the general lower-bound construction; their Conjecture 4.7 concerns its sharpness more broadly. The argument here proves this particular two-above-triangular case directly. It does not assume their conjecture or claim novelty.

## Sequence facts

For a trajectory from a partition of $n$, let $c_i$ be the pile count in $B^{i-1}(\lambda)$, and let $d$ be its first cyclic depth. Use the [C2 lifetime and retreat lemmas](../c2/upper-bound-proof.md) and [C3 final-pattern dichotomy](../c3/written-proof.md). Choose the earliest count rise $c_t=k-1,c_{t+1}=k$ occurring in a cyclic state. Then $d\le t-1$. If $t>k$, one of two patterns occurs:

* Type I: $(c_p,\ldots,c_q)=(k-1,k,\ldots,k,k+1)$, with $t-k\le p<q\le t-1$.
* Type II: $(c_p,\ldots,c_q)=(k-2,k-1,\ldots,k-1,k)$, with $t-k+1\le p<q\le t+1$.

Write $L=q-p\ge2$. Every level $x$ pattern satisfies $p\le x(L-1)$. A block of $m$ consecutive counts satisfies

$$
\sum_{j=0}^{m-1}c_{p+j}\le n+T_{m-1}.
$$

(1)

The last inequality counts the remaining lives of piles present at time $p$, plus at most $m-1,m-2,\ldots,1$ appearances by subsequent newborn piles. For a type-II pattern of full width $k$, the special lifetime lemma also gives $p+k\le n+1$.

If $t\le k$, then $d\le k-1<F$. The rest assumes $t>k$.

## Type I

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

## Type II: narrow and forbidden widths

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

## Type II: width $k-3$

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

Thus sorting does nothing during these $k-2$ moves, and every one of $S_k,B(S_k),\ldots,B^{k-2}(S_k)$ still has a cell on diagonal $k+1$. The [C1 classification](../c1/written-proof.md) rules out cyclicity at all these times. But $t\le p+k-1$, so the chosen cyclic state at time $t-1$ would occur at most $k-2$ moves after $B^p(\lambda)=S_k$, a contradiction. Therefore width $k-3$ also obeys $d\le F$.

## Width $k-2$: two possible cyclic entry states

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

## The $B_k$ family is bounded

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

## The $A_k$ family is bounded

Use the exhaustive inverse rule: for a partition $\mu$ with $m$ parts, choose a distinct part $s\ge m-1$, remove it, increment every other part, and append $s-m+1$ ones. The resulting partition is a predecessor of $\mu$, and all predecessors arise this way.

Since $A_k$ has $k-1$ parts, only its part values $k$ and $k-2$ are eligible. Removing $k$ gives

$$
(k-1,k-1,k-3,k-4,\ldots,2,1,1),
$$

which is already cyclic: relative to the padded staircase $(k-1,k-2,\ldots,1,0)$, it has exactly the two added boundary bits at columns $1$ and $k-1$. Hence, if $p>0$, its predecessor at time $p-1$ must be

$$
P_k=(k+1,k-1,k-3,k-4,\ldots,2),
$$

obtained by removing $k-2$. This state has two distinguished largest parts $M=k+1$ and $M-2=k-1$, and every tail part is at most $M-4$.

Trace the $p-1$ further inverse moves from $P_k$. Call a move *tail-selecting* if it selects neither distinguished large part. After $j$ successive tail-selecting moves, both large parts remain, of sizes $M=k+1+j$ and $M-2$. Card conservation gives

$$
2k+2j\le n,\qquad
j\le\left\lfloor\frac{n-2k}{2}\right\rfloor
 =\left\lfloor\frac F4\right\rfloor.
$$

If the inverse chain ends without selecting a distinguished part, its length from $A_k$ is at most $1+j\le1+\lfloor F/4\rfloor<F$.

Suppose at least one tail-selecting move occurs. Initially $P_k$ has $k-2$ parts, so the inverse threshold is $k-3$; its unique eligible tail part is the largest tail part $k-3=M-4$. Removing that part leaves every tail part at most $M-5$ before incrementing, so afterward every tail part is at most the new largest part minus $5$. Further tail-selecting moves preserve this gap. Thus, when a distinguished part is eventually selected after $j\ge1$ tail moves, the state has top parts $M,M-2$ and tail parts at most $M-5$.

If the inverse step selects the largest part $M$, the next partition has $M$ parts, one part $M-1$, and all others at most $M-4$. Its threshold is $M-1$, making that top part the unique eligible choice. Selecting it gives a partition of length $M-1$, all of whose parts are at most $M-3$, below the threshold $M-2$. Thus at most two inverse moves follow the $j$ tail moves. If instead the step selects the second-largest part $M-2$, the next partition has $M-2$ parts, one part $M+1$, and all others at most $M-4$. Its threshold is $M-3$, so again only its top part is eligible; selecting it gives a partition of length $M+1$, all of whose parts are at most $M-3$, below the threshold $M$. In either case,

$$
p\le1+j+2\le3+\left\lfloor\frac F4\right\rfloor\le F.
$$

It remains to consider selecting a distinguished part immediately at $P_k$, before any tail move.

**Select the second-largest $k-1$.** The resulting partition is

$$
Q_2=(k+2,k-2,k-3,\ldots,3,1,1).
$$

Its unique largest part exceeds every tail part by at least $4$. Any reverse step selecting a tail part preserves this gap and increments the largest part. If a reverse step selects the largest part $M$, its predecessor has length $M$ and all parts at most $M-3$, so it has no predecessor. Starting from size $k+2$, there can be at most $n-k-2$ tail-selecting inverse moves by card conservation, followed by at most one largest-part selection. Including the first two reverse moves $A_k\to P_k\to Q_2$,

$$
p\le2+(n-k-2)+1=n-k+1\le F.
$$

For the last inequality, $2(F-(n-k+1))=k^2-7k+2\ge0$ when $k\ge7$.

**Select the largest $k+1$.** The resulting partition is

$$
Q_1=(k,k-2,k-3,\ldots,3,1,1,1,1).
$$

It has $k+1$ parts and largest part $k$, so its only predecessor is obtained by selecting $k$. That predecessor has $k$ parts and largest part $k-1$, so its predecessor is again unique, obtained by selecting $k-1$. If $p\le3$, the desired bound is immediate. Otherwise the resulting earlier state exists, and the three consecutive pile counts at indices $p-3,p-2,p-1$ are

$$
(c_{p-3},c_{p-2},c_{p-1})=(k-1,k,k+1).
$$

This is a width-two, level $k$ sandwich. The C2 width-two lifetime lemma gives $p-3\le k$, hence $p\le k+3\le F$ for $k\ge7$.

All reverse branches are covered, proving the claimed first-entry bound for $A_k$.

## Conclusion and why C3 alone is insufficient

Every final-pattern case now gives $d\le F$: type I, all type-II widths other than $k-2$, and both possible first-entry states at width $k-2$. Together with the explicit lower-bound family, this proves the formula for every $k\ge7$.

C3 gives only $D_B(n)\le k^2-2k-1$, exceeding this target $F=k^2-5k+4$ by $3k-5$. Even after the two-extra-card budget eliminates most pattern widths, the ordinary retreat estimate at width $k-2$ is only $p\le(k-1)(k-3)=F+k-1$. It still misses the target by $k-1$.

The additional ingredient is the exact inverse structure of the two possible cyclic entry states. Distinguished large piles persist under inverse steps until selected; their total card mass bounds those steps, and selecting them leaves only a short branch. The one exceptional branch has two forced predecessors, exposing a width-two count pattern to which the C2 lifetime lemma applies. This closes the gap uniformly in $k$, without a separate search for each rank.
