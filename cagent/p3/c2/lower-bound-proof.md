# C2: triangular lower bound

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

For every $t<T$, $D(p_t,q_t)$ still has an occupied cell on diagonal $k+1$, whereas the staircase has none. The staircase is the **only cyclic partition** of $T_k$, by the general triangular uniqueness theorem proved in [TriangularGeneral.lean](../lean/ProofPursuit/P3/TriangularGeneral.lean) and explained in the [C1 proof](../c1/written-proof.md). Thus no earlier state is cyclic, and the first cyclic depth of this witness is exactly $T=k(k-1)$.

The witness and lower-bound result appear in [Griggs and Ho, Theorem 3.1](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf). The modular calculation above supplies an explicit check that the unsorted diagonal rotations remain valid partitions at every earlier step.
