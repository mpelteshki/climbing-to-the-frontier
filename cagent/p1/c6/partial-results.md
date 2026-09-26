# C6 — partial results (the cell is not solved)

The exact [C6 statement](https://hackathon.bainsa.ai/p/p1/c6), also transcribed in [statements.md](../statements.md): for $N=qd+s$ with $0\le s<d$, put

$$
M(N,d)=s\binom{q+1}{2}+(d-s)\binom{q}{2}.
$$

Prove or disprove that $N$ lines through the origin of $\mathbb R^d$, repetitions allowed, satisfy

$$
S=\sum_{i<j}\theta(x_i,x_j)\le\left(\binom N2-M(N,d)\right)\frac{\pi}{2},\qquad \theta(x,y)=\arccos|\langle x,y\rangle|.
$$

The cell is an open question; infinite families beyond the earlier cells count as partial progress. **Nothing below proves the cell.** What is proved here, with complete written arguments, is:

1. an averaging lemma showing that the C6 bound at $N$ follows from the bound at $N-1$ whenever $d$ divides $N$ (Theorem 2.3); with C5 this proves the $(N,d)=(6,3)$ case (Corollary 2.4), which is the classical Fejes Tóth value $S(6,3)$;
2. an explicit, non-sharp upper bound on $S$ for every $N\ge d+2$ and $d\ge2$ (Theorem 2.5), derived from C5;
3. structural lemmas for the deficiency sum, and a rigorous reduction of the next family $N=d+3$ to connected, sparse, "light" configurations (Theorem 4.1 and Lemma 4.2), together with explicit examples showing why the C5 projection step does not extend verbatim.

Section 5 records numerical evidence for $21$ small parameter pairs. Section 6 states the exact status and what remains.

## 0. Conventions

For unit representatives, the deficiency of a pair is $\delta(x,y)=\arcsin|\langle x,y\rangle|=\pi/2-\theta(x,y)\in[0,\pi/2]$. For a finite family $X$ of unit vectors write $D(X)=\sum_{i<j}\delta(x_i,x_j)$; then $S=\binom N2\frac{\pi}{2}-D(X)$, and the C6 bound for the pair $(N,d)$, written $\mathrm{C6}(N,d)$, is

$$
D(X)\ge M(N,d)\frac{\pi}{2}\quad\text{for every }N\text{ unit vectors in }\mathbb R^d.
$$

Let $D_{\min}(N,d)$ be the minimum of $D$ over all $N$ unit vectors in $\mathbb R^d$; it exists by compactness. The repeated-axis configuration with $s$ axes of multiplicity $q+1$ and $d-s$ axes of multiplicity $q$ has exactly $M(N,d)$ coincident pairs and no other nonorthogonal pairs, so $D_{\min}(N,d)\le M(N,d)\pi/2$ always, and $\mathrm{C6}(N,d)$ is equivalent to $D_{\min}(N,d)=M(N,d)\pi/2$.

Known cases used below: $\mathrm{C6}(N,d)$ for $N\le d$ (then $M=0$); for $d=1$ (all lines coincide); for $d=2$ and all $N$ ([C1](../written-proofs.md#c1-all-n-planar-lines)); for $N=d+1$ ([C3 auxiliary bound](../c4/proof.md#1-a-maximizing-configuration-can-be-made-sparse), written (A) below); and for $N=d+2$ ([C5](../c5/proof.md)). Bound (A) says: any $m\ge2$ unit vectors whose span has dimension at most $m-1$ have $D\ge\pi/2$.

The nonorthogonality graph $G$ of $X$ has the lines as vertices and an edge between two lines exactly when their inner product is nonzero. Its Gram matrix $\Gamma_{ij}=\langle x_i,x_j\rangle$ is positive semidefinite with unit diagonal, and $\operatorname{rank}\Gamma=\dim\operatorname{span}X$.

## 1. Combinatorics of $M(N,d)$

**Lemma 1.1.** Let $d\ge1$ and $N\ge0$.

- (a) $M(N,d)=\min\sum_{i=1}^d\binom{n_i}{2}$ over nonnegative integers $n_1+\cdots+n_d=N$.
- (b) For $N\ge1$, $M(N,d)-M(N-1,d)=\lceil N/d\rceil-1$.
- (c) For $N\ge3$, $N\,M(N-1,d)\le(N-2)\,M(N,d)$, with equality if and only if $d\mid N$ or $N\le d$. Equivalently $M(N-1,d)/\binom{N-1}{2}\le M(N,d)/\binom N2$.
- (d) $M(a,r)+M(b,s)\ge M(a+b,r+s)$.
- (e) $M(N,d)\ge M(N,d+1)$ and, for $N,d\ge2$, $M(N-1,d-1)\ge M(N,d)$.
- (f) For $N\ge d$, $M(N,d)\ge N-d$, with equality if and only if $N\le 2d$.

*Proof.* (a) If some $n_i\ge n_j+2$, moving one item from box $i$ to box $j$ changes the sum by $n_j-(n_i-1)\le-1$. So a minimizer is balanced: all $n_i\in\{q,q+1\}$ with $s$ boxes of size $q+1$; its value is $M(N,d)$.

(b) Write $N=qd+s$. If $s\ge1$, a balanced placement of $N-1$ has $s-1$ boxes of size $q+1$; adding the $N$th item to a box of size $q$ gives a balanced placement of $N$ and adds $\binom{q+1}2-\binom q2=q=\lceil N/d\rceil-1$. If $s=0$ and $q\ge1$, a balanced placement of $N-1$ has one box of size $q-1$; filling it adds $q-1=\lceil N/d\rceil-1$.

(c) Let $\Delta=M(N,d)-M(N-1,d)$. Then $N\,M(N-1,d)-(N-2)\,M(N,d)=2M(N,d)-N\Delta$. With $2M(N,d)=dq(q-1)+2sq$: if $s\ge1$ then $\Delta=q$ and $2M-Nq=q(s-d)$, which is $<0$ for $q\ge1$ and $=0$ for $q=0$ (that is, $N<d$); if $s=0$ then $\Delta=q-1$ and $2M-N(q-1)=dq(q-1)-dq(q-1)=0$. Dividing by $N(N-1)(N-2)>0$ gives the ratio form.

(d) A balanced placement of $a$ items into $r$ boxes next to a balanced placement of $b$ items into $s$ other boxes is a placement of $a+b$ items into $r+s$ boxes; apply (a).

(e) Add an empty box, or a box containing the $N$th item alone, and apply (a).

(f) For $n\ge1$, $\binom n2\ge n-1$ with equality iff $n\le2$. In a balanced placement with $N\ge d$ every box is nonempty, so $\sum\binom{n_i}2\ge\sum(n_i-1)=N-d$, with equality iff all $n_i\le2$, i.e. $N\le2d$. $\square$

## 2. Subset averaging

**Lemma 2.1 (averaging).** For $2\le m\le N$ and any $N$ unit vectors $X$ in $\mathbb R^d$,

$$
D(X)\ \ge\ \frac{N(N-1)}{m(m-1)}\ \min_{T\subset X,\ |T|=m}D(T)\ \ge\ \frac{\binom N2}{\binom m2}\,D_{\min}(m,d).
$$

*Proof.* Each unordered pair $\{i,j\}$ lies in exactly $\binom{N-2}{m-2}$ of the $\binom Nm$ subsets $T$ of size $m$, so $\sum_{|T|=m}D(T)=\binom{N-2}{m-2}D(X)$. Bounding every $D(T)$ below by the minimum and using $\binom Nm/\binom{N-2}{m-2}=N(N-1)/(m(m-1))$ gives the claim. $\square$

**Corollary 2.2.** $D_{\min}(N,d)/\binom N2$ is nondecreasing in $N$. In words: the average deficiency per pair of an optimal configuration never decreases when lines are added.

**Theorem 2.3 (multiples of $d$).** Let $d\ge1$, $q\ge1$, $N=qd$. If $\mathrm{C6}(N-1,d)$ holds, then $\mathrm{C6}(N,d)$ holds.

*Proof.* For $N\le2$ the statement is trivial. For $N\ge3$, Lemma 2.1 with $m=N-1$ and the hypothesis give $D(X)\ge\frac{N}{N-2}M(N-1,d)\frac\pi2$, and $\frac{N}{N-2}M(N-1,d)=M(N,d)$ by the equality case $s=0$ of Lemma 1.1(c). $\square$

**Corollary 2.4 ($(N,d)=(6,3)$).** Six lines in $\mathbb R^3$ satisfy $D\ge3\pi/2$, i.e. $S\le 6\pi=\left(\binom62-3\right)\frac\pi2$, which is the C6 value since $M(6,3)=3$.

*Proof.* C5 gives $\mathrm{C6}(5,3)$: $D\ge M(5,3)\pi/2=\pi$. Apply Theorem 2.3 with $d=3$, $q=2$: $D\ge\frac64\cdot\pi=\frac{3\pi}2$. $\square$

This is the value $S(6,3)$ that Fejes Tóth is reported to have obtained from $S(5,3)$ by a recursive bound (see §6); the argument above derives it from the C4/C5 proofs in this repository without consulting the 1959 text. The averaging identity is classical and no novelty is claimed for it. Theorem 2.3 gives nothing else new at present: for $d\ge4$ and $q\ge2$ it needs $\mathrm{C6}(qd-1,d)$, which is unknown.

**Theorem 2.5 (explicit bound for all $N\ge d+2$).** For $d\ge2$ and $N\ge d+2$, every configuration of $N$ lines in $\mathbb R^d$ satisfies

$$
D\ \ge\ \frac{2\binom N2}{\binom{d+2}2}\cdot\frac\pi2,\qquad\text{equivalently}\qquad S\ \le\ \frac\pi2\binom N2\left(1-\frac{4}{(d+1)(d+2)}\right).
$$

The bound coincides with the conjectured C6 value exactly when $N=d+2$ or $(N,d)=(6,3)$; otherwise it is strictly weaker than the conjecture.

*Proof.* Lemma 2.1 with $m=d+2$ and C5, i.e. $D_{\min}(d+2,d)=M(d+2,d)\pi/2=\pi$ for $d\ge2$. Equality with the conjectured value means $M(N,d)/\binom N2=M(d+2,d)/\binom{d+2}2$; by Lemma 1.1(c) the per-pair value strictly increases at every step $N'\to N'+1$ with $d\nmid N'+1$, so equality forces $d\mid d+3$, i.e. $d=3$ and $N\le6$, and then $3\nmid7$ stops the chain at $N=6$. $\square$

For $N=d+3$ Theorem 2.5 gives $D\ge\frac{2(d+3)}{d+1}\cdot\frac\pi2$, against the conjectured $3\cdot\frac\pi2$; the deficit is $\frac{d-3}{d+1}\cdot\frac\pi2$. As $N\to\infty$ the bound is much weaker than the continuous-energy bound of Bilyk–Matzke (§6), whose correction term is of order $1/d$ rather than $1/d^2$; for $N$ close to $d$, however, the asymptotic bound is worse than the trivial bound and Theorem 2.5 is the best explicit bound we know of.

## 3. Structural lemmas for the deficiency sum

**Lemma 3.1 (row bound).** Let $x$ be a unit vector and $y_1,\dots,y_k$ orthonormal, with $P$ the orthogonal projection onto their span. Then

$$
\sum_{i=1}^k\arcsin|\langle x,y_i\rangle|\ \ge\ \arcsin\|Px\|.
$$

In particular $\sum_i\delta(x,y_i)\ge\pi/2$ if $x\in\operatorname{span}(y_1,\dots,y_k)$.

*Proof.* For $a,b\ge0$ with $a^2+b^2\le1$ we claim $\arcsin a+\arcsin b\ge\arcsin\sqrt{a^2+b^2}$. If the left side is at least $\pi/2$ there is nothing to prove. Otherwise both sides lie in $[0,\pi/2]$, where sine is increasing, and $\sin(\arcsin a+\arcsin b)=a\sqrt{1-b^2}+b\sqrt{1-a^2}$. Squaring, the claim is equivalent to $2ab\sqrt{(1-a^2)(1-b^2)}\ge2a^2b^2$, which for $ab>0$ reduces to $(1-a^2)(1-b^2)\ge a^2b^2$, i.e. $a^2+b^2\le1$; for $ab=0$ it is an equality. Now induct on $k$ with $t_i=|\langle x,y_i\rangle|$: $\sum_{i\le k}\arcsin t_i\ge\arcsin\sqrt{\sum_{i<k}t_i^2}+\arcsin t_k\ge\arcsin\sqrt{\sum_{i\le k}t_i^2}$, where $\sum_it_i^2=\|Px\|^2\le1$ by Bessel's inequality. $\square$

**Lemma 3.2 (deleting one line).** For any line $v\in X$, $D(X)=D(X\setminus v)+\sum_{u\ne v}\delta(v,u)$. Consequently:

- (a) *Essential line.* If $v\notin\operatorname{span}(X\setminus v)$, then $X\setminus v$ lies in a $(d-1)$-dimensional space and $D(X)\ge D_{\min}(N-1,d-1)$. If $\mathrm{C6}(N-1,d-1)$ holds, then $D(X)\ge M(N-1,d-1)\frac\pi2\ge M(N,d)\frac\pi2$ by Lemma 1.1(e).
- (b) *Coincident lines.* If $v=\pm v'$ for some other $v'\in X$, then $D(X)\ge\frac\pi2+D_{\min}(N-1,d)$. If $\mathrm{C6}(N-1,d)$ holds and $N\le2d$, this gives $D(X)\ge M(N,d)\frac\pi2$ by Lemma 1.1(b).
- (c) *Heavy line.* If $\sum_{u\ne v}\delta(v,u)\ge(\lceil N/d\rceil-1)\frac\pi2$ and $\mathrm{C6}(N-1,d)$ holds, then $D(X)\ge M(N,d)\frac\pi2$ by Lemma 1.1(b).

*Proof.* The identity is the definition of $D$. In (a) the vectors of $X\setminus v$ span a proper subspace, of dimension at most $d-1$, and $\sum_{u\ne v}\delta(v,u)\ge0$; embed the span in $\mathbb R^{d-1}$. In (b), $\delta(v,v')=\pi/2$. In (c) combine the identity with the hypotheses. $\square$

**Lemma 3.3 (orthogonal components).** Suppose $X=X_1\sqcup\cdots\sqcup X_m$ with vectors in different parts pairwise orthogonal, $|X_c|=n_c$ and $r_c=\dim\operatorname{span}X_c$. If $\mathrm{C6}(n_c,r_c)$ holds for every part, then $D(X)\ge M(N,d)\frac\pi2$.

*Proof.* $D(X)=\sum_cD(X_c)\ge\sum_cM(n_c,r_c)\frac\pi2\ge M(N,\sum_cr_c)\frac\pi2\ge M(N,d)\frac\pi2$, using Lemma 1.1(d), then $\sum_cr_c=\dim\operatorname{span}X\le d$ and Lemma 1.1(e). $\square$

**Lemma 3.4 (kernel support and forcing).** Let $\Gamma$ be the Gram matrix of $X$, $G$ its nonorthogonality graph, and $c\in\ker\Gamma$.

- (i) Let $B$ be a set of vertices with $c_v=0$ for all $v\in B$, let $W$ be a connected component of $G-B$, and let $b\in B$ have exactly one neighbour $w$ inside $W$. Then $c_w=0$.
- (ii) If $G$ is connected, then $\dim\ker\Gamma\le1$ when $G$ is a tree and $\dim\ker\Gamma\le2$ when $G$ has at most $|V(G)|$ edges. Hence $\dim\ker\Gamma\ge3$ forces $|E(G)|\ge|V(G)|+1$.
- (iii) If $c\ne0$ and $|c_v|=\max_u|c_u|$, then $\sum_{u\sim v}|\langle x_v,x_u\rangle|\ge1$. In particular such a $v$ is not a leaf of $G$ unless its neighbour coincides with it.

*Proof.* (i) Since $c^{\mathsf T}\Gamma c=\|\sum_ic_ix_i\|^2$, $c\in\ker\Gamma$ means $\sum_ic_ix_i=0$. Put $y=\sum_{i\in W}c_ix_i$. Because $c$ vanishes on $B$, also $y=-\sum_{i\notin W\cup B}c_ix_i$. Vertices in different components of $G-B$ are nonadjacent, hence orthogonal, so $\langle y,y\rangle=0$ and $y=0$. Taking the inner product with $x_b$, only $w$ among the vertices of $W$ is adjacent to $b$, so $0=\langle y,x_b\rangle=c_w\langle x_w,x_b\rangle$ with $\langle x_w,x_b\rangle\ne0$; thus $c_w=0$.

(ii) Call $B$ a forcing set if repeated application of (i), starting from $c_B=0$, forces $c=0$. Then the restriction $\ker\Gamma\to\mathbb R^B$ is injective and $\dim\ker\Gamma\le|B|$. In a tree, any single vertex $v$ is a forcing set: each component of $G-v$ contains exactly one neighbour of $v$, so all neighbours are forced; then each further vertex is forced from its parent in the same way. If $G$ is connected with $|E|\le|V|$ and not a tree, it has exactly one cycle. Take $B=\{a,b\}$ adjacent on the cycle. Every component of $G-B$ contains at most one neighbour of $a$ and at most one neighbour of $b$: the pendant trees at $a$ or $b$ are separate components, and the component containing the rest of the cycle contains exactly one further neighbour of each of $a$ and $b$. So both next cycle vertices are forced, and inductively the whole cycle, then the pendant trees. Thus $\dim\ker\Gamma\le2$.

(iii) Row $v$ of $\Gamma c=0$ reads $c_v=-\sum_{u\sim v}\langle x_v,x_u\rangle c_u$, so $|c_v|\le|c_v|\sum_{u\sim v}|\langle x_v,x_u\rangle|$. For a leaf this gives $|\langle x_v,x_u\rangle|\ge1$, hence $=1$. $\square$

## 4. The family $N=d+3$: reduction to the connected sparse case

For $d\ge3$, $M(d+3,d)=3$, so $\mathrm{C6}(d+3,d)$ reads $D\ge3\pi/2$. Define, for every $d\ge1$,

> $F(d)$: every $d+3$ unit vectors in $\mathbb R^d$ satisfy $D\ge3\pi/2$.

$F(1)$ holds (four coincident lines have $D=3\pi$), $F(2)$ holds by C1 ($D\ge M(5,2)\pi/2=2\pi$), and $F(3)$ is Corollary 2.4. For $d\ge3$, $F(d)$ is exactly $\mathrm{C6}(d+3,d)$.

**Theorem 4.1 (reduction).** Let $d\ge4$ and assume $F(d')$ for all $d'<d$. Let $X$ be $d+3$ unit vectors in $\mathbb R^d$ with $D(X)=D_{\min}(d+3,d)$, chosen among all such minimizers with the largest number of orthogonal pairs. If $D(X)<3\pi/2$, then all of the following hold.

1. *(Sparse structure.)* $X$ spans $\mathbb R^d$; every line has at least $d-1$ linearly independent orthogonal lines; hence $G$ has maximum degree at most $3$, and for every vertex $v$ the lines orthogonal to $v$ span exactly $v^\perp$.
2. *(Distinct lines.)* No two of the lines coincide.
3. *(No essential line.)* Every line lies in the span of the others. Equivalently every proper subfamily has Gram nullity at most $2$, and $\ker\Gamma$, of dimension exactly $3$, has no coordinate identically zero.
4. *(Connected.)* $G$ is connected.
5. *(Light vertices.)* Every vertex satisfies $\sum_{u\sim v}\delta(v,u)<\pi/2$. Nevertheless every vertex $v$ at which some nonzero kernel vector attains its maximum modulus satisfies $\sum_{u\sim v}|\langle x_v,x_u\rangle|\ge1$.
6. *(Cycle structure.)* $|E(G)|\ge d+4$, and the numbers $n_k$ of vertices of degree $k$ satisfy $n_3\ge n_1+2\ge2$.
7. *(Local ranks.)* For every $v$, $X\setminus v$ has rank $d$, and $X\setminus(\{v\}\cup N(v))$ has rank $d-1$ and nullity $3-\deg v$.
8. *(No long degree-two chains.)* $G$ contains no path $v_1v_2v_3v_4v_5$ on five distinct vertices with $\deg v_2=\deg v_3=\deg v_4=2$ and $v_1$ not adjacent to $v_5$.

Consequently, $F(d)$ holds for all $d\ge4$ as soon as every configuration satisfying 1–8 has $D\ge3\pi/2$.

*Proof.* Item 1 is the sparse-maximizer argument of [C4 §1](../c4/proof.md#1-a-maximizing-configuration-can-be-made-sparse) with $N-d=3$; note that maximizing $S$ is minimizing $D$. Since the lines orthogonal to $v$ lie in $v^\perp$ and contain $d-1$ independent vectors, they span $v^\perp$.

Item 2: if two lines coincide, Lemma 3.2(b) and C5 (for $d+2$ lines in $\mathbb R^d$) give $D(X)\ge\frac\pi2+\pi$.

Item 3: if $v\notin\operatorname{span}(X\setminus v)$, then $X\setminus v$ consists of $(d-1)+3$ vectors in a $(d-1)$-dimensional space, and Lemma 3.2(a) with $F(d-1)$ gives $D(X)\ge3\pi/2$. If a proper subfamily $S$ had nullity $3$, its rank would be $|S|-3$, and adding the remaining $d+3-|S|$ lines one at a time must raise the rank to $d$, by exactly one at each step; the last line added then lies outside the span of all the others and is essential. Hence every proper subfamily has nullity at most $2$. The kernel statement is a restatement: $c_v=0$ for all $c\in\ker\Gamma$ exactly when $v$ is essential. The nullity of $\Gamma$ is $(d+3)-d=3$ by item 1.

Item 4: suppose $G$ has components $X_1,\dots,X_m$ with $m\ge2$, sizes $n_c$, ranks $r_c$ and nullities $\nu_c=n_c-r_c\ge0$. Then $\sum_cr_c=d$ (item 1) and $\sum_c\nu_c=3$; each $r_c\ge1$, so each $r_c\le d-1$. We claim $D(X_c)\ge\nu_c\pi/2$ for each part: for $\nu_c=0$ trivially; for $\nu_c=1$ by (A); for $\nu_c=2$ by C5 if $r_c\ge2$, and for $r_c=1$ the three lines coincide, giving $3\pi/2\ge\pi$; for $\nu_c=3$ by $F(r_c)$, which is known for $r_c\le3$ and assumed for $4\le r_c\le d-1$. Summing, $D(X)\ge3\pi/2$.

Item 5: if $\sum_{u\sim v}\delta(v,u)\ge\pi/2$ for some $v$, Lemma 3.2 and C5 give $D(X)\ge\frac\pi2+\pi$. The second statement is Lemma 3.4(iii).

Item 6: by items 3 and 4, $G$ is connected with $\dim\ker\Gamma=3$, so Lemma 3.4(ii) gives $|E|\ge|V|+1=d+4$. Then $\sum_v(\deg v-2)=2|E|-2|V|\ge2$; since degrees are at most $3$, this sum equals $n_3-n_1$.

Item 7: by item 3, deleting $v$ does not lower the rank. By item 1 the lines not adjacent to $v$ are exactly the lines orthogonal to $v$, they span $v^\perp$ of dimension $d-1$, and there are $d+2-\deg v$ of them.

Item 8 follows from Lemma 4.2 below: if such a path existed, the lemma would produce $d+2=(d-1)+3$ lines in the $(d-1)$-dimensional space $v_3^\perp$ with $D'\le D(X)<3\pi/2$, contradicting $F(d-1)$.

For the final sentence: if no configuration satisfying 1–8 has $D<3\pi/2$, then the minimizer $X$ has $D(X)\ge3\pi/2$, so $F(d)$ holds; induct on $d$ from the known $F(1),F(2),F(3)$. $\square$

**Lemma 4.2 (shortening a degree-two chain).** Let $X$ be unit vectors in $\mathbb R^d$ whose nonorthogonality graph contains a path $v_1v_2v_3v_4v_5$ on five distinct vertices with $\deg v_2=\deg v_3=\deg v_4=2$ and $v_1$ not adjacent to $v_5$. Remove $v_3$ and replace $v_2,v_4$ by their normalized orthogonal projections onto $v_3^\perp$, leaving all other vectors unchanged. The new family $X'$ has $|X|-1$ vectors in $v_3^\perp$ and $D(X')\le D(X)$.

*Proof.* This is the projection step of [C5 §2](../c5/proof.md#2-projection-of-a-cycle-in-any-dimension) together with the scalar inequality of [C5 §1](../c5/proof.md#1-the-scalar-projection-inequality-in-its-general-form); we check that its hypotheses are exactly the stated ones. Nonadjacent pairs are orthogonal, so $v_1,v_3,v_5$ are pairwise orthogonal and $v_2\perp v_4$, $v_2\perp v_5$, $v_1\perp v_4$. Orient the representatives so that the four path inner products $a,b,c,d$ are positive. Then $v_2=av_1+bv_3+u$ and $v_4=cv_3+dv_5+w$ with $u,w\perp\operatorname{span}(v_1,v_3,v_5)$, $\langle u,w\rangle=-bc$, and $a>0$ forces $b<1$, so the normalizing constants $\sqrt{1-b^2},\sqrt{1-c^2}$ are positive. The C5 argument shows that the three new deficiencies among $v_1,v_2',v_4',v_5$ total at most the four old deficiencies along the path. Every other term is unchanged: a vector $z\notin\{v_1,\dots,v_5\}$ is orthogonal to $v_3$, so $\langle v_2',z\rangle=\langle v_2,z\rangle/\sqrt{1-b^2}$, and $\langle v_2,z\rangle=0$ because $v_2$ has no neighbours other than $v_1,v_3$; similarly for $v_4'$. $\square$

**Remark 4.3 (why the C5 step does not extend verbatim).** The natural inductive step for $F(d)$ removes one vertex $v$ and projects its neighbours onto $v^\perp$; by $F(d-1)$ it suffices that this does not increase $D$. Item 8 is exactly the case where this works. Two explicit examples show that the local inequality fails in general, so a proof of $F(d)$ must either choose the removed vertex using the global structure or use a different reduction.

- *Degree three.* Take $v=e_1$, $u_1=u_2=(e_1+e_2)/\sqrt2$, $u_3=(e_1-e_2)/\sqrt2$ in $\mathbb R^2$. The deficiencies among these four lines total $3\cdot\frac\pi4+\frac\pi2=\frac{5\pi}4$. Projecting $u_1,u_2,u_3$ onto $v^\perp$ makes them coincide, with total deficiency $\frac{3\pi}2$. (This example has coincident lines, which item 2 excludes.)
- *Leaf with distinct lines.* Let $v$ be a leaf attached to $u$, and let $u$ have two further neighbours $w_1,w_2$ with $\langle w_1,w_2\rangle=\cos\varepsilon$, $\varepsilon>0$ small, and $v\perp w_1,w_2$. Take $u=\sin\beta\,v+\cos\beta\,w_1$ with $0<\beta<\pi/2$. The deficiencies on the three edges at $u$ total $\beta+(\frac\pi2-\beta)+\arcsin(\cos\beta\cos\varepsilon)=\frac\pi2+\arcsin(\cos\beta\cos\varepsilon)$. After projecting $u$ onto $v^\perp$ it becomes $w_1$, and the two remaining edges have deficiency $\frac\pi2+(\frac\pi2-\varepsilon)=\pi-\varepsilon$. The projection increases the local deficiency by $\frac\pi2-\varepsilon-\arcsin(\cos\beta\cos\varepsilon)$, which tends to $\beta>0$ as $\varepsilon\to0$, while all five lines stay distinct.

Random sampling (see [local_ineq.py](local_ineq.py)) indicates that for a degree-three vertex whose three neighbours are pairwise orthogonal *and have no further neighbours*, the local inequality $\sum_i\beta_i\ge\sum_{i<j}\arcsin(\tan\beta_i\tan\beta_j)$ does hold, where $\beta_i=\delta(v,u_i)$ and $\sum_i\sin^2\beta_i\le1$; this is not proved here, and by item 6 the neighbours generally do have further neighbours, whose edges also change under projection.

**Question 4.4.** Does every configuration satisfying items 1–8 of Theorem 4.1 contain a vertex whose removal, with orthogonal projection of its neighbours, does not increase $D$? A positive answer for every $d\ge4$ proves $F(d)$, hence $\mathrm{C6}(d+3,d)$ for all $d$, by the induction of Theorem 4.1.

**Remark 4.5 (equality is far from unique).** Any proof strategy for C6 must accommodate a large equality set. Three planar lines have $D=\pi/2$ exactly when no half-open quarter circle of directions contains all three (this is the equality analysis of the C1 proof for $N=3$; for directions $0<\alpha<\beta<\pi$ one computes $D=\pi/2$ if $\beta\ge\pi/2$ and $D=3\pi/2-2\beta$ otherwise). Hence for $N=d+3$ with $d\ge6$, three such triples in three mutually orthogonal planes together with $d-6$ further orthogonal axes give $D=3\pi/2$ with all lines distinct and no coincidences; for $d\ge3$, two orthonormal bases of one plane together with a doubled orthogonal axis and $d-3$ further axes also give $D=\pi+\pi/2$. Both families were found by the numerical search of §5.

## 5. Numerical evidence

[explore.py](explore.py) minimizes $D$ over $N$ unit vectors in $\mathbb R^d$ by L-BFGS-B on a smoothed objective ($|t|$ replaced by $\sqrt{t^2+\varepsilon^2}$ inside $\arcsin$) with continuation $\varepsilon\to0$ and $40$ random restarts per case (seed $12345$; numpy 1.26.4, scipy 1.13.1, Python 3.12.7). It reports the exact deficiency of the best final configuration, the conjectured value $M(N,d)\pi/2$, the Gram rank, the degree sequence of the nonorthogonality graph (tolerance $10^{-6}$), and the configuration itself. Reproduce from this directory with

```sh
python3 explore.py 5,3 6,3 7,3 8,3 9,3 6,4 7,4 8,4 9,4 10,4 7,5 8,5 9,5 10,5 8,6 9,6 10,6 11,6 12,6 9,7 10,7
```

Results are in [explore-results.json](explore-results.json).

| $N$ | $d$ | $M(N,d)$ | conjectured $D$ | best numerical $D$ (raw) | raw $-$ conjectured | near-coincident pairs | snapped $-$ conjectured | degree sequence of best configuration |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 5 | 3 | 2 | 3.141592654 | 3.141592633 | -2.1e-08 | 2 | +1.6e-12 | 0,1,1,1,1 |
| 6 | 3 | 3 | 4.712388980 | 4.712388965 | -1.5e-08 | 1 | +1.4e-12 | 1,1,2,2,2,2 |
| 7 | 3 | 5 | 7.853981634 | 7.853981613 | -2.1e-08 | 2 | +2.7e-05 | 1,1,3,3,4,4,4 |
| 8 | 3 | 7 | 10.995574288 | 10.995574224 | -6.3e-08 | 3 | +1.9e-11 | 2,2,2,4,4,4,4,4 |
| 9 | 3 | 9 | 14.137166941 | 14.137166884 | -5.7e-08 | 3 | +2.8e-11 | 2,2,2,4,4,4,4,4,4 |
| 6 | 4 | 2 | 3.141592654 | 3.141592624 | -3.0e-08 | 2 | +6.5e-12 | 0,0,1,1,1,1 |
| 7 | 4 | 3 | 4.712388980 | 4.712388938 | -4.2e-08 | 3 | +2.1e-12 | 0,1,1,1,1,1,1 |
| 8 | 4 | 4 | 6.283185307 | 6.283185307 | +3.0e-13 | 0 | +3.0e-13 | 2,2,2,2,2,2,2,2 |
| 9 | 4 | 6 | 9.424777961 | 9.424777946 | -1.5e-08 | 3 | +2.4e-12 | 1,1,1,1,2,3,3,4,4 |
| 10 | 4 | 8 | 12.566370614 | 12.566370600 | -1.5e-08 | 2 | +2.5e-06 | 2,3,3,3,3,4,4,4,4,4 |
| 7 | 5 | 2 | 3.141592654 | 3.141592634 | -2.0e-08 | 2 | +4.2e-06 | 0,0,1,1,2,2,2 |
| 8 | 5 | 3 | 4.712388980 | 4.712388959 | -2.1e-08 | 2 | +1.6e-06 | 0,1,1,1,1,2,2,2 |
| 9 | 5 | 4 | 6.283185307 | 6.283185256 | -5.1e-08 | 4 | +5.0e-12 | 0,1,1,1,1,1,1,1,1 |
| 10 | 5 | 5 | 7.853981634 | 7.853981613 | -2.1e-08 | 1 | +1.4e-11 | 1,1,2,2,2,2,2,2,2,2 |
| 8 | 6 | 2 | 3.141592654 | 3.141592654 | +3.5e-14 | 0 | +3.5e-14 | 0,0,2,2,2,2,2,2 |
| 9 | 6 | 3 | 4.712388980 | 4.712388966 | -1.5e-08 | 2 | +7.8e-06 | 0,1,1,2,2,2,2,2,2 |
| 10 | 6 | 4 | 6.283185307 | 6.283185281 | -2.6e-08 | 3 | +5.1e-12 | 0,1,1,1,1,1,1,2,2,2 |
| 11 | 6 | 5 | 7.853981634 | 7.853981592 | -4.2e-08 | 3 | +1.9e-11 | 0,1,1,1,1,1,1,2,2,2,2 |
| 12 | 6 | 6 | 9.424777961 | 9.424777925 | -3.6e-08 | 2 | +7.0e-12 | 1,1,1,1,2,2,2,2,2,2,2,2 |
| 9 | 7 | 2 | 3.141592654 | 3.141592654 | +7.4e-13 | 0 | +7.4e-13 | 0,0,0,2,2,2,2,2,2 |
| 10 | 7 | 3 | 4.712388980 | 4.712388944 | -3.6e-08 | 3 | +2.2e-11 | 0,0,0,0,1,1,1,1,1,1 |

The full run of all $21$ cases took $14.6$ seconds of wall time on the development laptop.

Negative entries of order $10^{-8}$ in the raw column are a floating-point artifact, not violations: near-coincident pairs have $|\langle x,y\rangle|=1-\varepsilon$ with $\varepsilon\approx10^{-16}$, and $\arcsin(1-\varepsilon)\approx\frac\pi2-\sqrt{2\varepsilon}\approx\frac\pi2-1.5\cdot10^{-8}$. The snapped column treats pairs with $|\langle x,y\rangle|>1-10^{-6}$ as coincident; it is never below the conjectured value by more than rounding. This is a local search with random restarts: it supports the conjecture at these parameters and exhibits alternative equality configurations, but it is not a proof of anything, and it cannot rule out undiscovered minima.

## 6. Status, provenance, and what remains

**Status of the cell: not solved.** Proved here with complete written arguments: Lemma 1.1, Lemma 2.1, Corollary 2.2, Theorem 2.3, Corollary 2.4 (the $(6,3)$ case), Theorem 2.5 (explicit non-sharp bounds for all $N\ge d+2$), Lemmas 3.1–3.4, Theorem 4.1 and Lemma 4.2 (reduction of $N=d+3$). Not proved: any $\mathrm{C6}(N,d)$ with $N\ge d+3$ other than $(6,3)$; in particular no infinite family beyond C5 is established, and the connected sparse case of Theorem 4.1 is open. Nothing here is Lean-checked. Nothing has been submitted.

**Literature check (2026-09-26).** [Bilyk–Matzke](https://arxiv.org/abs/1801.07837) state that only the planar case is settled for all $N$, that Fejes Tóth confirmed the $\mathbb R^3$ case for $N\le6$, and prove the continuous bound $\max I(\mu)\le\frac\pi2-\frac{69}{50(d+1)}$ on $S^d\subset\mathbb R^{d+1}$ together with a dimension-reduction proposition for the continuous conjecture. [Lim–McCann](https://arxiv.org/abs/2007.08698) resolve the $\alpha=\infty$ member of a one-parameter family by an induction on dimension and number of lines, and state that for $d\ge2$ the original conjecture remains open. [Fodor–Vígh–Zarnócz](https://www.math.u-szeged.hu/~vigvik/preprints/egyenesekszogei.pdf) report that Fejes Tóth obtained $S(6,3)$ from $S(5,3)$ by a recursive bound, which is presumably the averaging of Theorem 2.3. None of these sources states a result for $N=d+3$ in general dimension; this is an absence in the sources inspected, not a proof that none exists. See also the [C5 literature note](../c5/literature.md).

**Plausible next steps.** (i) Settle Question 4.4, most likely by a case analysis on the neighbourhood of a well-chosen vertex using items 5–8 as fallbacks. (ii) Alternatively, prove the linear form "$D\ge(N-\operatorname{rank})\frac\pi2$", which by Lemma 1.1(f) is exactly C6 for $d<N\le2d$ and is implied by it otherwise; Lemma 3.2(a) and the projection identity $\operatorname{rank}(X')=\operatorname{rank}(X)-1$ show that a projection step never changes nullity, so an inductive proof needs only a suitable non-increase of $D$. (iii) A rigorous interval computation for the single case $(7,4)$ would, by Theorem 2.3, also give $(8,4)$, but the equality set of Remark 4.5 means the minimum is attained, so pure branch-and-bound on the value cannot close; a local argument near the equality set would be needed.
