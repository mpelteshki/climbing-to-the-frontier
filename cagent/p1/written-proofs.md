# Written proofs — partial Lean formalizations

The exact [C1](https://hackathon.bainsa.ai/p/p1/c1) and [C2](https://hackathon.bainsa.ai/p/p1/c2) statements are also transcribed in [statements.md](statements.md). The [Lean replay](evidence/replay/README.md) verifies specific small cases; it does not formalize the arguments below.

## C1: all $N$ planar lines

For the [C1 statement](https://hackathon.bainsa.ai/p/p1/c1), let $x_1,\ldots,x_N$ represent $N\ge0$ lines in $\mathbb R^2$, and put $S=\sum_{i<j}\arccos|\langle x_i,x_j\rangle|$. The target is

$$
S\le\frac{\pi}{2}\left\lfloor\frac{N^2}{4}\right\rfloor.
$$

Represent each line by a point $\alpha$ on the circle $\mathbb R/(\pi\mathbb Z)$, of circumference $\pi$. Its distance from another point is the shorter circular arc, hence exactly the non-obtuse line angle.

For $t$ on that circle, let $A_t$ be the half-open semicircle $[t,t+\pi/2)$, and let $k(t)$ count the $N$ line-points in $A_t$, with multiplicity. Exactly $k(t)(N-k(t))$ unordered pairs have one point in $A_t$ and one outside.

For two fixed points at circular distance $\delta\in[0,\pi/2]$, the set of $t$ separating them has length $2\delta$. Indeed the sets of $t$ for which each point is in $A_t$ are semicircles whose symmetric difference consists of two intervals of length $\delta$; this also handles coincident or opposite points. Endpoints have measure zero.

Integrate the pair count over a full period. All functions are finite step functions, so ordinary Riemann integration and finite additivity suffice:

$$
2S=\int_0^\pi k(t)(N-k(t))\,dt
\le \pi\left\lfloor\frac{N^2}{4}\right\rfloor.
$$

The inequality follows from $4k(N-k)=N^2-(N-2k)^2$ and integrality. Divide by $2$. Equality is attained by $\lfloor N/2\rfloor$ copies of one axis and $\lceil N/2\rceil$ copies of its perpendicular axis.

This proves C1 mathematically for every $N$, including repeated lines. The circle/cut identity and integration argument are not yet formalized in Lean. Lean currently proves only explicitly listed small-$N$ geometric cases.

## C2: all $m$, via positive definiteness

For the [C2 statement](https://hackathon.bainsa.ai/p/p1/c2), let $m\ge2$ and $x_1,\ldots,x_m$ be unit vectors in $\mathbb R^{m-1}$ with $\langle x_i,x_j\rangle=0$ whenever $|i-j|\ge2$. The target is

$$
\sum_{i=1}^{m-1}\arccos|\langle x_i,x_{i+1}\rangle|\le(m-2)\frac{\pi}{2}.
$$

Let $G$ be the $m\times m$ Gram matrix. It has diagonal $1$ and vanishes off the first off-diagonals. Since the vectors lie in $\mathbb R^{m-1}$, $G$ is singular. Successive sign changes of the vectors make every adjacent entry $a_i$ nonnegative; this preserves all absolute inner products, and hence every line angle. Write $\beta_i=\arcsin(a_i)\in[0,\pi/2]$. The desired inequality is equivalent to $\sum_i\beta_i\ge\pi/2$.

Suppose instead $B=\sum_i\beta_i<\pi/2$. Let $B_i=\beta_1+\cdots+\beta_i$. Set $b_1=a_1$, and inductively

$$
b_i=\frac{a_i}{\sqrt{1-b_{i-1}^2}}.
$$

We show $0\le b_i\le\sin B_i<1$, so every denominator exists and is positive. The base case is $b_1=\sin\beta_1$. At the inductive step, $b_{i-1}\le\sin B_{i-1}$ implies

$$
\sqrt{1-b_{i-1}^2}\ge\cos B_{i-1}>0.
$$

Since $B_i<\pi/2$,

$$
\sin B_i\cos B_{i-1}-\sin\beta_i
=\sin B_{i-1}\cos B_i\ge0.
$$

Therefore $b_i\le\sin\beta_i/\cos B_{i-1}\le\sin B_i<1$.

Now eliminate successive rows/columns of the tridiagonal matrix $G$. Its $LDL^{\mathsf T}$ pivots are

$$
d_1=1,\qquad d_{i+1}=1-\frac{a_i^2}{d_i}=1-b_i^2.
$$

All pivots are positive. Explicitly, take $L$ lower bidiagonal, with diagonal $1$ and $L_{i+1,i}=a_i/d_i$. Direct multiplication gives $G=L\operatorname{diag}(d_1,\ldots,d_m)L^{\mathsf T}$. Thus $\det G=\prod_i d_i>0$, contradicting singularity. This contradiction proves $\sum_i\beta_i\ge\pi/2$ and hence C2.

This is a full written argument, including zero adjacent products. The general matrix factorization/rank argument and scalar induction are not formalized here. The actual geometric $m=2$ and $m=3$ cases are separately Lean-checked when listed in [README.md](README.md).

## Scope

The general C3 auxiliary bound and both C4 bounds have complete written proofs in [c4/proof.md](c4/proof.md). The general C5 bound has a complete written proof in [c5/proof.md](c5/proof.md). Their full Lean assembly remains incomplete; specific C4 analytic, geometric-reduction, and matrix lemmas are verified separately. C6 work is paused by explicit user direction. No source citation substitutes for any proof above.
