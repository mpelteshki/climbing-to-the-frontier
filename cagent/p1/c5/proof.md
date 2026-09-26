# C5 — complete written proof for $d+2$ lines

For every $d\ge2$ and $N=d+2$ lines through the origin in $\mathbb R^d$, with repetitions allowed, the exact [C5 statement](https://hackathon.bainsa.ai/p/p1/c5) (also in [statements.md](../statements.md)) asks for

$$
\sum_{i<j}\theta(x_i,x_j)\le\left(\binom N2-2\right)\frac{\pi}{2},\qquad \theta(x,y)=\arccos|\langle x,y\rangle|.
$$

Equivalently, for unit representatives and $\delta(x,y)=\arcsin|\langle x,y\rangle|$,

$$
D=\sum_{i<j}\delta(x_i,x_j)\ge\pi.
$$

This is a written proof reconstructed in this work. It extends the projection argument in the [C4 proof](../c4/proof.md); no claim of mathematical novelty is made. The extension and its hypotheses were independently reviewed. The full C5 theorem is not verified in Lean; the checked subclaims and commands are recorded in the [replay evidence](../evidence/replay/README.md).

## 1. The scalar projection inequality in its general form

For acute $B,U$ define

$$
g(B,U)=B+U-\arccos(\cos B\cos U).
$$

For $B,C,U,V\in(0,\pi/2)$, suppose

$$
\tan B\tan C\le\sin U\sin V.
$$

Then

$$
\arcsin(\tan B\tan C)\le g(B,U)+g(C,V).\tag{1}
$$

The arcsine argument is in $(0,1)$, since $\sin U\sin V<1$. Put

$$
U_0=\arcsin\!\left(\frac{\tan B\tan C}{\sin V}\right).
$$

The hypothesis and sine monotonicity on $[0,\pi/2]$ give $0<U_0\le U<\pi/2$. Choose $T\in(0,\pi/2)$ with

$$
\tan T=\frac{\sin U_0}{\tan B}=\frac{\tan C}{\sin V}.
$$

Thus

$$
\begin{aligned}\sin B\sin T&=\cos B\sin U_0\cos T,\\\sin C\cos T&=\cos C\sin V\sin T.\end{aligned}
$$

The equality-case projection inequality proved in C4, and formalized as `C4Pentagon.local_projection_inequality`, gives

$$
\arcsin(\sin U_0\sin V)\le g(B,U_0)+g(C,V).
$$

Its left side is $\arcsin(\tan B\tan C)$. It remains to compare $U_0$ with $U$. For fixed $B\in(0,\pi/2)$,

$$
\frac{\partial g(B,U)}{\partial U}=1-\frac{\cos B\sin U}{\sqrt{1-\cos^2B\cos^2U}}\ge0.
$$

The denominator is positive, and its square minus $(\cos B\sin U)^2$ equals $\sin^2 B$. Consequently $g(B,U_0)\le g(B,U)$, proving (1). This monotonicity extension is written only; the equality-case inequality is Lean-verified.

## 2. Projection of a cycle in any dimension

Consider an irreducible nonorthogonality cycle of length $k\ge6$ and rank $k-2$. Remove one vertex and project its two neighbors onto its orthogonal complement, normalizing both. All remaining vertices were already orthogonal to the removed vertex.

Write the five-vertex path around the removed vertex as $(v_1,v_2,v_3,v_4,v_5)$, with $v_3$ removed. Orient the representatives along this path so that the four consecutive inner products $a,b,c,d$ are positive. Because $k\ge6$, the odd vectors $v_1,v_3,v_5$ are orthonormal and $v_2\perp v_4$. Decompose

$$
\begin{aligned}v_2&=av_1+bv_3+u,\\v_4&=cv_3+dv_5+v,\end{aligned}
$$

where $u,v$ are orthogonal to the span of $v_1,v_3,v_5$. Then

$$
\begin{aligned}a^2+b^2+\|u\|^2&=1,\\c^2+d^2+\|v\|^2&=1,\\\langle u,v\rangle&=-bc.\end{aligned}
$$

Cauchy–Schwarz yields $bc\le\|u\|\|v\|$. Since $a,b,c,d>0$, the residual vectors are nonzero and

$$
A=\sqrt{1-b^2}>0,\qquad Q=\sqrt{1-c^2}>0.
$$

Set

$$
\begin{aligned}B&=\arcsin b,&C&=\arcsin c,\\\cos U&=a/A,&\sin U&=\|u\|/A,\\\cos V&=d/Q,&\sin V&=\|v\|/Q.\end{aligned}
$$

These specify angles $B,C,U,V\in(0,\pi/2)$. Moreover,

$$
\tan B\tan C=\frac{bc}{AQ}\le\frac{\|u\|\|v\|}{AQ}=\sin U\sin V.
$$

Only four old deficiencies and three new deficiencies change. The original local contribution is

$$
\arcsin a+B+C+\arcsin d=\pi-\arccos(\cos B\cos U)-\arccos(\cos C\cos V)+B+C.
$$

The normalized projections of $v_2,v_4$ have inner products $a/A$ with $v_1$, $d/Q$ with $v_5$, and $-bc/(AQ)$ with each other. Their local contribution is therefore

$$
\pi-U-V+\arcsin(\tan B\tan C).
$$

Inequality (1) says that the new contribution is at most the old contribution. Every other surviving inner product is unchanged: vectors outside the two projected neighbors are orthogonal to $v_3$, and all nonincident products with either projected neighbor were zero. The removed vertex had nonzero products only with those two neighbors. Thus projection does not increase total deficiency.

The original cycle spans a space of dimension $k-2$. After projection, the $k-1$ remaining lines lie in a space of dimension at most $k-3$. No assertion about their new Gram rank or graph structure is needed.

## 3. Induction and component accounting

We prove the desired bound by strong induction on $N\ge4$. The sparse-maximizer argument from C4 applies in every finite dimension: some angle maximizer has at most $N-d=2$ nonorthogonal neighbors per line. The corresponding general geometric reduction is also Lean-verified as `C4SparseConfiguration.exists_degree_two_maximizer`.

Its nonorthogonality graph has only path and cycle components. The Gram matrix is block diagonal across these components. Its rank is at most $d=N-2$, so its total nullity is at least two; full spanning is unnecessary here. An irreducible path block has nullity at most one; an irreducible cycle block has nullity at most two. These matrix bounds are Lean-verified under their explicit ordered-band hypotheses in [C4MatrixCorank.lean](../C4MatrixCorank.lean).

If at least two components are singular, each contributes deficiency at least $\pi/2$ by the general auxiliary C3 bound proved in [C4 §1](../c4/proof.md#1-a-maximizing-configuration-can-be-made-sparse). Their total already gives $D\ge\pi$. If exactly one component is singular, it must be a cycle of nullity two, of some length $k\le N$, and its rank is $k-2$.

The small cycles are settled as follows:

- $k=3$: rank one forces all three lines to coincide, giving deficiency $3\pi/2$.
- $k=4$: the two opposite orthogonal pairs are bases of one plane; the four edge deficiencies sum to $\pi$.
- $k=5$: the explicit pentagon inequality in [C4 §3](../c4/proof.md#3-the-five-cycle) gives deficiency at least $\pi$. Its scalar coordinate bound is Lean-verified in [C4FiveCycle.lean](../C4FiveCycle.lean).

These cases include the $N=4$ and $N=5$ bases. If $k\ge6$, apply §2. The resulting $k-1$ lines lie in dimension at most $k-3$ and $k-1<N$. Embed their span into $\mathbb R^{k-3}$ if necessary. The induction hypothesis gives projected deficiency at least $\pi$, and projection did not increase deficiency. The original cycle therefore contributes at least $\pi$ too. Every other component contributes a nonnegative amount.

This proves $D\ge\pi$ in all cases, and hence the C5 angle bound. Equality is attained by coordinate axes with multiplicities $(2,2,1,\ldots,1)$, which have exactly two coincident pairs.

## Assurance and method fit

The mathematical argument is complete on independent review. The scalar monotonicity extension, graph component classification, Gram rank-to-span and coordinate extraction, component deficiency accounting, and final induction are not assembled into a full Lean theorem. Existing checked lemmas do not silently certify these steps.

For this extension, a line-by-line mathematical proof adds more immediate value than expanding Lean encodings of the finite graph and coordinate bookkeeping. The difficult trigonometric core, geometric sparse-maximizer reduction, and local matrix bounds already have kernel-checked companions. This complete written proof meets the cell's stated written-proof requirement; full Lean formalization remains incomplete. This is not an organizer acceptance or submission claim. C6 remains paused; no claim about arbitrary $N,d$ is made.
