# C4 — complete written proof, Lean formalization still partial

The exact [C4 statement](https://hackathon.bainsa.ai/p/p1/c4), also transcribed in [statements.md](../statements.md), asks for at most $4\pi$ for five lines in $\mathbb R^3$ and $13\pi/2$ for six lines in $\mathbb R^4$. [Lean replay evidence](../evidence/replay/README.md) records the separately verified lemmas. Write the deficiency of unit representatives $x,y$ as

$$
\delta(x,y)=\arcsin|x\cdot y|=\frac{\pi}{2}-\theta(x,y).
$$

Both targets say that the sum of all deficiencies is at least $\pi$. Repeated lines are allowed. The argument below is a written proof. Lean verifies analytic and sparse-geometric reduction lemmas, but does not yet assemble the full C4 statement.

## 1. A maximizing configuration can be made sparse

For fixed $N,d$, the angle sum attains a maximum on the compact product of $N$ unit spheres. Among maximizers choose one with the largest number of orthogonal pairs.

For a vector $x$ with at least one nonorthogonal neighbor, let $W$ span its orthogonal neighbors. If $\dim W<d-1$, choose a unit $y$ orthogonal to $W$ and to $x$. Move $x$ along $x(t)=x\cos t+y\sin t$. Every existing orthogonality is preserved. For any other vector $z$ not orthogonal to $x$, its inner product is $A\cos t+B\sin t$, with $A\ne0$. On the interval between its consecutive zeros containing $t=0$, its line angle is convex. To check this, write the signed inner product as $r\cos(t-t_0)>0$, $0<r\le1$. For $r<1$,

$$
\frac{d^2}{dt^2}\arccos(r\cos t)=\frac{r(1-r^2)\cos t}{(1-r^2\cos^2 t)^{3/2}}\ge0.
$$

For $r=1$ the angle is an absolute-value function on that interval, also convex. Intersect these zero-free intervals for all nonorthogonal neighbors. The total angle sum is convex there, and has its global maximum at the interior point $0$, so it is constant. At an endpoint at least one additional pair becomes orthogonal, while no orthogonal pair is lost. This contradicts the choice of maximizer.

Here $N>d$, so at least one pair is nonorthogonal. If the configuration spanned dimension $r<d$, an endpoint $x$ of such a pair would have $\dim W\le r-1<d-1$, contradicting the preceding rotation argument. Thus the configuration spans $\mathbb R^d$. For a vector orthogonal to every other vector, those other vectors consequently span its entire orthogonal complement; its orthogonal-neighbor span has dimension $d-1$ too. Every vector therefore has at least $d-1$ linearly independent orthogonal neighbors. Its nonorthogonality graph (an edge means nonzero inner product) has maximum degree at most $N-d$.

For $N=d+1$, this graph consists of edges and isolated vertices. The Gram matrix has nullity one. Some two-vertex block must have rank one, hence its two lines coincide and contribute deficiency $\pi/2$. We have proved the auxiliary bound:

For $m\ge2$, any $m$ unit vectors spanning dimension at most $m-1$ have total deficiency at least $\pi/2$. This is the auxiliary bound (A).

To apply it in smaller dimension, embed that space in $\mathbb R^{m-1}$.

For $N=d+2$, the sparse graph consists of paths and cycles. Gram blocks belonging to different components are orthogonal. An irreducible path block has nullity at most one: the first row and the tridiagonal recurrence determine every kernel coordinate from the first coordinate. An irreducible cycle block has nullity at most two: two adjacent coordinates determine all others. The whole matrix has nullity exactly two. If two components are singular, (A) gives deficiency at least $\pi/2$ in each, proving the target. Otherwise one cycle has nullity two, and all other components are nonsingular.

For $N\le6$ only cycles of lengths $3,4,5,6$ remain.

A three-cycle of nullity two has rank one: all three lines coincide and its deficiency is $3\pi/2$. A four-cycle of nullity two has rank two: its opposite pairs are orthonormal bases of the same plane. For every unit planar vector, its acute angles to an orthogonal pair sum to $\pi/2$. Consequently the four edge deficiencies sum to $\pi$.

## 2. Two elementary analytic inequalities

For $p,q\in[0,\pi/2]$, put

$$
\begin{aligned}h&=\arccos(\cos p\cos q),\\E(p,q)&=\arcsin\!\left(\frac{\sin p\sin q}{1+\cos p\cos q}\right).\end{aligned}
$$

Then

$$
h+E(p,q)\le p+q.\tag{B}
$$

Here is a direct proof, with no geometric theorem required. Set $A=\cos p$, $B=\cos q$, $r=\sin p\sin q$, $u=AB$, and $L=\sqrt{1-u^2}$. The identity

$$
(1+u)^2-r^2=(A+B)^2.
$$

gives $\cos E=(A+B)/(1+u)$. Therefore

$$
(1+u)[\cos(h+E)-\cos(p+q)]=-u(1-A)(1-B)+r(1+u-L)\ge0.
$$

Indeed $L\le1$ and $r\ge(1-A)(1-B)$, since $\sin t\ge1-\cos t$ on $[0,\pi/2]$. Both arguments compared lie in $[0,\pi]$, where cosine is decreasing. This proves (B). The Lean declaration `C4Pentagon.pentagon_scalar_angles` proves this inequality.

A second inequality, for $T,p,q\in[0,\pi/2]$, is

$$
\arcsin(\sin p\sin q)\le\arccos(\cos T\cos p)+\arccos(\sin T\cos q)-\frac{\pi}{2}.\tag{C}
$$

Set $X=\cos T\cos p$, $Y=\sin T\cos q$, and $Z=\sin p\sin q$. Direct expansion gives

$$
X^2+Y^2+Z^2+2XYZ-1=-(\cos T\sin p\cos q-\sin T\sin q\cos p)^2\le0.
$$

For nonnegative $X,Y,Z\le1$ this implies

$$
\sqrt{1-X^2}\sqrt{1-Y^2}\ge Z+XY.
$$

hence $\cos(\arccos X+\arccos Y)\le-Z$. Since $\arccos X+\arccos Y\in[0,\pi]$, cosine monotonicity gives their sum at least $\pi-\arccos Z$. This is (C).

## 3. The five-cycle

Its Gram rank is three. Take $x_1=e_1,x_3=e_2$, and choose signs of coordinates so that, in absolute value,

$$
x_4=(0,c,\sqrt{1-c^2}),\qquad x_5=(a,0,\sqrt{1-a^2}).
$$

where $0<a,c<1$. Possible remaining signs do not affect any formula below. Since $x_2$ is orthogonal to $x_4$ and $x_5$, their cross product determines it up to sign. With $L=\sqrt{a^2+c^2-a^2c^2}$, the absolute edge inner products are

$$
\frac{c\sqrt{1-a^2}}{L},\quad\frac{a\sqrt{1-c^2}}{L},\quad c,\quad\sqrt{1-a^2}\sqrt{1-c^2},\quad a.
$$

Write $a=\sin p,c=\sin q$. If the first two deficiencies are $U,V$, then

$$
\begin{aligned}\cos(U+V)&=\frac{\sin p\sin q}{1+\cos p\cos q},\\\sin(U+V)&=\frac{\cos p+\cos q}{1+\cos p\cos q}.\end{aligned}
$$

Thus $U+V=\pi/2-E(p,q)$. The middle product has deficiency $\pi/2-\arccos(\cos p\cos q)$. The total edge deficiency is therefore

$$
\pi+p+q-\arccos(\cos p\cos q)-E(p,q)\ge\pi.
$$

by (B). The expressions extend continuously to boundary cases; alternatively those cases break the cycle and were already handled. This completes the five-line $\mathbb R^3$ bound.

## 4. Removing a vertex from the six-cycle

The six-cycle has Gram rank four. Remove $x_6$ and project $x_1$ and $x_5$ orthogonally onto $x_6^\perp$, normalizing the results. The other three vectors already lie in that hyperplane. The resulting five lines lie in $\mathbb R^3$.

Only four original deficiencies and three projected deficiencies need comparison. Relabel the local path $(x_2,x_1,x_6,x_5,x_4)$ as $(v_1,v_2,v_3,v_4,v_5)$, and choose signs making its consecutive inner products $a,b,c,d$ positive. The odd vectors $v_1,v_3,v_5$ are orthonormal. In an orthonormal basis extending them,

$$
v_2=(a,b,0,u),\qquad v_4=(0,c,d,v),\qquad uv=-bc.
$$

All $a,b,c,d,|u|,|v|$ are positive for an irreducible six-cycle. Choose the fourth basis direction so $u>0$ and $v<0$. Consequently there are $P,Q,T\in(0,\pi/2)$ with

$$
\begin{aligned}a&=\cos P,&b&=\sin P\cos T,&u&=\sin P\sin T,\\d&=\cos Q,&c&=\sin Q\sin T,&v&=-\sin Q\cos T.\end{aligned}
$$

Let $B=\arcsin b,C=\arcsin c$. Let $p,q$ be the acute angles of the normalized projections of $v_2,v_4$ to $v_1,v_5$ respectively. Then

$$
\begin{aligned}\cos P&=\cos B\cos p,&\cos Q&=\cos C\cos q,\\\tan B&=\sin p\cot T,&\tan C&=\sin q\tan T.\end{aligned}
$$

The new connecting inner product has absolute value $\sin p\sin q$. Hence the original local deficiency is $\pi-P-Q+B+C$, whereas the projected local deficiency is $\pi-p-q+\arcsin(\sin p\sin q)$.

By (B),

$$
B+p-P\ge E(B,p),\qquad C+q-Q\ge E(C,q).
$$

The tangent relations imply the following exact identities:

$$
\begin{aligned}E(B,p)&=\arccos(\cos T\cos p)-T,\\E(C,q)&=\arccos(\sin T\cos q)-\left(\frac{\pi}{2}-T\right).\end{aligned}
$$

For completeness the first identity follows by substituting $\sin B\sin T=\cos B\sin p\cos T$ into the cosine addition formula for $E(B,p)+T$; the result is $\cos T\cos p$. Both angles are in $[0,\pi]$, making cosine injective. The second is the same computation with $T$ replaced by $\pi/2-T$.

Inequality (C) now gives

$$
(B+p-P)+(C+q-Q)\ge\arcsin(\sin p\sin q).
$$

Thus projection does not increase total deficiency. The projected five-line configuration has deficiency at least $\pi$ by the result just proved. The original six-cycle therefore also has deficiency at least $\pi$.

Combining all component cases proves both C4 bounds. Equality is attained by coordinate axes with two axes repeated: multiplicities $(2,2,1)$ in $\mathbb R^3$ and $(2,2,1,1)$ in $\mathbb R^4$.

## Formalization status

The analytic inequalities (B), (C), the exact gap identity, and the local projection inequality are Lean-verified in `C4Pentagon.lean`. The local geometric increment also verifies the explicit five-cycle deficiency bound, the six-cycle raw-coordinate projection inequality, compact maximizing-configuration selection, the rotation argument, the resulting maximum-degree-two reduction, and the path/cycle matrix corank bounds. The remaining full-cell obligations are the graph-component decomposition, extraction of the required Gram coordinates from arbitrary geometric cycle blocks, singular-component auxiliary bound assembly, and the final C4 inequalities. These are not supplied by the scalar theorem assumptions. C4 remains incomplete as a full Lean theorem. C6 work remains paused; nothing has been submitted to the hackathon.
