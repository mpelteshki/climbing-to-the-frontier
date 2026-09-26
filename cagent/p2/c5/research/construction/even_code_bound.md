# A self-contained upper bound for the even 9-bit code branch

Let $C\subseteq\{0,1\}^9$ consist entirely of even-weight words and have minimum Hamming distance at least four. Then $|C|\le20$. In particular, the 24-word code required by the proposed independent-feedback-set branch cannot exist. The sharp value $A(9,4)=20$ is also proved in [Best–Brouwer–MacWilliams–Odlyzko–Sloane, Theorem 6](https://neilsloane.com/doc/Me54.pdf#page=7); the argument here is self-contained.

Write $M=|C|$. For $t=4,6,8$, let $A_t$ be the average, over $x\in C$, of the number of words $y\in C$ at distance $t$ from $x$. All distances between distinct words are even because all words have even weight. Hence

$$
M=1+A_4+A_6+A_8.\tag{1}
$$

For each coordinate $i$, set $s_i=\sum_{x\in C}(-1)^{x_i}$. Expanding the nonnegative sum $\sum_i s_i^2$ by pairs $(x,y)$ gives

$$
0\le\sum_i s_i^2
=\sum_{x,y\in C}(9-2d(x,y))
=M(9+A_4-3A_6-7A_8).
\tag{2}
$$

Similarly, for each pair $i<j$ set $t_{ij}=\sum_{x\in C}(-1)^{x_i+x_j}$. If $d=d(x,y)$, the sum of $(-1)^{x_i+y_i+x_j+y_j}$ over all coordinate pairs equals $((9-2d)^2-9)/2$. Therefore

$$
0\le\sum_{i<j}t_{ij}^2
=M(36-4A_4+20A_8).
\tag{3}
$$

For each fixed $x$, there is at most one other word at distance eight: two distinct words each at distance eight from $x$ differ from one another in exactly two coordinates, violating minimum distance four. Thus $A_8\le1$.

Equations (2) and (3) yield

$$
A_6\le\frac{9+A_4-7A_8}{3},
\qquad A_4\le9+5A_8.
$$

Substitution in (1) gives

$$
M\le4+\frac43(A_4-A_8)
\le16+\frac{16}{3}A_8
\le\frac{64}{3}<22.
$$

As $M$ is integral, $M\le21$. To exclude equality, suppose $M=21$. Let $N_t=MA_t$ be the number of *ordered* pairs $(x,y)\in C^2$ at distance $t$, for $t=4,6,8$. Each $N_t$ is even: every unordered pair contributes both orders. The bound just obtained forces $A_8\ge15/16$, while $N_8\le M=21$ by distance-eight uniqueness. Thus $N_8$ is an even integer in $[315/16,21]$, so $N_8=20$.

There are $M(M-1)=420$ ordered distinct pairs, hence $N_4+N_6=400$. Expanding (2) and (3) after multiplication by $M$ gives

$$
\sum_i s_i^2=9M+N_4-3N_6-7N_8=449-4N_6\ge0,
$$

$$
\sum_{i<j}t_{ij}^2=36M-4N_4+20N_8=4N_6-444\ge0.
$$

The first inequality gives $N_6\le112$, the second gives $N_6\ge111$, and $N_6$ is even. Therefore $N_6=112$ and $\sum_i s_i^2=1$. But every $s_i$ is a sum of 21 signs, so it is an odd integer and $s_i^2\ge1$. The sum of nine such squares is at least 9, a contradiction. Hence $M\le20$.

The same upper bound applies to an arbitrary, possibly mixed-parity length-9 code of distance at least four. Puncture any coordinate to obtain eight-bit words of distance at least three, then append each word's parity bit. Their new distance is the least even integer at least their eight-bit distance, hence at least four. This produces an even-weight nine-bit code of the same size, so the bound just proved applies.

The 20-word code in [Östergård's author-maintained code archive](https://users.aalto.fi/~pat/opt/20_4.txt) shows sharpness. Its first code is `[0,63,85,90,99,142,147,184,201,228,263,281,298,365,368,417,438,450,476,507]`; every listed word has even parity and each pair has distance at least four. The local [`verify_code.py`](verify_code.py) checks these finite facts and the associated three-layer uphill-path count. The general upper-bound proof itself does not depend on that check.
