# C1: complete mathematical argument

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

## 1. Energy and the shape of a cyclic orbit

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

## 2. A higher occupied diagonal forces the lower one to be full

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

## 3. Every asserted boundary is cyclic

Conversely, take any length-$k$ bit word of weight $r$. The asserted pile list is decreasing: adjacent differences are $1+\varepsilon_j-\varepsilon_{j+1}\ge0$. Its only possible zero is the last entry, and its total is $T_{k-1}+r=n$.

Its number of positive piles is $k-1+\varepsilon_{k-1}$. One move therefore changes its boundary word to

$$
(\varepsilon_{k-1},\varepsilon_0,\ldots,\varepsilon_{k-2}).
$$

After $k$ moves it returns. This proves sufficiency. The word-to-partition map at fixed $k$ is injective: pad the partition with a final zero when needed and subtract $(k-1,k-2,\ldots,0)$. Hence two such partitions belong to the same cycle exactly when their words are rotations of one another.

## 4. Counting the cycles

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

## 5. Triangular convergence

For $n=T_k$, we have $r=k$. The only weight-$k$ binary word of length $k$ is the all-1 word, encoding the staircase. Thus the staircase is the only cyclic partition; the move description proves it is fixed.

There are finitely many partitions of $n$, and a move preserves $n$. Every forward trajectory therefore eventually repeats and enters a cycle. That cycle must be the staircase, proving eventual convergence. For $n=0$, the empty partition is fixed, so the same assertion holds with $k=0$.

## Verification boundary and provenance

The general statements in Sections 1–3 and 5 have corresponding Lean proofs in [Energy](../lean/ProofPursuit/P3/Energy.lean), [DiagonalOrder](../lean/ProofPursuit/P3/DiagonalOrder.lean), [RankedClassification](../lean/ProofPursuit/P3/RankedClassification.lean), [Necklace](../lean/ProofPursuit/P3/Necklace.lean), and [TriangularGeneral](../lean/ProofPursuit/P3/TriangularGeneral.lean). Section 4 is the remaining **unformalized counting argument**.

The independent [cycle-count checker](check_cycles.py) enumerates actual solitaire trajectories and compares their cycle counts with the formula and boundary encodings for each checked card count. This finite replay is a cross-check of the definitions and formula, not a substitute for the general written argument. [Recorded evidence](../evidence/cycle-counts.json).

These are classical results, not novelty claims. See [Griggs and Ho, *The Cycling of Partitions and Compositions under Repeated Shifts*](https://sc.edu/study/colleges_schools/artsandsciences/mathematics/research/imi/research/documents/1998/1998_12.pdf) for context. The proof above makes the energy, alignment, and counting steps explicit; it does not use a cited target theorem as a premise.
