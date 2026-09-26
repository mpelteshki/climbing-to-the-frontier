# Established optimal values and the remaining Lean gap

The explicit witnesses have path counts 14, 34, 88, 204, 464, 1040 in dimensions 3 through 8. These are the optimal values, using the following reduction and the established hypercube decycling numbers. The reduction and external decycling theorem have **not** been formalized in this Lean project. The Lean certificates prove the witness counts and hence upper bounds; they do not alone prove optimality.

## Reduction, proved mathematically

Orient every edge from its lower to its higher label. Write p(v) for the number of uphill paths ending at v. Then p(v)=1 at sources, and otherwise p(v)=sum p(u) over incoming neighbours. In particular p(v)>=1 at every vertex, by induction through the labels.

Let G be d-regular, with n vertices and m edges. Let B={v:p(v)>1}, b=|B|, s the number of sources, and e_B the number of edges with both ends in B.

No edge goes from B to its complement: such an edge would make the endpoint's count at least 2. Every nonsource vertex outside B therefore has exactly one incoming edge, also from outside B. Hence the subgraph on V\B has n-b-s edges and is a forest. To see acyclicity without a counting assumption, the maximum-labelled vertex of any undirected cycle would have two lower-labelled cycle neighbours and hence count at least 2. Thus B is a feedback vertex set.

The degree sum at B gives

    m = (n-b-s) + d*b - e_B,
    s = n-m+(d-1)*b-e_B.

Counting paths by their last edge, with singleton sources separately, gives

    P = s + sum_{u->v} p(u)
      = m+s+sum_{u in B} (p(u)-1)*outdeg(u).

Every internal B-edge contributes at least 1 to the last sum. Consequently

    P >= m+s+e_B = n+(d-1)*b
      >= n+(d-1)*decycling_number(G).

## C1, self-contained lower bound

There is at least one source. Since e_B>=0, the identity for s gives (d-1)*b>=m-n+1.

For Q3, (n,m,d)=(8,12,3), so b>=3 and P>=14.
For Q4, (n,m,d)=(16,32,4), so b>=6 and P>=34.
The certified labellings attain these bounds.

## C2–C4, established decycling theorem

Beineke and Vandell, *Decycling graphs*, Journal of Graph Theory 25 (1997), 59–77, established the decycling numbers for Q3 through Q8:

| d | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| decycling number | 3 | 6 | 14 | 28 | 56 | 112 |
| n+(d-1)*decycling number | 14 | 34 | 88 | 204 | 464 | 1040 |

Original paper: https://onlinelibrary.wiley.com/doi/10.1002/(SICI)1097-0118(199705)25:1%3C59::AID-JGT4%3E3.0.CO;2-H

The table is reproduced in Section 2 of the primary-author survey *The Decycling Number of Graphs*: https://arxiv.org/pdf/math/0703544 (PDF page 3). The general doubling lower bound follows by restricting a feedback vertex set to each of two disjoint (d-1)-dimensional faces. Thus the value 14 for Q5 also supplies the lower bounds 28,56,112 for Q6,Q7,Q8.

No reference is imported as an axiom. Full Lean optimality still requires formalizing the reduction and the relevant feedback-vertex-set lower bounds. C5 and C6 remain unworked under the instruction to pause open-problem research.
