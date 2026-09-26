# Established optimal values and the remaining Lean gap

The explicit witnesses have path counts 14, 34, 88, 204, 464, 1040 in dimensions 3 through 8. These are the optimal values mathematically. For C1, [Lean proves](c1/C1Optimal.lean) that the Q3 and Q4 witnesses attain universal lower bounds. For C2–C4, the written reduction below, two independently replayable Q5 checks, and face doubling establish the lower bounds. The [path-count budget inequality](shared/DecyclingBridge.lean) is formalized, but its Q5 conclusion retains two explicit Lean premises; the external computations are not kernel proofs.

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
The certified labellings attain these bounds. The written argument is retained here; [`q3_optimal` and `q4_optimal`](c1/C1Optimal.lean) also prove the exact C1 values in Lean.

## C2, exact finite Q5 lower bound

Suppose removing at most 13 vertices makes Q5 a forest. Extend that deletion set to 13 vertices B; deleting more vertices preserves acyclicity. Q5 has 32 vertices, 80 edges, and degree 5. The 19-vertex complement has `80−5·13+e(B)=15+e(B)` edges, where `e(B)` counts edges inside B. A forest on 19 vertices has at most 18 edges, so `e(B)≤3`.

Partition Q5 by the parity of the number of one-bits. Each side has 16 vertices and every edge crosses the partition. XOR with 1 preserves adjacency and swaps the sides, so assume B has `k≤6` vertices on the even side. Fix such a subset A of size k. Each odd vertex v has cost `|N(v)∩A|`; selecting `13−k` odd vertices contributes the sum of their costs to `e(B)`. The cheapest possible sum is obtained by taking the `13−k` smallest of the 16 costs. [The parity replay](c2/decycling5_parity_replay.py) checks every even-side subset and obtains:

| k | 3 | 4 | 5 | 6 |
|---|---|---|---|---|
| even-side subsets checked | 560 | 1,820 | 4,368 | 8,008 |
| minimum internal edges | 4 | 4 | 5 | 5 |

Thus `e(B)≤3` leaves only `k=0,1,2`. For each of those cases, the replay visits every odd subset of the required size by include/exclude recursion. It discards a branch only if its accumulated cost exceeds 3 or too few odd vertices remain. It checks 560, 10,640, and 1,600 affordable sets, respectively. For each, it generates Q5 edges independently by one-bit flips and tests the 19-vertex complement with union-find. Every complement contains a cycle. The [parity log](c2/decycling5_parity_replay.log) records all counts and a hash of the 12,800 checked sets. This proves by exhaustive finite cases that every Q5 decycling set has at least 14 vertices. `python3 c2/decycling5_parity_replay.py` replays it in well under one second here.

The separate [cycle-branch replay](c2/decycling5_replay.py) regenerates the Q5 edge and short-cycle inventory, then branches on every vertex of the first unhit cycle while pruning only when the internal-edge budget is already exceeded. Its [log](c2/decycling5_replay.log) reports 42,324 states and `UNSAT`. This independently checks the finite obstruction without using the parity partition or forest test. The [Lean search-soundness theorem](shared/Decycling5.lean) validates the branch rule conditionally; its root Boolean result has not been proved by the kernel. Together with `P≥32+4|B|` and the Q5 witness count 88, the written and computed argument gives `U(Q5)=88`.

## C3–C4, face doubling and published comparison

For any decycling set in Qd, its intersections with the two disjoint `(d−1)`-dimensional faces are decycling sets in those faces. Therefore `∇(Qd)≥2∇(Q(d−1))`. Starting from the checked Q5 lower bound 14 gives lower bounds 28, 56, 112 for Q6–Q8. Substituting them into `P≥n+(d−1)|B|`, then using the packaged attaining witnesses, gives exact path-count optima 204, 464, 1040.

For comparison, Beineke and Vandell, *Decycling graphs*, Journal of Graph Theory 25 (1997), 59–77, reported these exact decycling numbers for Q3 through Q8:

| d | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| decycling number | 3 | 6 | 14 | 28 | 56 | 112 |
| n+(d-1)*decycling number | 14 | 34 | 88 | 204 | 464 | 1040 |

Original paper: https://onlinelibrary.wiley.com/doi/10.1002/(SICI)1097-0118(199705)25:1%3C59::AID-JGT4%3E3.0.CO;2-H

The table is reproduced in [§2, p. 288 of the primary-author Bau–Beineke survey](https://ajc.maths.uq.edu.au/pdf/25/ajc-v25-p285.pdf#page=4). [Zou's thesis, §2.2.3](https://www.math.mun.ca/~dapike/publications/Theses/YuboZou_PhD.pdf#page=28) and [Hertz's 2021 Table 4](https://jgaa-v5.cs.brown.edu/index.php/jgaa/article/download/paper567/2402/2209#page=17) also state the values. The accessible sources report Q5=14 but do not provide its special lower-bound proof line by line; the finite replay above reconstructs that step independently.

No reference is imported as an axiom. C2–C4 meet the task's value-and-label-list criteria, while full Lean optimality remains incomplete: `pathCount_lower5_of_search_and_edges` assumes the search root result and an edge-count comparison, and the face-doubling step for C3–C4 is written rather than formalized here. C5 and C6 remain paused.
