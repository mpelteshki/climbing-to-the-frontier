# Written proofs — not complete Lean formalizations

## C1: all N planar lines

Represent each line by a point α on the circle R/(π Z), of circumference π. Its distance from another point is the shorter circular arc, hence exactly the non-obtuse line angle.

For t on that circle, let A_t be the half-open semicircle [t,t+π/2), and let k(t) count the N line-points in A_t, with multiplicity. Exactly k(t)(N−k(t)) unordered pairs have one point in A_t and one outside.

For two fixed points at circular distance δ∈[0,π/2], the set of t separating them has length 2δ. Indeed the sets of t for which each point is in A_t are semicircles whose symmetric difference consists of two intervals of length δ; this also handles coincident or opposite points. Endpoints have measure zero.

Integrate the pair count over a full period. All functions are finite step functions, so ordinary Riemann integration and finite additivity suffice:

    2 S = ∫₀^π k(t)(N−k(t)) dt
        ≤ π floor(N²/4).

The inequality follows from 4k(N−k)=N²−(N−2k)² and integrality. Divide by 2. Equality is attained by floor(N/2) copies of one axis and ceil(N/2) copies of its perpendicular axis.

This proves C1 mathematically for every N, including repeated lines. The circle/cut identity and integration argument are not yet formalized in Lean. Lean currently proves only explicitly listed small-N geometric cases.

## C2: all m, via positive definiteness

Let G be the m×m Gram matrix. It has diagonal 1 and vanishes off the first off-diagonals. Since the vectors lie in R^(m−1), G is singular. Successive sign changes of the vectors make every adjacent entry a_i nonnegative; this preserves all absolute inner products, and hence every line angle. Write β_i=arcsin(a_i)∈[0,π/2]. The desired inequality is equivalent to Σβ_i≥π/2.

Suppose instead B=Σβ_i<π/2. Let B_i=β₁+⋯+β_i. Set b₁=a₁, and inductively

    b_i = a_i / sqrt(1−b_(i−1)²).

We show 0≤b_i≤sin B_i<1, so every denominator exists and is positive. The base case is b₁=sinβ₁. At the inductive step, b_(i−1)≤sin B_(i−1) implies

    sqrt(1−b_(i−1)²) ≥ cos B_(i−1)>0.

Since B_i<π/2,

    sin(B_i) cos(B_(i−1)) − sinβ_i
      = sin(B_(i−1)) cos(B_i) ≥ 0.

Therefore b_i≤sinβ_i/cos B_(i−1)≤sin B_i<1.

Now eliminate successive rows/columns of the tridiagonal matrix G. Its LDLᵀ pivots are

    d₁=1,  d_(i+1)=1−a_i²/d_i=1−b_i².

All pivots are positive. Explicitly, take L lower bidiagonal, with diagonal 1 and L_(i+1,i)=a_i/d_i. Direct multiplication gives G=L diag(d₁,…,d_m)Lᵀ. Thus det G=∏d_i>0, contradicting singularity. This contradiction proves Σβ_i≥π/2 and hence C2.

This is a full written argument, including zero adjacent products. The general matrix factorization/rank argument and scalar induction are not formalized here. The actual geometric m=2 and m=3 cases are separately Lean-checked when listed in README.

## Scope

C3–C5 general bounds remain unsolved in this work. C3 d=2 follows from the Lean three-planar-line result. C6 work is paused by explicit user direction. No source citation substitutes for any proof above.
