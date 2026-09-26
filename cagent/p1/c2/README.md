# C2: orthogonal non-neighbors

The full statement concerns m ≥ 2 unit vectors in ℝ^(m−1), with non-neighbors orthogonal. [written-proofs.md](../written-proofs.md) gives a complete mathematical argument using the tridiagonal Gram matrix and its positive pivots. The general matrix argument is not formalized in Lean.

[Angles.lean](../Angles.lean) proves `Angles.c2_m2` for two unit scalars in ℝ¹ and `Angles.c2_m3` for three unit planar vectors whose first and last vectors are orthogonal. The m = 3 conclusion is equality: both neighboring line angles sum to π/2. To check the shared source, run `lake env lean Angles.lean` from the package root.
