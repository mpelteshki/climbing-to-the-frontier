# C1: planar lines

**Status: Solved — complete written proof; Lean partial.** The full proof covers every N ≥ 0.

The full statement is `S ≤ (π/2)⌊N²/4⌋` for N lines through the origin in ℝ². [written-proofs.md](../written-proofs.md) gives a complete mathematical proof for every N, including repeated lines. Its circle integration argument is not formalized in Lean.

[Angles.lean](../Angles.lean) proves the N = 2 bound through `Angles.angle2_le`, `Angles.c1_n3` (`S ≤ π` for three planar lines), and `Angles.c1_n4` (`S ≤ 2π` for four planar lines). N = 0 and N = 1 have empty sums but are not separate Lean declarations. Inputs are arbitrary real Cartesian unit vectors; the results are not limited to a finite coordinate grid. To check the shared source, run `lake env lean Angles.lean` from the package root.
