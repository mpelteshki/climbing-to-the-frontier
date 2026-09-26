# C3: d + 1 lines

**Status: Solved — complete written proof; Lean partial.** The auxiliary argument in the C4 proof covers every d ≥ 1.

The [C4 written proof, §1](../c4/proof.md#1-a-maximizing-configuration-can-be-made-sparse) proves the general auxiliary C3 bound: for d + 1 lines spanning at most d dimensions, total deficiency is at least π/2. The sparse-maximizer reduction has separate Lean lemmas in [C4SparseConfiguration.lean](../C4SparseConfiguration.lean), but its full C3 deficiency assembly is not formalized. Direct Lean coverage of the C3 angle bound remains d = 1 and d = 2 only. For d = 1, `Angles.c2_m2` proves the two line representatives have angle zero. For d = 2, `Angles.c3_d2` proves the three planar line angles sum to at most π. These declarations are in [Angles.lean](../Angles.lean); run `lake env lean Angles.lean` from the checkpoint root.
