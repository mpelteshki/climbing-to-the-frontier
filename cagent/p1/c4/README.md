# C4: five lines in ℝ³ and six lines in ℝ⁴

**Status: Solved — complete written proof; Lean partial.** Both requested bounds and equality examples are proved.

The [complete written proof](proof.md) establishes that the sum of all pairwise acute angles is at most 4π for five lines in ℝ³ and at most 13π/2 for six lines in ℝ⁴, including repeated lines. It uses a sparse-maximizer reduction, Gram graph and rank cases, a five-cycle coordinate argument, and a projection reduction for the six-cycle. Section 1 also proves the general written C3 auxiliary bound. The extremal examples show both C4 constants are sharp.

[C4Pentagon.lean](../C4Pentagon.lean) Lean-checks six analytic steps used in that proof:

| Declaration | Verified statement or role |
| --- | --- |
| `C4Pentagon.pentagon_scalar` | Scalar form of the pentagon estimate (B) |
| `C4Pentagon.pentagon_scalar_angles` | Acute-angle form of (B) |
| `C4Pentagon.arccos_triple_ge_pi` | Reverse three-arccos certificate for (C) |
| `C4Pentagon.six_cycle_scalar` | Acute-angle form of the six-cycle estimate (C) |
| `C4Pentagon.gap_angle_add_projection` | Exact right-triangle gap identity |
| `C4Pentagon.local_projection_inequality` | Local deficiency comparison under the two stated right-triangle relations |

Additional checked modules provide the explicit [five-cycle](../C4FiveCycle.lean) and [six-cycle](../C4SixCycle.lean) coordinate bounds; rotation convexity and endpoint lemmas ([C4Rotation.lean](../C4Rotation.lean), [C4SparseStep.lean](../C4SparseStep.lean), [C4SignedSparse.lean](../C4SignedSparse.lean), [C4Extremum.lean](../C4Extremum.lean)); vector rotation and local zero creation ([C4Geometry.lean](../C4Geometry.lean), [C4LocalRotation.lean](../C4LocalRotation.lean)); compact selection and replacement ([C4Selection.lean](../C4Selection.lean), [C4Configuration.lean](../C4Configuration.lean), [C4Replacement.lean](../C4Replacement.lean)); orthogonal direction and sparse degree-two reduction ([C4Direction.lean](../C4Direction.lean), [C4MaximalSparse.lean](../C4MaximalSparse.lean), [C4NeighborCount.lean](../C4NeighborCount.lean), [C4SparseConfiguration.lean](../C4SparseConfiguration.lean)); and [path/cycle matrix corank bounds](../C4MatrixCorank.lean). Exact replay logs are [indexed here](../evidence/replay/README.md).

The graph-component decomposition, extraction of Gram coordinates from arbitrary cycle blocks, singular-component auxiliary C3 assembly, and final bounds for arbitrary five/six-line configurations remain unformalized. Scalar cycle lemmas assume exact coordinate relations; they do not themselves prove the geometric setup.

Lean has been valuable for the error-prone scalar inequalities, rotation endpoint argument, and matrix rank bounds. The remaining graph and coordinate plumbing is costly to formalize and offers limited new mathematical insight. The independent complete written proof meets the live written-proof criterion; it is not a Lean-certified full cell or an organizer acceptance claim.
