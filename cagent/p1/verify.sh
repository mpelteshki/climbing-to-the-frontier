#!/bin/sh
set -eu
cd "$(dirname "$0")"
export MATHLIB_CACHE_DIR="$PWD/.cache"
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake update
lake exe cache get \
  Mathlib.Analysis.Convex.Deriv \
  Mathlib.Analysis.Convex.Function \
  Mathlib.Analysis.InnerProductSpace.Basic \
  Mathlib.Analysis.InnerProductSpace.Continuous \
  Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional \
  Mathlib.Analysis.Normed.Module.Convex \
  Mathlib.Analysis.SpecialFunctions.Sqrt \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv \
  Mathlib.Data.Finset.Card \
  Mathlib.Data.Finset.Max \
  Mathlib.LinearAlgebra.Dimension.Constructions \
  Mathlib.LinearAlgebra.Dimension.StrongRankCondition \
  Mathlib.LinearAlgebra.FiniteDimensional.Lemmas \
  Mathlib.LinearAlgebra.Matrix.Rank \
  Mathlib.LinearAlgebra.Span.Basic \
  Mathlib.Order.Preorder.Finite \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.Ring \
  Mathlib.Topology.MetricSpace.ProperSpace \
  Mathlib.Topology.Order.Compact
mkdir -p .lake/build/lib/lean
for module in \
  Angles C4Pentagon C4Extremum C4Rotation C4SparseStep C4SignedSparse \
  C4Geometry C4LocalRotation C4Selection C4Configuration C4Replacement \
  C4Direction C4MaximalSparse C4NeighborCount C4SparseConfiguration \
  C4MatrixCorank C4FiveCycle C4SixCycle
do
  lake env lean -o ".lake/build/lib/lean/$module.olean" "$module.lean"
done
