#!/bin/sh
set -eu
cd "$(dirname "$0")"
export MATHLIB_CACHE_DIR="$PWD/.cache"
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake update
lake exe cache get \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.Ring \
  Mathlib.Tactic.NormNum
lake env lean Angles.lean
