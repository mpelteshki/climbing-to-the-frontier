#!/bin/sh
set -eu
checkpoint=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
isolated=/Users/martin/Documents/LW/proof-pursuit-p1
fresh=$(mktemp -d /private/tmp/p1-c4-replay.XXXXXXXX)
printf '%s\n' "$fresh" > "$checkpoint/evidence/replay/output-dir.txt"
cd "$isolated"
lake env sh -c '
  set -eu
  fresh=$1
  checkpoint=$2
  root_build="$PWD/.lake/build/lib/lean"
  new_path=
  old_ifs=$IFS
  IFS=:
  for entry in $LEAN_PATH; do
    if [ "$entry" != "$root_build" ]; then
      new_path=${new_path:+$new_path:}$entry
    fi
  done
  IFS=$old_ifs
  export LEAN_PATH="$fresh:$new_path"
  for module in \
    Angles C4Pentagon C4Extremum C4Rotation C4SparseStep C4SignedSparse \
    C4Geometry C4LocalRotation C4Selection C4Configuration C4Replacement \
    C4Direction C4MaximalSparse C4NeighborCount C4SparseConfiguration \
    C4MatrixCorank C4FiveCycle C4SixCycle
  do
    printf "%s\n" "$module"
    lean -o "$fresh/$module.olean" "$checkpoint/$module.lean" \
      > "$checkpoint/evidence/replay/$module.log" 2>&1
  done
' sh "$fresh" "$checkpoint"
