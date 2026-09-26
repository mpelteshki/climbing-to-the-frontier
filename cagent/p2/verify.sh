#!/bin/sh
set -eu
cd "$(dirname "$0")"

echo "Lean toolchain:"
lean --version
echo "Build complete C1 optimality proofs and dependencies:"
lake build C1Optimal
echo "Kernel-check C1 proof artifact:"
lake env leanchecker C1Optimal
echo "Check C1 theorem axioms:"
lake env lean shared/LowerBound.lean
lake env lean shared/RegularLower.lean
lake env lean c1/C1Optimal.lean
echo "Build and kernel-check the reusable path-count lower bound:"
lake build DecyclingBridge
lake env leanchecker DecyclingBridge
lake env lean shared/DecyclingBridge.lean
for d in 5 6 7 8; do
  case "$d" in
    5) part=c2 ;;
    6) part=c3 ;;
    7|8) part=c4 ;;
  esac
  echo "Verify Q$d in $part:"
  /usr/bin/time -p lake env lean "$part/Q$d.lean"
done
