#!/bin/sh
set -eu
cd "$(dirname "$0")"

echo "Lean toolchain:"
lean --version
echo "Build shared semantics and fast counting theorem:"
lake build Fast
for d in 3 4 5 6 7 8; do
  case "$d" in
    3|4) part=c1 ;;
    5) part=c2 ;;
    6) part=c3 ;;
    7|8) part=c4 ;;
  esac
  echo "Verify Q$d in $part:"
  /usr/bin/time -p lake env lean "$part/Q$d.lean"
done
