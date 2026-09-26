#!/bin/sh
# Full replay of every computation cited in output/RESULT.md.
# Run from output/code:   sh replay.sh            (about 2 minutes, one process)
#                         sh replay.sh full       (adds k=14, n=94: about 5 more minutes, ~2 GB RAM)
# Python 3 standard library only. Evidence JSON files are rewritten in ../evidence/.
set -e
cd "$(dirname "$0")"
echo "== prerequisites stress test (C1 classification, lifetime lemmas, retreat, dichotomy, inverse rule), n<=36"
python3 check_prereqs.py 36 | tail -1
echo "== exhaustive D_B(T_{k-1}+3), k=3..13 (n<=81), backward layering, sizes summed against p(n)"
python3 exhaustive_r3.py 3 13
if [ "$1" = "full" ]; then
  echo "== exhaustive k=14 (n=94, 92,669,720 partitions)"
  python3 exhaustive_r3.py 14 14
fi
echo "== lower-bound family, actual moves vs modular description, k=9..120"
python3 lower_family_r3.py 9 120 | tail -3
echo "== symbolic claims of the upper-bound proof, k=9..40; Lemmas D/D2 on all partitions n<=26"
python3 verify_claims_r3.py 9 40 26 | tail -2
echo "== entry-state table (h, delta) for k=9..11"
python3 entry_states_r3.py 9 11 | grep -v generic-ok | grep -c "closed\|IMPOSSIBLE"
echo "== independent audit of reused C5 (r=2) claims"
python3 audit_c5_r2.py 30 | tail -2
echo "== exhaustive D_B(n) for n=51..70 (all residues), backward layering"
python3 exhaustive_general.py $(seq 51 70) | awk '{print $1,$2,$3,$5,$6,$7}'
echo "== certificate checker calibration on r=3 (must close k>=10) and Theorem C samples r=4 k=12..16"
python3 toolkit_general_r.py 3 10 16 | grep -c "UNCLASS" | xargs -I{} sh -c 'test {} -eq 0 && echo "r=3 k=10..16: all closed"'
python3 toolkit_general_r.py 4 12 16 | grep -c "UNCLASS" | xargs -I{} sh -c 'test {} -eq 0 && echo "r=4 k=12..16: all closed (Theorem C sample)"'
python3 lower_family_general.py 4 11 40
echo "== conjectural Lemmas D'', O, O3 on all partitions n<=30"
python3 lemma_conjectures_test.py 30 | tail -2
if [ "$1" = "full" ]; then
  echo "== full certificate sweep r=4..8 (about 18 minutes) and with Lemma D'' (2 minutes)"
  for r in 4 5 6 7 8; do python3 toolkit_general_r.py $r $((2*r+3)) 30 | grep -c UNCLASS; done
  for r in 4 5 6 7 8; do python3 toolkit_general_r.py $r $((2*r+3)) 40 dprime | grep -c UNCLASS; done
fi
echo "ALL REPLAYS PASSED"
