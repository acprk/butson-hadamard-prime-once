#!/bin/sh
# Theorem E2, case (m,h) = (21,21): which 7-subsets T of Z_21 carry a weighing B: T -> mu_42 with B B^* = 7?
# Mode "reps": the 22 support classes (up to translation and multiplier) that pass the
#              "no difference occurs exactly once" filter (supports.py).
# Mode "all":  all 1303 such supports containing 0, without multiplier reduction (supports_all.py).
# Each support is searched exhaustively by wexact (exact arithmetic in Z[zeta_42]).
# usage: sh run_wexact.sh reps|all     (run from this directory; needs python3 and a C compiler)
set -e
cd "$(dirname "$0")"
cc -O2 -o wexact wexact.c -lm
mode=${1:-reps}
if [ "$mode" = reps ]; then python3 supports.py 21 7 | tail -n +2 | tr -d '(),'; else python3 supports_all.py; fi |
while read -r T; do
  printf '%s : %s\n' "$T" "$(PRINTMAX=0 ./wexact 21 42 $T 2>/dev/null)"
done
