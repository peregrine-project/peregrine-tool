#!/usr/bin/env bash
# Regression test: `peregrine ocaml --untyped-dearg` on the
# programs of gen-params.sh, scaled by N, must finish within a time limit
# (the run without the flag must succeed too).  With the earlier `dedup_nat` (two
# recursive calls per element), N = 40 does not finish: inference time
# doubles with every parameter (1.6 s at N = 26, 6 s at N = 28).
#
# Usage: test/perf/dearg-perf.sh [N...]   (default: 10 20 40)
# Environment: PEREGRINE (default: `dune exec peregrine --`), LIMIT (s, default 60).
here=$(cd "$(dirname "$0")" && pwd)
limit=${LIMIT:-60}
if [ -n "$PEREGRINE" ]; then pg=($PEREGRINE); else pg=(dune exec --no-build peregrine --); fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
status=0
for n in ${@:-10 20 40}; do
  "$here/gen-params.sh" "$n" > "$tmp/p$n.ast"
  timeout "$limit" "${pg[@]}" ocaml "$tmp/p$n.ast" -q -o "$tmp/plain$n.mlf" > "$tmp/plain$n.log" 2>&1
  rc=$?
  start=$(date +%s.%N)
  timeout "$limit" "${pg[@]}" ocaml "$tmp/p$n.ast" -q -o "$tmp/dearg$n.mlf" --untyped-dearg > "$tmp/dearg$n.log" 2>&1
  rd=$?
  t=$(awk -v s="$start" -v e="$(date +%s.%N)" 'BEGIN { printf "%.2f", e - s }')
  if [ $rc -ne 0 ]; then
    echo "FAIL N=$n: peregrine without the flag exited with $rc"; status=1
  elif [ $rd -eq 124 ]; then
    echo "FAIL N=$n: --untyped-dearg did not finish within $limit s"; status=1
  elif [ $rd -ne 0 ]; then
    echo "FAIL N=$n: --untyped-dearg exited with $rd: $(tail -c 200 "$tmp/dearg$n.log")"; status=1
  else
    echo "ok   N=$n: --untyped-dearg in $t s"
  fi
done
exit $status
