#!/bin/bash
# Comprehensive benchmark comparison including Lean via Peregrine
# Compares: Native Lean, Lean via Peregrine, Rocq via Peregrine
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARGETS="$SCRIPT_DIR/targets"
RUNS=3

echo "=================================================================="
echo "    Full Benchmark Comparison"
echo "    Native Lean vs Lean/Peregrine vs Rocq/Peregrine"
echo "=================================================================="
echo "Date: $(date)"
echo ""

# Helper functions
time_native() {
    local exe="$1"
    shift
    [[ -x "$exe" ]] || { echo "N/A"; return; }
    "$exe" "$@" 2>&1 | grep "Time:" | sed 's/Time: //' | sed 's/ ms//'
}

time_peregrine_native() {
    local exe="$1"
    [[ -x "$exe" ]] || { echo "N/A"; return; }
    local total=0
    local count=0
    for ((i=0; i<RUNS; i++)); do
        t=$("$exe" 2>&1 | grep "Time:" | awk '{print $2}')
        if [[ -n "$t" ]]; then
            total=$(echo "$total + $t" | bc)
            ((count++))
        fi
    done
    if [[ $count -gt 0 ]]; then
        echo "scale=1; $total / $count" | bc
    else
        echo "N/A"
    fi
}

echo "=== Ackermann Benchmark ==="
echo ""
printf "%-15s %12s %12s %12s\n" \
    "Input" "Lean Native" "Lean/Pereg" "Rocq/Pereg"
printf "%-15s %12s %12s %12s\n" \
    "---------------" "------------" "------------" "------------"

for args in "3 9" "3 10" "3 11"; do
    m=$(echo $args | cut -d' ' -f1)
    n=$(echo $args | cut -d' ' -f2)
    label="ack($m,$n)"

    lean=$(time_native "$TARGETS/lean/.lake/build/bin/ackermann" $m $n)
    lean_p=$(time_peregrine_native "$TARGETS/lean_peregrine/bin/ackermann_${m}_${n}")
    rocq_p=$(time_peregrine_native "$TARGETS/c/bin/ackermann_${m}_${n}_direct" 2>/dev/null || echo "N/A")

    printf "%-15s %12s %12s %12s\n" "$label" "$lean" "$lean_p" "$rocq_p"
done

echo ""
echo "=== NQueens Benchmark ==="
echo ""
printf "%-15s %12s %12s %12s\n" \
    "Input" "Lean Native" "Lean/Pereg" "Rocq/Pereg"
printf "%-15s %12s %12s %12s\n" \
    "---------------" "------------" "------------" "------------"

for n in 8 10 11; do
    label="nqueens($n)"

    lean=$(time_native "$TARGETS/lean/.lake/build/bin/nqueens" $n)
    lean_p=$(time_peregrine_native "$TARGETS/lean_peregrine/bin/nqueens_${n}")
    rocq_p=$(time_peregrine_native "$TARGETS/c/bin/nqueens_${n}_direct" 2>/dev/null || echo "N/A")

    printf "%-15s %12s %12s %12s\n" "$label" "$lean" "$lean_p" "$rocq_p"
done

echo ""
echo "=== Quicksort Benchmark ==="
echo ""
printf "%-15s %12s %12s %12s\n" \
    "Input" "Lean Native" "Lean/Pereg" "Rocq/Pereg"
printf "%-15s %12s %12s %12s\n" \
    "---------------" "------------" "------------" "------------"

for n in 100 500 1000; do
    label="qsort($n)"

    lean=$(time_native "$TARGETS/lean/.lake/build/bin/quicksort" $n)
    lean_p=$(time_peregrine_native "$TARGETS/lean_peregrine/bin/quicksort_${n}")
    rocq_p=$(time_peregrine_native "$TARGETS/c/bin/quicksort_${n}_direct" 2>/dev/null || echo "N/A")

    printf "%-15s %12s %12s %12s\n" "$label" "$lean" "$lean_p" "$rocq_p"
done

echo ""
echo "=== Binary Trees Benchmark ==="
echo ""
printf "%-15s %12s %12s %12s\n" \
    "Input" "Lean Native" "Lean/Pereg" "Rocq/Pereg"
printf "%-15s %12s %12s %12s\n" \
    "---------------" "------------" "------------" "------------"

for n in 10 14; do
    label="btrees($n)"

    lean=$(time_native "$TARGETS/lean/.lake/build/bin/binary_trees" $n)
    lean_p=$(time_peregrine_native "$TARGETS/lean_peregrine/bin/binary_trees_${n}")
    rocq_p=$(time_peregrine_native "$TARGETS/c/bin/binary_trees_${n}_direct" 2>/dev/null || echo "N/A")

    printf "%-15s %12s %12s %12s\n" "$label" "$lean" "$lean_p" "$rocq_p"
done

echo ""
echo "=== Tak Benchmark ==="
echo ""
printf "%-15s %12s %12s %12s\n" \
    "Input" "Lean Native" "Lean/Pereg" "Rocq/Pereg"
printf "%-15s %12s %12s %12s\n" \
    "---------------" "------------" "------------" "------------"

for args in "18 12 6" "21 14 7" "24 16 8"; do
    x=$(echo $args | cut -d' ' -f1)
    y=$(echo $args | cut -d' ' -f2)
    z=$(echo $args | cut -d' ' -f3)
    label="tak($x,$y,$z)"

    lean=$(time_native "$TARGETS/lean/.lake/build/bin/tak" $x $y $z)
    lean_p=$(time_peregrine_native "$TARGETS/lean_peregrine/bin/tak_${x}_${y}_${z}")
    rocq_p=$(time_peregrine_native "$TARGETS/c/bin/tak_${x}_${y}_${z}_direct" 2>/dev/null || echo "N/A")

    printf "%-15s %12s %12s %12s\n" "$label" "$lean" "$lean_p" "$rocq_p"
done

echo ""
echo "=== Sieve Benchmark ==="
echo ""
printf "%-15s %12s %12s %12s\n" \
    "Input" "Lean Native" "Lean/Pereg" "Rocq/Pereg"
printf "%-15s %12s %12s %12s\n" \
    "---------------" "------------" "------------" "------------"

for n in 1000 5000 10000; do
    label="sieve($n)"

    lean=$(time_native "$TARGETS/lean/.lake/build/bin/sieve" $n)
    lean_p=$(time_peregrine_native "$TARGETS/lean_peregrine/bin/sieve_${n}")
    rocq_p=$(time_peregrine_native "$TARGETS/c/bin/sieve_${n}_direct" 2>/dev/null || echo "N/A")

    printf "%-15s %12s %12s %12s\n" "$label" "$lean" "$lean_p" "$rocq_p"
done

echo ""
echo "=================================================================="
echo "Legend:"
echo "  Lean Native  = Direct Lean 4 compilation (lake build)"
echo "  Lean/Pereg   = Lean → lean-to-lambdabox → Peregrine C → GCC"
echo "  Rocq/Pereg   = Rocq → MetaCoq → Peregrine C → GCC"
echo ""
echo "Times in milliseconds (lower is better)"
echo "N/A = not available or not yet compiled"
echo "=================================================================="
