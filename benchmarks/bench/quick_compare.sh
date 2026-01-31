#!/bin/bash
# Quick benchmark comparison (without CompCert)
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TARGETS_DIR="$SCRIPT_DIR/targets"
RUNS=3

echo "=============================================="
echo "Peregrine Quick Benchmark Comparison"
echo "=============================================="
echo ""

# Small benchmarks only
BENCHMARKS=("binary_trees_10" "binary_trees_14" "fannkuch_7" "fannkuch_8" "pidigits_27" "pidigits_100")

time_wasm() {
    local f="$1"
    node -e "
const fs = require('fs');
const bytes = fs.readFileSync('$f');
const io = { env: { write_char: () => {}, write_int: () => {} } };
(async () => {
    const times = [];
    for (let i = 0; i < $RUNS; i++) {
        const { instance } = await WebAssembly.instantiate(bytes, io);
        const start = Date.now();
        try { instance.exports.main_function(); } catch(e) { console.log('ERR'); return; }
        times.push(Date.now() - start);
    }
    const avg = times.reduce((a,b) => a+b) / times.length;
    console.log(avg.toFixed(1));
})();
" 2>/dev/null
}

time_native() {
    local exe="$1"
    local total=0
    for ((i=0; i<RUNS; i++)); do
        t=$("$exe" 2>&1 | grep "Time:" | awk '{print $2}')
        [[ -n "$t" ]] && total=$(echo "$total + $t" | bc)
    done
    echo "scale=1; $total / $RUNS" | bc
}

time_ocaml() {
    local exe="$1"
    local total=0
    for ((i=0; i<RUNS; i++)); do
        start=$(date +%s%N)
        "$exe" >/dev/null 2>&1 || true
        end=$(date +%s%N)
        ms=$(echo "scale=1; ($end - $start) / 1000000" | bc)
        total=$(echo "$total + $ms" | bc)
    done
    echo "scale=1; $total / $RUNS" | bc
}

printf "%-18s %10s %10s %10s %10s\n" "Benchmark" "WASM/dir" "WASM/cps" "C/gcc" "OCaml"
printf "%-18s %10s %10s %10s %10s\n" "------------------" "----------" "----------" "----------" "----------"

for bench in "${BENCHMARKS[@]}"; do
    wd=$(time_wasm "$TARGETS_DIR/wasm/direct/${bench}.wasm" 2>/dev/null || echo "N/A")
    wc=$(time_wasm "$TARGETS_DIR/wasm/cps/${bench}.wasm" 2>/dev/null || echo "N/A")
    cg=$([[ -x "$TARGETS_DIR/c/bin/${bench}_direct" ]] && time_native "$TARGETS_DIR/c/bin/${bench}_direct" || echo "N/A")
    oc=$([[ -x "$TARGETS_DIR/ocaml/bin/${bench}" ]] && time_ocaml "$TARGETS_DIR/ocaml/bin/${bench}" || echo "N/A")
    printf "%-18s %10s %10s %10s %10s\n" "$bench" "$wd" "$wc" "$cg" "$oc"
done

echo ""
echo "Times in milliseconds (average of $RUNS runs)"
echo "ERR = stack overflow or runtime error"
