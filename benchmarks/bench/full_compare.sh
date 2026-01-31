#!/bin/bash
# Full benchmark comparison: WASM, C/gcc, C/CompCert, OCaml
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TARGETS_DIR="$SCRIPT_DIR/targets"
RUNS=3

echo "============================================================"
echo "    Peregrine Benchmark Comparison (all backends)"
echo "============================================================"
echo "Date: $(date)"
echo "Runs: $RUNS per benchmark"
echo ""

BENCHMARKS=("binary_trees_10" "binary_trees_14" "binary_trees_16" "fannkuch_7" "fannkuch_8" "fannkuch_9" "pidigits_27" "pidigits_100" "pidigits_500")

time_wasm() {
    local f="$1"
    [[ -f "$f" ]] || { echo "N/A"; return; }
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
    console.log((times.reduce((a,b) => a+b) / times.length).toFixed(1));
})();
" 2>/dev/null
}

time_native() {
    local exe="$1"
    [[ -x "$exe" ]] || { echo "N/A"; return; }
    local total=0
    for ((i=0; i<RUNS; i++)); do
        t=$("$exe" 2>&1 | grep "Time:" | awk '{print $2}')
        [[ -n "$t" ]] && total=$(echo "$total + $t" | bc)
    done
    echo "scale=1; $total / $RUNS" | bc
}

time_ocaml() {
    local exe="$1"
    [[ -x "$exe" ]] || { echo "N/A"; return; }
    local total=0
    for ((i=0; i<RUNS; i++)); do
        start=$(date +%s%N)
        timeout 120 "$exe" >/dev/null 2>&1 || { echo "TIMEOUT"; return; }
        end=$(date +%s%N)
        ms=$(echo "scale=1; ($end - $start) / 1000000" | bc)
        total=$(echo "$total + $ms" | bc)
    done
    echo "scale=1; $total / $RUNS" | bc
}

printf "%-16s %9s %9s %9s %9s %9s\n" "Benchmark" "WASM/dir" "WASM/cps" "C/gcc" "C/ccomp" "OCaml"
printf "%-16s %9s %9s %9s %9s %9s\n" "----------------" "---------" "---------" "---------" "---------" "---------"

for bench in "${BENCHMARKS[@]}"; do
    wd=$(time_wasm "$TARGETS_DIR/wasm/direct/${bench}.wasm")
    wc=$(time_wasm "$TARGETS_DIR/wasm/cps/${bench}.wasm")
    cg=$(time_native "$TARGETS_DIR/c/bin/${bench}_direct")
    cc=$(time_native "$TARGETS_DIR/c/bin/${bench}_compcert")
    oc=$(time_ocaml "$TARGETS_DIR/ocaml/bin/${bench}")
    printf "%-16s %9s %9s %9s %9s %9s\n" "$bench" "$wd" "$wc" "$cg" "$cc" "$oc"
done

echo ""
echo "Times in milliseconds (average of $RUNS runs, lower is better)"
echo "ERR = stack overflow | N/A = not available | TIMEOUT = >120s"
echo ""
echo "Note: WASM/direct uses less stack but may overflow on large inputs"
echo "      WASM/cps uses heap-based CPS, handles larger inputs but slower"
