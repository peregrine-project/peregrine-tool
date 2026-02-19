#!/bin/bash
# Comprehensive benchmark comparison: Native languages vs Peregrine targets
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_DIR="$SCRIPT_DIR"
TARGETS="$BENCH_DIR/targets"
RUNS=3

echo "=================================================================="
echo "    Comprehensive Benchmark Comparison"
echo "    Native Languages vs Peregrine Compilation Targets"
echo "=================================================================="
echo "Date: $(date)"
echo ""

time_lean() {
    local exe="$1"
    local arg="$2"
    [[ -x "$exe" ]] || { echo "N/A"; return; }
    "$exe" "$arg" 2>&1 | grep "Time:" | sed 's/Time: //' | sed 's/ ms//'
}

time_ocaml_native() {
    local exe="$1"
    local arg="$2"
    [[ -x "$exe" ]] || { echo "N/A"; return; }
    "$exe" "$arg" 2>&1 | grep "Time:" | sed 's/Time: //' | sed 's/ ms//'
}

time_peregrine_native() {
    local exe="$1"
    [[ -x "$exe" ]] || { echo "N/A"; return; }
    local total=0
    for ((i=0; i<RUNS; i++)); do
        t=$("$exe" 2>&1 | grep "Time:" | awk '{print $2}')
        [[ -n "$t" ]] && total=$(echo "$total + $t" | bc)
    done
    echo "scale=1; $total / $RUNS" | bc
}

time_wasm() {
    local f="$1"
    [[ -f "$f" ]] || { echo "N/A"; return; }
    node -e "
const fs = require('fs');
const b = fs.readFileSync('$f');
WebAssembly.instantiate(b, {env:{write_char:()=>{},write_int:()=>{}}}).then(({instance})=>{
    const times = [];
    for (let i = 0; i < $RUNS; i++) {
        const s = Date.now();
        try { instance.exports.main_function(); } catch(e) { console.log('ERR'); return; }
        times.push(Date.now() - s);
    }
    console.log((times.reduce((a,b)=>a+b)/times.length).toFixed(1));
});
" 2>/dev/null
}

echo "=== Binary Trees Comparison ==="
echo ""
printf "%-10s %10s %10s %10s %10s %10s %10s %10s\n" \
    "Input" "Lean" "OCaml" "P:WASM/d" "P:WASM/c" "P:C/gcc" "P:OCaml" "P:Rust"
printf "%-10s %10s %10s %10s %10s %10s %10s %10s\n" \
    "----------" "----------" "----------" "----------" "----------" "----------" "----------" "----------"

for n in 10 14; do
    lean=$(time_lean "$TARGETS/lean/.lake/build/bin/binary_trees" "$n")
    ocaml=$(time_ocaml_native "$TARGETS/ocaml_native/binary_trees" "$n")
    p_wasm_d=$(time_wasm "$TARGETS/wasm/direct/binary_trees_${n}.wasm")
    p_wasm_c=$(time_wasm "$TARGETS/wasm/cps/binary_trees_${n}.wasm")
    p_c=$(time_peregrine_native "$TARGETS/c/bin/binary_trees_${n}_direct")
    p_ocaml=$(time_peregrine_native "$TARGETS/ocaml/bin/binary_trees_${n}" 2>/dev/null || echo "N/A")
    p_rust=$(time_peregrine_native "$TARGETS/rust/bin/binary_trees_${n}")
    printf "%-10s %10s %10s %10s %10s %10s %10s %10s\n" \
        "N=$n" "$lean" "$ocaml" "$p_wasm_d" "$p_wasm_c" "$p_c" "$p_ocaml" "$p_rust"
done

echo ""
echo "=== Fannkuch Comparison ==="
echo ""
printf "%-10s %10s %10s %10s %10s %10s %10s\n" \
    "Input" "Lean" "OCaml" "P:WASM/d" "P:WASM/c" "P:C/gcc" "P:OCaml"
printf "%-10s %10s %10s %10s %10s %10s %10s\n" \
    "----------" "----------" "----------" "----------" "----------" "----------" "----------"

for n in 7 8; do
    lean=$(time_lean "$TARGETS/lean/.lake/build/bin/fannkuch" "$n")
    ocaml=$(time_ocaml_native "$TARGETS/ocaml_native/fannkuch" "$n")
    p_wasm_d=$(time_wasm "$TARGETS/wasm/direct/fannkuch_${n}.wasm")
    p_wasm_c=$(time_wasm "$TARGETS/wasm/cps/fannkuch_${n}.wasm")
    p_c=$(time_peregrine_native "$TARGETS/c/bin/fannkuch_${n}_direct")
    p_ocaml=$(time_peregrine_native "$TARGETS/ocaml/bin/fannkuch_${n}" 2>/dev/null || echo "N/A")
    printf "%-10s %10s %10s %10s %10s %10s %10s\n" \
        "N=$n" "$lean" "$ocaml" "$p_wasm_d" "$p_wasm_c" "$p_c" "$p_ocaml"
done

echo ""
echo "=== Pidigits Comparison ==="
echo ""
printf "%-10s %10s %10s %10s %10s %10s %10s %10s\n" \
    "Input" "Lean" "OCaml" "P:WASM/d" "P:WASM/c" "P:C/gcc" "P:OCaml" "P:Rust"
printf "%-10s %10s %10s %10s %10s %10s %10s %10s\n" \
    "----------" "----------" "----------" "----------" "----------" "----------" "----------" "----------"

for n in 27 100; do
    lean=$(time_lean "$TARGETS/lean/.lake/build/bin/pidigits" "$n")
    ocaml=$(time_ocaml_native "$TARGETS/ocaml_native/pidigits" "$n")
    p_wasm_d=$(time_wasm "$TARGETS/wasm/direct/pidigits_${n}.wasm")
    p_wasm_c=$(time_wasm "$TARGETS/wasm/cps/pidigits_${n}.wasm")
    p_c=$(time_peregrine_native "$TARGETS/c/bin/pidigits_${n}_direct")
    p_ocaml=$(time_peregrine_native "$TARGETS/ocaml/bin/pidigits_${n}" 2>/dev/null || echo "N/A")
    p_rust=$(time_peregrine_native "$TARGETS/rust/bin/pidigits_${n}")
    printf "%-10s %10s %10s %10s %10s %10s %10s %10s\n" \
        "N=$n" "$lean" "$ocaml" "$p_wasm_d" "$p_wasm_c" "$p_c" "$p_ocaml" "$p_rust"
done

echo ""
echo "Legend:"
echo "  Lean    = Native Lean 4"
echo "  OCaml   = Native OCaml (ocamlopt)"
echo "  P:*     = Peregrine-compiled Rocq"
echo ""
echo "Times in milliseconds (lower is better)"
echo "N/A = not available, ERR = error"
