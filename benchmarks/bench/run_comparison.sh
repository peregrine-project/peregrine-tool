#!/bin/bash
# Run comprehensive benchmark comparison across all backends
#
# Backends tested:
#   - WASM (direct) via Node.js
#   - WASM (CPS) via Node.js
#   - C (direct) compiled with gcc -O3
#   - C (direct) compiled with CompCert
#   - OCaml (Malfunction) native
#
# Usage: ./run_comparison.sh [--small-only]

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TARGETS_DIR="$SCRIPT_DIR/targets"
RESULTS_DIR="$SCRIPT_DIR/results"
CERTICOQ_RUNTIME="${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/CertiCoq/Plugin/runtime"

SMALL_ONLY=false
if [[ "$1" == "--small-only" ]]; then
    SMALL_ONLY=true
fi

mkdir -p "$RESULTS_DIR"

# Benchmarks to run
if $SMALL_ONLY; then
    BENCHMARKS=("binary_trees_10" "fannkuch_7" "pidigits_27")
else
    BENCHMARKS=("binary_trees_10" "binary_trees_14" "fannkuch_7" "fannkuch_8" "pidigits_27" "pidigits_100")
fi

RUNS=3

echo "=============================================="
echo "Peregrine Benchmark Comparison"
echo "=============================================="
echo "Date: $(date)"
echo "Runs per benchmark: $RUNS"
echo "Benchmarks: ${BENCHMARKS[*]}"
echo ""

# Compile C with CompCert (if not already done)
compile_compcert() {
    local cfile="$1"
    local name="$2"
    local outfile="$TARGETS_DIR/c/bin/${name}_compcert"

    if [[ -x "$outfile" ]]; then
        return 0
    fi

    echo "Compiling $name with CompCert..."

    wrapper=$(mktemp --suffix=.c)
    cat > "$wrapper" << 'MAIN_EOF'
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

extern struct thread_info *make_tinfo(void);
extern void *body(struct thread_info *);

int main(int argc, char **argv) {
    struct thread_info *tinfo = make_tinfo();
    clock_t start = clock();
    void *result = body(tinfo);
    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC * 1000.0;
    printf("Result: %p\n", result);
    printf("Time: %.2f ms\n", elapsed);
    return 0;
}
MAIN_EOF

    # CompCert doesn't support all gcc flags, use minimal options
    ccomp -O \
        -I"$CERTICOQ_RUNTIME" \
        -I"$TARGETS_DIR/c/direct" \
        "$cfile" \
        "$wrapper" \
        "$CERTICOQ_RUNTIME/gc_stack.c" \
        "$CERTICOQ_RUNTIME/prim_int63.c" \
        "$CERTICOQ_RUNTIME/prim_floats.c" \
        -lgc \
        -lm \
        -o "$outfile" 2>/dev/null || return 1

    rm -f "$wrapper"
    return 0
}

# Time a native executable (returns milliseconds)
time_native() {
    local exe="$1"
    local total=0

    for ((i=0; i<RUNS; i++)); do
        # Run and extract time from output
        output=$("$exe" 2>&1)
        time_ms=$(echo "$output" | grep "Time:" | awk '{print $2}')
        if [[ -n "$time_ms" ]]; then
            total=$(echo "$total + $time_ms" | bc)
        fi
    done

    echo "scale=2; $total / $RUNS" | bc
}

# Time a WASM file (returns milliseconds)
time_wasm() {
    local wasmfile="$1"
    local total=0

    for ((i=0; i<RUNS; i++)); do
        time_ms=$(node -e "
const fs = require('fs');
const bytes = fs.readFileSync('$wasmfile');
const importObject = { env: { write_char: () => {}, write_int: () => {} } };
WebAssembly.instantiate(bytes, importObject).then(({instance}) => {
    const start = Date.now();
    instance.exports.main_function();
    console.log(Date.now() - start);
});
" 2>/dev/null)
        if [[ -n "$time_ms" ]]; then
            total=$(echo "$total + $time_ms" | bc)
        fi
    done

    echo "scale=2; $total / $RUNS" | bc
}

# Results array
declare -A RESULTS

echo "Running benchmarks..."
echo ""

for bench in "${BENCHMARKS[@]}"; do
    echo "=== $bench ==="

    # WASM Direct
    wasm_direct="$TARGETS_DIR/wasm/direct/${bench}.wasm"
    if [[ -f "$wasm_direct" ]]; then
        time=$(time_wasm "$wasm_direct")
        echo "  WASM (direct):    ${time} ms"
        RESULTS["${bench}_wasm_direct"]=$time
    fi

    # WASM CPS
    wasm_cps="$TARGETS_DIR/wasm/cps/${bench}.wasm"
    if [[ -f "$wasm_cps" ]]; then
        time=$(time_wasm "$wasm_cps")
        echo "  WASM (CPS):       ${time} ms"
        RESULTS["${bench}_wasm_cps"]=$time
    fi

    # C gcc
    c_gcc="$TARGETS_DIR/c/bin/${bench}_direct"
    if [[ -x "$c_gcc" ]]; then
        time=$(time_native "$c_gcc")
        echo "  C (gcc -O3):      ${time} ms"
        RESULTS["${bench}_c_gcc"]=$time
    fi

    # C CompCert
    c_ccomp="$TARGETS_DIR/c/bin/${bench}_compcert"
    cfile="$TARGETS_DIR/c/direct/${bench}.c"
    if [[ ! -x "$c_ccomp" ]] && [[ -f "$cfile" ]]; then
        compile_compcert "$cfile" "$bench"
    fi
    if [[ -x "$c_ccomp" ]]; then
        time=$(time_native "$c_ccomp")
        echo "  C (CompCert):     ${time} ms"
        RESULTS["${bench}_c_compcert"]=$time
    fi

    # OCaml (Malfunction)
    ocaml_exe="$TARGETS_DIR/ocaml/bin/${bench}"
    if [[ -x "$ocaml_exe" ]]; then
        # OCaml executables don't have built-in timing, measure externally
        total=0
        for ((i=0; i<RUNS; i++)); do
            start=$(date +%s%N)
            "$ocaml_exe" >/dev/null 2>&1
            end=$(date +%s%N)
            elapsed=$(echo "scale=2; ($end - $start) / 1000000" | bc)
            total=$(echo "$total + $elapsed" | bc)
        done
        time=$(echo "scale=2; $total / $RUNS" | bc)
        echo "  OCaml (native):   ${time} ms"
        RESULTS["${bench}_ocaml"]=$time
    fi

    echo ""
done

# Generate results table
echo "=============================================="
echo "Results Summary (milliseconds, lower is better)"
echo "=============================================="
echo ""

printf "%-20s %12s %12s %12s %12s %12s\n" "Benchmark" "WASM/direct" "WASM/CPS" "C/gcc" "C/CompCert" "OCaml"
printf "%-20s %12s %12s %12s %12s %12s\n" "--------------------" "------------" "------------" "------------" "------------" "------------"

for bench in "${BENCHMARKS[@]}"; do
    wd="${RESULTS[${bench}_wasm_direct]:-N/A}"
    wc="${RESULTS[${bench}_wasm_cps]:-N/A}"
    cg="${RESULTS[${bench}_c_gcc]:-N/A}"
    cc="${RESULTS[${bench}_c_compcert]:-N/A}"
    oc="${RESULTS[${bench}_ocaml]:-N/A}"
    printf "%-20s %12s %12s %12s %12s %12s\n" "$bench" "$wd" "$wc" "$cg" "$cc" "$oc"
done

echo ""
echo "Note: WASM/direct may stack overflow on larger inputs"
echo ""

# Save to file
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTFILE="$RESULTS_DIR/comparison_${TIMESTAMP}.txt"

{
    echo "Peregrine Benchmark Comparison"
    echo "Date: $(date)"
    echo ""
    printf "%-20s %12s %12s %12s %12s %12s\n" "Benchmark" "WASM/direct" "WASM/CPS" "C/gcc" "C/CompCert" "OCaml"
    for bench in "${BENCHMARKS[@]}"; do
        wd="${RESULTS[${bench}_wasm_direct]:-N/A}"
        wc="${RESULTS[${bench}_wasm_cps]:-N/A}"
        cg="${RESULTS[${bench}_c_gcc]:-N/A}"
        cc="${RESULTS[${bench}_c_compcert]:-N/A}"
        oc="${RESULTS[${bench}_ocaml]:-N/A}"
        printf "%-20s %12s %12s %12s %12s %12s\n" "$bench" "$wd" "$wc" "$cg" "$cc" "$oc"
    done
} > "$OUTFILE"

echo "Results saved to: $OUTFILE"
