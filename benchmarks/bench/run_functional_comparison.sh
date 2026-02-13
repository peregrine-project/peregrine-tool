#!/bin/bash
# Comprehensive comparison of functional benchmarks across:
#   - Peregrine C/GCC (extracted from Rocq)
#   - Peregrine OCaml/Malfunction (extracted from Rocq)
#   - Lean 4 native (hand-written)
#   - OCaml native (hand-written)
#
# Usage: ./run_functional_comparison.sh [--compile-only] [--run-only]

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BENCH_ROOT="$SCRIPT_DIR/.."
AST_DIR="$BENCH_ROOT"
TARGETS_DIR="$SCRIPT_DIR/targets"
RESULTS_DIR="$SCRIPT_DIR/results"
LEAN_DIR="$TARGETS_DIR/lean"
OCAML_NATIVE_DIR="$TARGETS_DIR/ocaml_native"

# CertiCoq runtime for C compilation
CERTICOQ_RUNTIME="${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/CertiCoq/Plugin/runtime"

COMPILE_ONLY=false
RUN_ONLY=false

for arg in "$@"; do
    case $arg in
        --compile-only) COMPILE_ONLY=true ;;
        --run-only) RUN_ONLY=true ;;
    esac
done

# Functional benchmarks (new ones)
FUNCTIONAL_BENCHMARKS=(
    "nqueens_8:8"
    "nqueens_10:10"
    "ackermann_3_9:3 9"
    "ackermann_3_10:3 10"
    "tak_18_12_6:18 12 6"
    "tak_21_14_7:21 14 7"
    "quicksort_1000:1000"
    "sieve_1000:1000"
    "sieve_5000:5000"
    "treesort_1000:1000"
    "symbdiff_20:20"
    "symbdiff_50:50"
    "lambda_fact_10:10"
)

# Map benchmark names to Lean/OCaml executables
declare -A LEAN_NAMES=(
    ["nqueens_8"]="nqueens"
    ["nqueens_10"]="nqueens"
    ["ackermann_3_9"]="ackermann"
    ["ackermann_3_10"]="ackermann"
    ["tak_18_12_6"]="tak"
    ["tak_21_14_7"]="tak"
    ["quicksort_1000"]="quicksort"
    ["sieve_1000"]="sieve"
    ["sieve_5000"]="sieve"
    ["treesort_1000"]="treesort"
    ["symbdiff_20"]="symbolic_diff"
    ["symbdiff_50"]="symbolic_diff"
    ["lambda_fact_10"]="lambda_interp"
)

declare -A OCAML_NAMES=(
    ["nqueens_8"]="nqueens"
    ["nqueens_10"]="nqueens"
    ["ackermann_3_9"]="ackermann"
    ["ackermann_3_10"]="ackermann"
    ["tak_18_12_6"]="tak"
    ["tak_21_14_7"]="tak"
    ["quicksort_1000"]="quicksort"
    ["sieve_1000"]="sieve"
    ["sieve_5000"]="sieve"
    ["treesort_1000"]="treesort"
    ["symbdiff_20"]="symbolic_diff"
    ["symbdiff_50"]="symbolic_diff"
    ["lambda_fact_10"]="lambda_interp"
)

RUNS=5
WARMUP=1

mkdir -p "$RESULTS_DIR"
mkdir -p "$TARGETS_DIR/c/direct"
mkdir -p "$TARGETS_DIR/c/bin"

echo "=============================================="
echo "Functional Benchmark Comparison"
echo "=============================================="
echo "Date: $(date)"
echo "Runs per benchmark: $RUNS (warmup: $WARMUP)"
echo ""

# =============================================================================
# COMPILATION PHASE
# =============================================================================

compile_all() {
    echo "=== Compilation Phase ==="
    echo ""

    # Check for peregrine
    if ! command -v peregrine &> /dev/null; then
        echo "Error: peregrine not found. Run: eval \$(opam env --switch=rocq-9)"
        exit 1
    fi

    # Compile AST to C
    echo "--- Compiling Peregrine AST to C ---"
    for entry in "${FUNCTIONAL_BENCHMARKS[@]}"; do
        bench="${entry%%:*}"
        ast="$AST_DIR/${bench}.ast"
        cout="$TARGETS_DIR/c/direct/${bench}.c"

        if [[ -f "$ast" ]]; then
            if [[ ! -f "$cout" ]] || [[ "$ast" -nt "$cout" ]]; then
                echo "  Compiling $bench.ast -> C"
                peregrine c "$ast" -o "$cout" 2>/dev/null || echo "    [FAILED]"
            else
                echo "  $bench.c (up to date)"
            fi
        else
            echo "  $bench.ast not found, skipping"
        fi
    done
    echo ""

    # Compile C to native binaries
    echo "--- Compiling C to native binaries (gcc -O3) ---"

    # Create a main wrapper for timing
    MAIN_WRAPPER=$(mktemp --suffix=.c)
    cat > "$MAIN_WRAPPER" << 'MAIN_EOF'
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/time.h>

extern struct thread_info *make_tinfo(void);
extern void *body(struct thread_info *);

double get_time_ms() {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000.0 + tv.tv_usec / 1000.0;
}

int main(int argc, char **argv) {
    struct thread_info *tinfo = make_tinfo();
    double start = get_time_ms();
    void *result = body(tinfo);
    double elapsed = get_time_ms() - start;
    printf("Result: %p\n", result);
    printf("Time: %.2f ms\n", elapsed);
    return 0;
}
MAIN_EOF

    for entry in "${FUNCTIONAL_BENCHMARKS[@]}"; do
        bench="${entry%%:*}"
        cfile="$TARGETS_DIR/c/direct/${bench}.c"
        binfile="$TARGETS_DIR/c/bin/${bench}"

        if [[ -f "$cfile" ]]; then
            if [[ ! -x "$binfile" ]] || [[ "$cfile" -nt "$binfile" ]]; then
                echo "  Compiling $bench -> native"
                gcc -O3 -w \
                    -I"$CERTICOQ_RUNTIME" \
                    "$cfile" \
                    "$MAIN_WRAPPER" \
                    "$CERTICOQ_RUNTIME/gc_stack.c" \
                    "$CERTICOQ_RUNTIME/prim_int63.c" \
                    "$CERTICOQ_RUNTIME/prim_floats.c" \
                    -lgc -lm \
                    -o "$binfile" 2>/dev/null || echo "    [FAILED]"
            else
                echo "  $bench (up to date)"
            fi
        fi
    done
    rm -f "$MAIN_WRAPPER"
    echo ""

    # Build Lean benchmarks
    echo "--- Building Lean benchmarks ---"
    (cd "$LEAN_DIR" && lake build 2>&1 | grep -E "(Built|Error)" | head -20) || true
    echo ""

    # Build OCaml benchmarks
    echo "--- Building OCaml benchmarks ---"
    (cd "$OCAML_NATIVE_DIR" && \
     for f in nqueens ackermann tak quicksort sieve treesort symbolic_diff lambda_interp; do
         if [[ -f "${f}.ml" ]]; then
             if [[ ! -x "$f" ]] || [[ "${f}.ml" -nt "$f" ]]; then
                 echo "  Compiling ${f}.ml"
                 ocamlfind ocamlopt -package unix -linkpkg "${f}.ml" -o "$f" 2>/dev/null || echo "    [FAILED]"
             fi
         fi
     done)
    echo ""
}

# =============================================================================
# BENCHMARK EXECUTION
# =============================================================================

# Time a native executable with internal timing
time_native_internal() {
    local exe="$1"
    shift
    local args="$@"
    local times=()

    # Warmup
    for ((i=0; i<WARMUP; i++)); do
        "$exe" $args >/dev/null 2>&1 || true
    done

    # Actual runs
    for ((i=0; i<RUNS; i++)); do
        output=$("$exe" $args 2>&1) || true
        time_ms=$(echo "$output" | grep -i "Time:" | awk '{print $2}')
        if [[ -n "$time_ms" ]]; then
            times+=("$time_ms")
        fi
    done

    # Calculate average
    if [[ ${#times[@]} -gt 0 ]]; then
        total=0
        for t in "${times[@]}"; do
            total=$(echo "$total + $t" | bc)
        done
        echo "scale=2; $total / ${#times[@]}" | bc
    else
        echo "N/A"
    fi
}

# Time a native executable with external timing (for executables without internal timing)
time_native_external() {
    local exe="$1"
    shift
    local args="$@"
    local times=()

    # Warmup
    for ((i=0; i<WARMUP; i++)); do
        "$exe" $args >/dev/null 2>&1 || true
    done

    # Actual runs
    for ((i=0; i<RUNS; i++)); do
        start=$(date +%s%N)
        "$exe" $args >/dev/null 2>&1 || true
        end=$(date +%s%N)
        elapsed=$(echo "scale=2; ($end - $start) / 1000000" | bc)
        times+=("$elapsed")
    done

    # Calculate average
    if [[ ${#times[@]} -gt 0 ]]; then
        total=0
        for t in "${times[@]}"; do
            total=$(echo "$total + $t" | bc)
        done
        echo "scale=2; $total / ${#times[@]}" | bc
    else
        echo "N/A"
    fi
}

run_benchmarks() {
    echo "=== Benchmark Execution Phase ==="
    echo ""

    # Results storage
    declare -A RESULTS

    for entry in "${FUNCTIONAL_BENCHMARKS[@]}"; do
        bench="${entry%%:*}"
        args="${entry#*:}"

        echo "=== $bench (args: $args) ==="

        # Peregrine C/GCC
        peregrine_bin="$TARGETS_DIR/c/bin/${bench}"
        if [[ -x "$peregrine_bin" ]]; then
            time=$(time_native_internal "$peregrine_bin")
            echo "  Peregrine C/GCC:  ${time} ms"
            RESULTS["${bench}_peregrine_c"]=$time
        else
            echo "  Peregrine C/GCC:  N/A (not compiled)"
            RESULTS["${bench}_peregrine_c"]="N/A"
        fi

        # Lean
        lean_name="${LEAN_NAMES[$bench]}"
        lean_bin="$LEAN_DIR/.lake/build/bin/${lean_name}"
        if [[ -x "$lean_bin" ]]; then
            time=$(time_native_internal "$lean_bin" $args)
            echo "  Lean 4:           ${time} ms"
            RESULTS["${bench}_lean"]=$time
        else
            echo "  Lean 4:           N/A (not compiled)"
            RESULTS["${bench}_lean"]="N/A"
        fi

        # OCaml native
        ocaml_name="${OCAML_NAMES[$bench]}"
        ocaml_bin="$OCAML_NATIVE_DIR/${ocaml_name}"
        if [[ -x "$ocaml_bin" ]]; then
            time=$(time_native_internal "$ocaml_bin" $args)
            echo "  OCaml native:     ${time} ms"
            RESULTS["${bench}_ocaml"]=$time
        else
            echo "  OCaml native:     N/A (not compiled)"
            RESULTS["${bench}_ocaml"]="N/A"
        fi

        echo ""
    done

    # Print results table
    echo "=============================================="
    echo "Results Summary (milliseconds, lower is better)"
    echo "=============================================="
    echo ""
    printf "%-20s %15s %15s %15s\n" "Benchmark" "Peregrine C" "Lean 4" "OCaml"
    printf "%-20s %15s %15s %15s\n" "--------------------" "---------------" "---------------" "---------------"

    for entry in "${FUNCTIONAL_BENCHMARKS[@]}"; do
        bench="${entry%%:*}"
        pc="${RESULTS[${bench}_peregrine_c]:-N/A}"
        ln="${RESULTS[${bench}_lean]:-N/A}"
        oc="${RESULTS[${bench}_ocaml]:-N/A}"
        printf "%-20s %15s %15s %15s\n" "$bench" "$pc" "$ln" "$oc"
    done

    echo ""

    # Save results
    TIMESTAMP=$(date +%Y%m%d_%H%M%S)
    OUTFILE="$RESULTS_DIR/functional_comparison_${TIMESTAMP}.txt"

    {
        echo "Functional Benchmark Comparison"
        echo "Date: $(date)"
        echo "Runs: $RUNS, Warmup: $WARMUP"
        echo ""
        printf "%-20s %15s %15s %15s\n" "Benchmark" "Peregrine C" "Lean 4" "OCaml"
        printf "%-20s %15s %15s %15s\n" "--------------------" "---------------" "---------------" "---------------"
        for entry in "${FUNCTIONAL_BENCHMARKS[@]}"; do
            bench="${entry%%:*}"
            pc="${RESULTS[${bench}_peregrine_c]:-N/A}"
            ln="${RESULTS[${bench}_lean]:-N/A}"
            oc="${RESULTS[${bench}_ocaml]:-N/A}"
            printf "%-20s %15s %15s %15s\n" "$bench" "$pc" "$ln" "$oc"
        done
    } > "$OUTFILE"

    echo "Results saved to: $OUTFILE"
}

# =============================================================================
# MAIN
# =============================================================================

if ! $RUN_ONLY; then
    compile_all
fi

if ! $COMPILE_ONLY; then
    run_benchmarks
fi
