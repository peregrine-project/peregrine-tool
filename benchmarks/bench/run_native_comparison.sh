#!/bin/bash
# Compare Lean and OCaml native benchmarks

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARGETS_DIR="$SCRIPT_DIR/targets"
LEAN_BIN="$TARGETS_DIR/lean/.lake/build/bin"
OCAML_BIN="$TARGETS_DIR/ocaml_native"

echo "============================================================"
echo "    Native Language Benchmark Comparison"
echo "============================================================"
echo ""

run_bench() {
    local name="$1"
    local lean_exe="$2"
    local ocaml_exe="$3"
    local arg="$4"

    echo "=== $name (N=$arg) ==="
    echo -n "Lean:   "
    "$LEAN_BIN/$lean_exe" "$arg" 2>&1 | grep "Time:"
    echo -n "OCaml:  "
    "$OCAML_BIN/$ocaml_exe" "$arg" 2>&1 | grep "Time:"
    echo ""
}

run_bench "Binary Trees" binary_trees binary_trees 10
run_bench "Binary Trees" binary_trees binary_trees 14
run_bench "Fannkuch" fannkuch fannkuch 7
run_bench "Fannkuch" fannkuch fannkuch 8
run_bench "Pidigits" pidigits pidigits 27
run_bench "Pidigits" pidigits pidigits 100
