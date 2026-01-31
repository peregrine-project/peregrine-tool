#!/bin/bash
# Compile all benchmark AST files to various backends with different pipeline options
#
# Backends: wasm, c, rust, ocaml
# Pipelines: direct (default), cps, direct+opt, cps+opt
#
# Usage: ./compile_all.sh [ast_dir]

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BENCH_DIR="$SCRIPT_DIR"
AST_DIR="${1:-$SCRIPT_DIR/../_build/default}"
TARGETS_DIR="$BENCH_DIR/targets"

# Check if peregrine is available
if ! command -v peregrine &> /dev/null; then
    echo "Error: peregrine not found in PATH"
    echo "Try: eval \$(opam env)"
    exit 1
fi

echo "=== Peregrine Benchmark Compilation ==="
echo "AST source: $AST_DIR"
echo "Targets:    $TARGETS_DIR"
echo ""

# Create target directories
mkdir -p "$TARGETS_DIR"/{wasm,c,rust,ocaml}/{direct,cps,direct_opt,cps_opt}

# List of benchmarks (without .ast extension)
BENCHMARKS=(
    "binary_trees_10"
    "binary_trees_14"
    "binary_trees_16"
    "fannkuch_7"
    "fannkuch_8"
    "fannkuch_9"
    "pidigits_27"
    "pidigits_100"
    "pidigits_500"
)

compile_wasm() {
    local ast="$1"
    local name="$2"
    local pipeline="$3"
    local flags="$4"
    local out="$TARGETS_DIR/wasm/$pipeline/${name}.wasm"

    echo "  wasm/$pipeline/$name.wasm"
    peregrine wasm "$ast" -o "$out" $flags 2>/dev/null || echo "    [FAILED]"
}

compile_c() {
    local ast="$1"
    local name="$2"
    local pipeline="$3"
    local flags="$4"
    local out="$TARGETS_DIR/c/$pipeline/${name}.c"

    echo "  c/$pipeline/$name.c"
    peregrine c "$ast" -o "$out" $flags 2>/dev/null || echo "    [FAILED]"
}

# Note: Rust and OCaml require typed extraction, which may not work for all benchmarks

echo "=== Compiling benchmarks ==="

for bench in "${BENCHMARKS[@]}"; do
    ast="$AST_DIR/${bench}.ast"

    if [[ ! -f "$ast" ]]; then
        echo "Skipping $bench (AST not found)"
        continue
    fi

    echo ""
    echo "[$bench]"

    # WASM backend
    compile_wasm "$ast" "$bench" "direct" ""
    compile_wasm "$ast" "$bench" "cps" "--cps"

    # C backend
    compile_c "$ast" "$bench" "direct" ""
    compile_c "$ast" "$bench" "cps" "--cps"
done

# Count successful compilations
wasm_count=$(find "$TARGETS_DIR/wasm" -name "*.wasm" 2>/dev/null | wc -l)
c_count=$(find "$TARGETS_DIR/c" -name "*.c" 2>/dev/null | wc -l)

echo ""
echo "=== Compilation Summary ==="
echo "WASM files: $wasm_count"
echo "C files:    $c_count"
echo ""
echo "To compile C to native binaries, run:"
echo "  cd $TARGETS_DIR/c/direct && for f in *.c; do gcc -O3 -o \${f%.c} \$f -lgc; done"
