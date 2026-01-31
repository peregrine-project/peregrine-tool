#!/bin/bash
# Compile OCaml (Malfunction) backend benchmarks
#
# Usage: ./compile_ocaml.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TARGETS_DIR="$SCRIPT_DIR/targets"
AST_DIR="$SCRIPT_DIR/../_build/default"
MLF_DIR="$TARGETS_DIR/ocaml"
BIN_DIR="$TARGETS_DIR/ocaml/bin"

# Check if peregrine and malfunction are available
if ! command -v peregrine &> /dev/null; then
    echo "Error: peregrine not found. Run: eval \$(opam env)"
    exit 1
fi

if ! command -v malfunction &> /dev/null; then
    echo "Error: malfunction not found. Run: opam install malfunction"
    exit 1
fi

mkdir -p "$MLF_DIR" "$BIN_DIR"

echo "=== Compiling OCaml (Malfunction) benchmarks ==="

BENCHMARKS=(
    "binary_trees_10"
    "binary_trees_14"
    "fannkuch_7"
    "fannkuch_8"
    "pidigits_27"
    "pidigits_100"
)

for bench in "${BENCHMARKS[@]}"; do
    ast="$AST_DIR/${bench}.ast"
    mlf="$MLF_DIR/${bench}.mlf"
    exe="$BIN_DIR/${bench}"

    if [[ ! -f "$ast" ]]; then
        echo "Skipping $bench (AST not found)"
        continue
    fi

    echo "[$bench]"

    # Generate Malfunction code
    echo "  Generating .mlf..."
    peregrine ocaml "$ast" -o "$mlf" 2>/dev/null

    if [[ ! -f "$mlf" ]]; then
        echo "  [FAILED to generate mlf]"
        continue
    fi

    # Compile with malfunction
    echo "  Compiling to native..."
    if malfunction compile "$mlf" -o "$exe" 2>&1; then
        echo "  -> $exe"
    else
        echo "  [FAILED to compile]"
    fi
done

# Count successful compilations
count=$(find "$BIN_DIR" -type f -executable 2>/dev/null | wc -l)
echo ""
echo "=== Compiled $count OCaml native binaries ==="
