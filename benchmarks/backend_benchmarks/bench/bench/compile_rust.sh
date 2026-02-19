#!/bin/bash
# Compile Rust benchmarks to native and WASM targets
#
# Prerequisites:
#   - rustc and cargo installed
#   - wasm32-unknown-unknown target: rustup target add wasm32-unknown-unknown
#   - wasmtime for running WASM
#
# Usage: ./compile_rust.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TARGETS_DIR="$SCRIPT_DIR/targets"
RUST_DIR="$TARGETS_DIR/rust"
AST_DIR="$SCRIPT_DIR/../_build/default"

echo "=== Compiling Rust Benchmarks ==="

# Check prerequisites
command -v peregrine >/dev/null || { echo "Error: peregrine not found. Run: eval \$(opam env)"; exit 1; }
command -v cargo >/dev/null || { echo "Error: cargo not found"; exit 1; }

mkdir -p "$RUST_DIR/src" "$RUST_DIR/wasm"

BENCHMARKS=("binary_trees_10" "binary_trees_14" "pidigits_27" "pidigits_100")

# Generate Rust source files from typed ASTs
echo ""
echo "Step 1: Generating Rust source files..."

for bench in "${BENCHMARKS[@]}"; do
    tast="$AST_DIR/${bench}.tast"
    rs="$RUST_DIR/src/${bench}.rs"

    if [[ ! -f "$tast" ]]; then
        echo "  $bench: .tast not found (run: dune build theories/RustExtract.vo)"
        continue
    fi

    echo -n "  $bench: "
    if peregrine rust "$tast" -o "$rs" 2>/dev/null; then
        # Fix Rust keyword issues (true/false as enum variants)
        sed -i 's/true(PhantomData/r#true(PhantomData/g' "$rs"
        sed -i 's/false(PhantomData/r#false(PhantomData/g' "$rs"
        sed -i 's/::true(/::r#true(/g' "$rs"
        sed -i 's/::false(/::r#false(/g' "$rs"

        # Make public
        sed -i 's/^struct Program/pub struct Program/' "$rs"
        sed -i 's/^fn new()/pub fn new()/' "$rs"
        sed -i 's/^fn alloc/pub fn alloc/' "$rs"
        sed -i 's/^fn closure/pub fn closure/' "$rs"
        sed -i 's/^fn \([A-Za-z_][A-Za-z0-9_]*\)(/pub fn \1(/' "$rs"

        echo "done"
    else
        echo "FAILED"
    fi
done

# Create main wrappers
echo ""
echo "Step 2: Creating binary wrappers..."

for bench in "${BENCHMARKS[@]}"; do
    rs="$RUST_DIR/src/${bench}.rs"
    [[ -f "$rs" ]] || continue

    main_fn="BenchmarksGame_RustExtract_${bench}"

    cat > "$RUST_DIR/src/${bench}_main.rs" << EOF
#[path = "${bench}.rs"]
mod benchmark;

use std::time::Instant;

fn main() {
    let program = benchmark::Program::new();
    let start = Instant::now();
    let result = program.${main_fn}();
    let elapsed = start.elapsed();
    println!("Result: {:?}", result);
    println!("Time: {:.2} ms", elapsed.as_secs_f64() * 1000.0);
}
EOF
    echo "  ${bench}_main.rs"
done

# Compile to native
echo ""
echo "Step 3: Compiling native binaries..."
cd "$RUST_DIR"
cargo build --release 2>&1 | grep -E "Compiling|Finished|error" || true

mkdir -p bin
for bench in "${BENCHMARKS[@]}"; do
    [[ -f "target/release/$bench" ]] && cp "target/release/$bench" "bin/"
done

echo "Native binaries:"
ls -la bin/ 2>/dev/null | grep -v "\.rs$" || echo "  (none)"

# Compile to WASM
echo ""
echo "Step 4: Compiling WASM..."
cargo build --release --target wasm32-unknown-unknown 2>&1 | grep -E "Compiling|Finished|error" || true

mkdir -p wasm
for bench in "${BENCHMARKS[@]}"; do
    src="target/wasm32-unknown-unknown/release/${bench}.wasm"
    [[ -f "$src" ]] && cp "$src" "wasm/"
done

echo "WASM files:"
ls -la wasm/*.wasm 2>/dev/null || echo "  (none)"

echo ""
echo "=== Rust Compilation Complete ==="
