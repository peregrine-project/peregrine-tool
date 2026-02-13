#!/bin/bash
# Compile Lean benchmarks via Peregrine pipeline
# Lean → lean-to-lambdabox → λ□ AST → Peregrine C → GCC → native
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_PEREGRINE="$SCRIPT_DIR/targets/lean_peregrine"
EXTRACTED="$LEAN_PEREGRINE/extracted"
C_DIR="$LEAN_PEREGRINE/c"
BIN_DIR="$LEAN_PEREGRINE/bin"

# CertiCoq runtime location (adjust as needed)
CERTICOQ_RUNTIME="${CERTICOQ_RUNTIME:-$SCRIPT_DIR/../../coq-certicoq/plugin}"

echo "=============================================="
echo "  Lean via Peregrine Compilation"
echo "=============================================="

# Create output directories
mkdir -p "$EXTRACTED" "$C_DIR" "$BIN_DIR"

# Step 1: Build Lean and extract to AST
echo ""
echo "=== Step 1: Building Lean and extracting to λ□ AST ==="
cd "$LEAN_PEREGRINE"
if lake build 2>&1; then
    echo "Lean build successful"
else
    echo "Error: lake build failed. Make sure lean-to-lambdabox is properly installed."
    exit 1
fi

# Check that AST files were generated
if [ ! -d "$EXTRACTED" ] || [ -z "$(ls -A "$EXTRACTED" 2>/dev/null)" ]; then
    echo "Warning: No .ast files found in $EXTRACTED"
    echo "The #erase commands may not have run. Check lean-to-lambdabox installation."
    exit 1
fi

# Step 2: Compile AST files to C using Peregrine
echo ""
echo "=== Step 2: Compiling λ□ AST to C via Peregrine ==="
cd "$SCRIPT_DIR"

for ast in "$EXTRACTED"/*.ast; do
    [ -f "$ast" ] || continue
    name=$(basename "$ast" .ast)
    echo "  Compiling $name.ast → $name.c"
    peregrine c "$ast" -o "$C_DIR/$name.c" 2>&1 || {
        echo "    Warning: Failed to compile $ast"
        continue
    }
done

# Step 3: Compile C to native binaries
echo ""
echo "=== Step 3: Compiling C to native binaries ==="

# Check for CertiCoq runtime
if [ ! -f "$CERTICOQ_RUNTIME/gc_stack.c" ]; then
    echo "Warning: CertiCoq runtime not found at $CERTICOQ_RUNTIME"
    echo "Set CERTICOQ_RUNTIME environment variable or adjust script"
    echo "Trying to compile without runtime (may fail)..."
    RUNTIME_FILES=""
    RUNTIME_INCLUDE=""
else
    RUNTIME_FILES="$CERTICOQ_RUNTIME/gc_stack.c"
    RUNTIME_INCLUDE="-I$CERTICOQ_RUNTIME"
fi

for c_file in "$C_DIR"/*.c; do
    [ -f "$c_file" ] || continue
    name=$(basename "$c_file" .c)
    # Skip if it's a header-only file
    [[ "$name" == *"_h" ]] && continue

    echo "  Compiling $name.c → $name"
    gcc -O2 $RUNTIME_INCLUDE "$c_file" $RUNTIME_FILES -o "$BIN_DIR/$name" 2>&1 || {
        echo "    Warning: Failed to compile $c_file"
        continue
    }
done

echo ""
echo "=== Compilation Complete ==="
echo "AST files: $EXTRACTED"
echo "C files:   $C_DIR"
echo "Binaries:  $BIN_DIR"

# List generated binaries
echo ""
echo "Generated binaries:"
ls -la "$BIN_DIR" 2>/dev/null || echo "  (none)"
