#!/bin/bash
# Compile C backend benchmarks to native binaries
#
# Usage: ./compile_c.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TARGETS_DIR="$SCRIPT_DIR/targets"
C_DIR="$TARGETS_DIR/c"
BIN_DIR="$TARGETS_DIR/c/bin"

# CertiCoq runtime location
CERTICOQ_RUNTIME="${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/CertiCoq/Plugin/runtime"

if [[ ! -d "$CERTICOQ_RUNTIME" ]]; then
    echo "Error: CertiCoq runtime not found at $CERTICOQ_RUNTIME"
    echo "Make sure CertiCoq is installed and opam env is set"
    exit 1
fi

mkdir -p "$BIN_DIR"

echo "=== Compiling C benchmarks to native binaries ==="
echo "CertiCoq runtime: $CERTICOQ_RUNTIME"
echo ""

# Compile each C file
for pipeline in direct cps; do
    echo "Pipeline: $pipeline"

    for cfile in "$C_DIR/$pipeline"/*.c; do
        [[ -f "$cfile" ]] || continue

        name=$(basename "$cfile" .c)
        hfile="$C_DIR/$pipeline/${name}.h"
        outfile="$BIN_DIR/${name}_${pipeline}"

        echo "  Compiling $name..."

        # Create a main wrapper
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

        # Compile with CertiCoq runtime
        gcc -O3 -w \
            -I"$CERTICOQ_RUNTIME" \
            -I"$C_DIR/$pipeline" \
            "$cfile" \
            "$wrapper" \
            "$CERTICOQ_RUNTIME/gc_stack.o" \
            "$CERTICOQ_RUNTIME/prim_int63.o" \
            "$CERTICOQ_RUNTIME/prim_floats.o" \
            -lgc \
            -lm \
            -o "$outfile" 2>&1 || echo "    [FAILED]"

        rm -f "$wrapper"

        if [[ -x "$outfile" ]]; then
            echo "    -> $outfile"
        fi
    done
    echo ""
done

# Count successful compilations
count=$(find "$BIN_DIR" -type f -executable 2>/dev/null | wc -l)
echo "=== Compiled $count native binaries ==="
