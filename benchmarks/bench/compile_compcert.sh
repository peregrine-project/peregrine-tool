#!/bin/bash
# Compile C benchmarks with CompCert
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TARGETS_DIR="$SCRIPT_DIR/targets"
C_DIR="$TARGETS_DIR/c/direct"
BIN_DIR="$TARGETS_DIR/c/bin"
CERTICOQ_RUNTIME="${OPAM_SWITCH_PREFIX}/lib/coq/user-contrib/CertiCoq/Plugin/runtime"

mkdir -p "$BIN_DIR"

echo "=== Compiling C with CompCert ==="

BENCHMARKS=("binary_trees_10" "binary_trees_14" "fannkuch_7" "fannkuch_8" "pidigits_27" "pidigits_100")

for bench in "${BENCHMARKS[@]}"; do
    cfile="$C_DIR/${bench}.c"
    hfile="$C_DIR/${bench}.h"
    outfile="$BIN_DIR/${bench}_compcert"

    [[ -f "$cfile" ]] || continue
    [[ -x "$outfile" ]] && { echo "  $bench: already compiled"; continue; }

    echo -n "  $bench: compiling... "

    # Create main wrapper
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

    if timeout 120 ccomp -O2 \
        -I"$CERTICOQ_RUNTIME" \
        -I"$C_DIR" \
        "$cfile" \
        "$wrapper" \
        "$CERTICOQ_RUNTIME/gc_stack.c" \
        "$CERTICOQ_RUNTIME/prim_int63.c" \
        "$CERTICOQ_RUNTIME/prim_floats.c" \
        -lgc -lm \
        -o "$outfile" 2>/dev/null; then
        echo "done"
    else
        echo "FAILED (timeout or error)"
    fi

    rm -f "$wrapper"
done

echo ""
echo "CompCert binaries:"
ls -la "$BIN_DIR"/*_compcert 2>/dev/null || echo "  (none)"
