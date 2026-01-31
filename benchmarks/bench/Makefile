# Peregrine Benchmark Suite Makefile
#
# Usage:
#   make all        - Build Rocq, extract ASTs, compile all backends, run benchmarks
#   make extract    - Build Rocq theories and extract AST files
#   make compile    - Compile ASTs to all backends
#   make run        - Run WASM benchmarks
#   make run-c      - Compile and run C benchmarks (requires gcc, libgc)
#   make clean      - Clean benchmark artifacts
#
# Prerequisites:
#   - peregrine in PATH (eval $(opam env))
#   - node for WASM runner
#   - gcc + libgc for C backend

.PHONY: all extract compile run run-c clean help

BENCH_DIR := $(shell pwd)
PARENT_DIR := $(BENCH_DIR)/..
AST_DIR := $(PARENT_DIR)/_build/default
TARGETS_DIR := $(BENCH_DIR)/targets

help:
	@echo "Peregrine Benchmark Suite"
	@echo ""
	@echo "Targets:"
	@echo "  make all       - Full pipeline: extract + compile + run"
	@echo "  make extract   - Build Rocq and extract AST files"
	@echo "  make compile   - Compile ASTs to WASM, C, etc."
	@echo "  make run       - Run WASM benchmarks"
	@echo "  make run-c     - Compile and run C benchmarks"
	@echo "  make quick     - Quick test (small inputs only)"
	@echo "  make clean     - Remove benchmark artifacts"

all: extract compile run

# Build Rocq theories and extract benchmark ASTs
extract:
	@echo "=== Building Rocq theories and extracting ASTs ==="
	cd $(PARENT_DIR) && dune build
	@echo ""
	@echo "AST files:"
	@ls -la $(AST_DIR)/*.ast 2>/dev/null || echo "  (none found)"

# Compile ASTs to various backends
compile: $(AST_DIR)
	@echo "=== Compiling to all backends ==="
	chmod +x $(BENCH_DIR)/compile_all.sh
	$(BENCH_DIR)/compile_all.sh $(AST_DIR)

# Run WASM benchmarks
run:
	@echo "=== Running WASM benchmarks ==="
	node $(BENCH_DIR)/run_benchmarks.js

# Quick test with just small inputs
quick:
	@echo "=== Quick test (small inputs) ==="
	@for f in $(TARGETS_DIR)/wasm/direct/*_10.wasm $(TARGETS_DIR)/wasm/direct/*_7.wasm $(TARGETS_DIR)/wasm/direct/*_27.wasm; do \
		if [ -f "$$f" ]; then \
			echo "Running: $$f"; \
			node -e "const fs=require('fs'); \
				const b=fs.readFileSync('$$f'); \
				WebAssembly.instantiate(b,{env:{write_char:()=>{},write_int:()=>{}}}).then(({instance})=>{ \
					const s=Date.now(); \
					instance.exports.main_function(); \
					console.log('  Time:', Date.now()-s, 'ms'); \
				});"; \
		fi \
	done

# Compile and run C benchmarks
run-c: compile
	@echo "=== Compiling C to native binaries ==="
	@mkdir -p $(TARGETS_DIR)/c/bin
	@for f in $(TARGETS_DIR)/c/direct/*.c; do \
		name=$$(basename $$f .c); \
		echo "Compiling $$name..."; \
		gcc -O3 -o $(TARGETS_DIR)/c/bin/$$name $$f -lgc 2>/dev/null || echo "  [FAILED - need libgc?]"; \
	done
	@echo ""
	@echo "=== Running C benchmarks ==="
	@for f in $(TARGETS_DIR)/c/bin/*; do \
		if [ -x "$$f" ]; then \
			echo "Running: $$f"; \
			time $$f 2>&1 || true; \
		fi \
	done

# Clean benchmark artifacts
clean:
	rm -rf $(TARGETS_DIR)
	rm -rf $(BENCH_DIR)/results
	rm -f $(AST_DIR)/*.ast 2>/dev/null || true

# Check if AST directory exists
$(AST_DIR):
	@echo "AST directory not found. Run 'make extract' first."
	@exit 1
