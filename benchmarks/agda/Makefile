# Agda Benchmarks Makefile
# 
# Compiles idiomatic Agda implementations to Haskell via MAlonzo,
# then to native code using GHC

TARGETS := BinaryTrees Fannkuch
.PHONY: all clean check $(TARGETS) help

AGDA := agda
GHC := ghc
GHC_RTS_OPTS := -s
GHC_FLAGS    := -package=text -O2 -rtsopts
AGDA_GHC_FLAGS := $(foreach f,$(GHC_FLAGS),--ghc-flag=$(f))
AGDA_GHC_FLAGS += --ghc-flag=-with-rtsopts="$(GHC_RTS_OPTS)"

# Outputs
BINARIES := $(addprefix bin/, $(TARGETS))

all: check $(TARGETS)

help:
	@echo "Agda Benchmarks Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make all              - Build all benchmarks"
	@echo "  make check            - Type-check all Agda files"
	@echo "  make BinaryTrees      - Build BinaryTrees benchmark"
	@echo "  make Fannkuch         - Build Fannkuch benchmark"
	@echo "  make clean            - Clean build artifacts"

# Type-check all Agda files
check:
	@echo "=== Type-checking Agda files ==="
	$(AGDA) BinaryTrees.agda
	$(AGDA) Fannkuch.agda
	@echo "✓ All files type-checked successfully"

# Create output directory
bin:
	mkdir -p bin

$(TARGETS): %: bin/%

# Compile Main program(s)
bin/%: Main%.agda bin %.agda Haskell.agda
	@echo "=== Compiling $* ==="
	mkdir -p _build$*
	$(AGDA) --ghc --compile-dir=_build$* $(AGDA_GHC_FLAGS) $<
	@if [ -f _build$*/Main$* ]; then \
		cp _build$*/Main$* $@; \
		echo "✓ $* compiled to $@"; \
	else \
		echo "✗ Compilation failed"; \
		exit 1; \
	fi

# Clean build artifacts
clean:
	rm -rf bin/
	rm -rf _build*
	rm -rf MAlonzo *~
