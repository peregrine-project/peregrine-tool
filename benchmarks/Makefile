.PHONY: all clean theory extract test

all: theory

# Generate Makefile from _CoqProject
RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

# Build Rocq theories
theory: RocqMakefile
	+@make -f RocqMakefile

# Clean build artifacts
clean: RocqMakefile
	+@make -f RocqMakefile clean
	rm -f RocqMakefile
	rm -f extracted/*

# Directory for extracted code
extracted:
	mkdir -p extracted

# Note: Extraction happens within Rocq via the Extract.v file
# The Peregrine plugin handles the actual extraction
