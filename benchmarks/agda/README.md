# Agda Benchmarks

This folder contains idiomatic Agda implementations of the following Benchmarks:

1. **BinaryTrees.agda** - Allocates and deallocates many binary trees, computing checksums.
2. **Fannkuch.agda** - Indexed-access to tiny integer-sequences via permutations and flips.

The implementation is based on the one for Lean, in this very same repo.

---


```bash
$ make help
Agda Benchmarks Makefile

Targets:
  make all              - Build all benchmarks
  make check            - Type-check all Agda files
  make BinaryTrees      - Build BinaryTrees benchmark
  make Fannkuch         - Build Fannkuch benchmark
  make clean            - Clean build artifacts
```

Once `make all` is run, `bin/` contains both `BinaryTrees` and `Fannkuch` executables.
Both may take an integer as argument, and have been compiled with the `-s` RTS option,
so they display timing information when executed.
