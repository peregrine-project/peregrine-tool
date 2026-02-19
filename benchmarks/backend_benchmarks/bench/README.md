# Peregrine Benchmarks

The contents of this directory is partially AI generated.

Benchmark suite based on the [Computer Language Benchmarks Game](https://benchmarksgame-team.pages.debian.net/benchmarksgame/) to compare Peregrine compilation backends.

## Benchmarks

- **Binary Trees**: Allocate and deallocate many binary trees
- **Fannkuch Redux**: Indexed-access to tiny integer-sequence
- **Pidigits**: Streaming arbitrary-precision arithmetic

## Directory Structure

```
benchmarks/
├── theories/           # Rocq source code
│   ├── BinaryTrees.v
│   ├── Fannkuch.v
│   ├── Pidigits.v
│   ├── BenchExtract.v  # Extraction for untyped backends
│   └── RustExtract.v   # Extraction for typed backends
├── bench/
│   ├── targets/
│   │   ├── lean/       # Native Lean 4 implementations
│   │   ├── ocaml_native/  # Native OCaml implementations
│   │   ├── c/          # Peregrine C output
│   │   ├── ocaml/      # Peregrine OCaml/Malfunction output
│   │   ├── rust/       # Peregrine Rust output
│   │   └── wasm/       # Peregrine WASM output
│   ├── results/
│   │   └── BENCHMARK_REPORT.md
│   └── *.sh            # Compilation and comparison scripts
└── Makefile
```

## Running Benchmarks

### 1. Build Rocq Sources and Extract

```bash
cd benchmarks
make
```

This compiles the Rocq code and generates `.ast` and `.tast` files.

### 2. Compile to Backends

```bash
cd bench
./compile_all.sh      # WASM + C targets
./compile_c.sh        # Compile C to native (GCC)
./compile_compcert.sh # Compile C with CompCert
./compile_ocaml.sh    # Compile to OCaml/Malfunction
./compile_rust.sh     # Compile to Rust
```

### 3. Run Comparisons

```bash
./comprehensive_compare.sh   # Full comparison table
./run_native_comparison.sh   # Lean vs OCaml only
```

## Native Language Implementations

The `bench/targets/lean/` and `bench/targets/ocaml_native/` directories contain purely functional implementations in Lean 4 and OCaml for fair comparison.

All implementations use:
- Immutable data structures (lists instead of mutable arrays)
- Purely functional style
- Arbitrary precision integers where needed
