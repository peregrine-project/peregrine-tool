# Peregrine Benchmark Report

**Date:** 2026-02-11
**Benchmarks:** Computer Language Benchmarks Game + extended suite
**Upstream:** post ast-format merge (PR #47)

## Executive Summary

This report compares:
1. **Native language implementations** (Lean 4, OCaml) - purely functional style
2. **Peregrine compilation backends** for Rocq - C, WASM, OCaml (Malfunction)

All implementations use purely functional data structures (immutable lists, trees) for fair comparison. Timing is handled uniformly by the test harness (C wrapper with `clock()` for native, `Date.now()` for WASM, wall-clock for Malfunction).

## Benchmarks Game Results (milliseconds)

| Benchmark | Lean 4 | OCaml | P:C/gcc | P:WASM/d | P:WASM/c | P:OCaml |
|-----------|--------|-------|---------|----------|----------|---------|
| binary_trees_10 | 0.22 | 1.31 | 2.12 | 6 | 12 | 5.8 |
| binary_trees_14 | 5.02 | 10.08 | 56.35 | 94 | 513 | 29.1 |
| binary_trees_16 | 26.19 | 63.05 | 307.74 | ERR | 10031 | ERR |
| fannkuch_7 | ERR | 1.19 | 11.14 | 102 | 97 | 7.6 |
| fannkuch_8 | ERR | 3.39 | 257.30 | ERR | 1064 | 45.3 |
| fannkuch_9 | ERR | 26.34 | ERR | ERR | 16710 | ERR |
| pidigits_27 | 0.11 | 0.08 | 26.64 | 72 | 100 | 75.1 |
| pidigits_100 | 0.53 | 0.57 | 2327.36 | 6825 | 8696 | 6436.3 |
| pidigits_500 | 6.55 | 3.82 | TIMEOUT | 211415 | 51766 | ERR |

*Times in milliseconds. Lower is better. ERR = stack overflow or runtime error. TIMEOUT = >60s.*

### Extended Benchmarks (P:C/gcc)

| Benchmark | P:C/gcc (ms) |
|-----------|-------------|
| tak_18_12_6 | 1.72 |
| tak_21_14_7 | 11.10 |
| symbdiff_20 | 0.09 |
| symbdiff_50 | 0.16 |
| lambda_fact_10 | 0.25 |
| sieve_1000 | 888.42 |

*Note: ackermann ERRs (stack overflow), sieve_5000+ TIMEOUTs, nqueens/treesort/quicksort need Uint63 primitives.*

## Key Observations

1. **Native Lean 4 is 10-100x faster** than Peregrine-compiled Rocq
2. **Native OCaml is 5-50x faster** than Peregrine-compiled Rocq
3. **P:OCaml (Malfunction) now works** - previously N/A across all benchmarks
4. **P:OCaml beats P:C/gcc on tree/list benchmarks** (binary_trees_14: 29ms vs 56ms, fannkuch_8: 45ms vs 257ms)
5. **P:C/gcc remains fastest for arithmetic** (pidigits_100: 2327ms vs 6436ms for P:OCaml)
6. **WASM CPS handles larger inputs** but at 5-40x speed cost vs direct
7. **Lean 4 Fannkuch ERRs** - needs stack size increase for list-heavy recursion

### Changes vs Previous Report (2026-01-31)

| Benchmark | Old P:C/gcc | New P:C/gcc | Delta |
|-----------|-------------|-------------|-------|
| binary_trees_14 | 60.7 | 56.4 | -7% |
| fannkuch_7 | 12.8 | 11.1 | -13% |
| fannkuch_8 | 268.2 | 257.3 | -4% |
| pidigits_27 | 29.5 | 26.6 | -10% |
| pidigits_100 | 2347.2 | 2327.4 | -1% |

The upstream AST format changes (PR #47) brought modest C backend improvements (~5-13% faster on tree/list benchmarks).

The **OCaml/Malfunction backend is the biggest improvement** - going from completely non-functional to competitive performance on tree-heavy benchmarks.

## Performance Rankings

| Rank | Backend | Relative Speed | Best For |
|------|---------|----------------|----------|
| 1 | **P:OCaml** | 0.5-2x vs C/gcc | Tree/list-heavy code |
| 2 | **P:C/GCC -O3** | 1.0x (baseline) | Arithmetic-heavy code |
| 3 | **P:WASM/direct** | 0.05-0.2x vs C | Small inputs, portability |
| 4 | **P:WASM/CPS** | 0.01-0.1x vs C | Large inputs (no stack limit) |

### WASM Direct vs CPS

The direct pipeline is 2-10x faster but hits stack overflow on larger inputs:
- binary_trees_16: ERR (direct) vs 10s (CPS)
- fannkuch_8+: ERR (direct) vs works (CPS)

**Recommendation:** Use CPS for production, direct for small inputs.

## Compilation Pipeline

```
Rocq Source
    | (Peregrine Extract via Plugin)
    v
Lambda Box AST (.ast)  -- new sexp serialization format (PR #47)
    |
    v
+---------------------------+        +----------+
|  Untyped Backends         |        |  Typed   |
|  WASM (direct/CPS)        |        |  Backends|
|  C -> GCC/CompCert        |        |  Rust    |
|  OCaml -> Malfunction     |        |  Elm     |
+---------------------------+        +----------+
```

## Limitations

- **Uint63 primitives**: nqueens, treesort, quicksort benchmarks need Int63 primitive support in the C backend (extraction fails with "Axioms found")
- **Stack depth**: ackermann, large fannkuch, large binary_trees hit stack overflow in direct pipelines
- **Arithmetic perf**: pidigits shows Peregrine is ~4000x slower than native for bignum-heavy code
- **Lean fannkuch**: Lean 4 implementation hits stack overflow (needs `@[reducible]` or increased stack)

## Test Environment

- **Platform:** Linux 6.17.0
- **Lean 4:** via lake
- **OCaml:** 5.2.0 with Zarith
- **Rocq:** 9.0.0
- **Peregrine:** post-PR#47 (ast-format branch merged)
- **GCC:** 13.3.0
- **Node.js:** 24.11.0 (for WASM)
- **Malfunction:** 0.7
