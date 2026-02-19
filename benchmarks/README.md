# Peregrine benchmarks

## Frontend benchmarks
Compare equivalent programs compiled with Rocq, Agda, and Lean frontends and Rocq built-in unverified OCaml extraction.

The examples use no remappings/efficient types as we focus purely on testing the frontend translations.
We benchmark the frontends with the C and OCaml Peregrine backends.

### Running benchmarks
`make compile-c` to compile benchmarks to C and then run `make bench-c` to run the benchsmarks

`make compile-ocaml` to compile benchmarks to OCaml and then run `make bench-ocaml` to run the benchsmarks

### Frontends to C
```
rocq/bin/c/BinaryTrees 15 ran
  1.01 ± 0.02 times faster than agda/bin/c/BinaryTrees 15
  1.23 ± 0.03 times faster than lean/bin/c/BinaryTrees 15
rocq/bin/c/Sieve 2000 ran
  1.48 ± 0.12 times faster than agda/bin/c/Sieve 2000
  2.26 ± 0.03 times faster than lean/bin/c/Sieve 2000
agda/bin/c/Quicksort 20 ran
  1.04 ± 0.42 times faster than rocq/bin/c/Quicksort 20
  1.05 ± 0.23 times faster than lean/bin/c/Quicksort 20
rocq/bin/c/Fannkuch 9 ran
  2.29 ± 0.31 times faster than lean/bin/c/Fannkuch 9
agda/bin/c/Arith 8 ran
  1.10 ± 0.30 times faster than lean/bin/c/Arith 8
  1.11 ± 0.30 times faster than rocq/bin/c/Arith 8
```

### Frontends to OCaml
```
agda/bin/ocaml/BinaryTrees 15 ran
  1.04 ± 0.02 times faster than rocq/bin/ocaml/BinaryTrees 15
  1.10 ± 0.02 times faster than lean/bin/ocaml/BinaryTrees 15
rocq/bin/ocaml/Sieve 2000 ran
  1.50 ± 0.11 times faster than agda/bin/ocaml/Sieve 2000
  2.05 ± 0.03 times faster than lean/bin/ocaml/Sieve 2000
rocq/bin/ocaml/Quicksort 20 ran
  1.02 ± 0.17 times faster than lean/bin/ocaml/Quicksort 20
  1.04 ± 0.39 times faster than agda/bin/ocaml/Quicksort 20
rocq/bin/ocaml/Fannkuch 9 ran
  1.63 ± 0.04 times faster than lean/bin/ocaml/Fannkuch 9
agda/bin/ocaml/Arith 8 ran
  1.15 ± 0.06 times faster than lean/bin/ocaml/Arith 8
  1.18 ± 0.28 times faster than rocq/bin/ocaml/Arith 8
```

### Differences between implementations
We avoid some let bindings in the Agda files since they are inlined leading to duplicate computation. This doesn't happen in the Rocq and Lean frontends.

Addition and multiplication are recursive in the second argument in Lean in contrast to Rocq and Agda. We swap the order of arguments to calls of those functions in the Lean files.

Lean csimp replaces list append with a tail recursive version during translation to $\lambda_\square$, so we use similar tail recursive version in the Agda and Rocq files.

`&&` and `||` is short-circuiting in Lean. We inline the definitions in Rocq and Agda files.

Agda frontend doesn't properly handle `if then else` so we rewrite those in Agda files.

Lean modulo implementation is inefficient, so we reimplement it to match Rocq.

### Differences in compilation
When compiling $\lambda_\square$ produced by the Rocq frontend we need to reorder the constructors of booleans as the order is different from Lean and Agda.

For $\lambda_\square$ produced by the Lean frontend we need to remap some the "Eq.rec" and "False.rec" axioms from Lean.

## Backend benchmarks
