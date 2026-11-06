# IO through a free monad

A program describes its input and output as a value of a free monad, and an
interpreter written in the source language runs it. Peregrine compiles the
program and the interpreter together, so only the primitive operations are
written for each backend.

`FreeIO.v` reads an integer `x`, prints `x` and `x + 1`, and returns `x + x`:

- `free A` has a constructor `Op o k` for an operation `o` and its continuation `k`.
- `interp` walks the tree and threads a value `token : world` through the two
  primitive axioms `put_int` and `get_int`. Each call depends on the previous
  one through the world, so evaluation keeps their order.
- `world` is declared in `Set`. Without the annotation Rocq puts a
  one-constructor inductive in `Prop`, and erasure removes every world argument
  together with the calls to `put_int`.

The primitives:

| Backend | File | Remap |
|---|---|---|
| OCaml | `ocaml/axioms.ml`, a module `Axioms` with `def_FreeIO_put_int` and `def_FreeIO_get_int` | none: Peregrine refers to an axiom `K` as `Axioms.def_K` |
| C | `c/freeio_prims.c` | `c/config.sexp`: `get_int` allocates its result pair through `mk_pair`, so its remap sets `re_const_gc` |

`make check` builds both programs, and the Wasm one below, and runs them with
input 3; each prints `3`, `4` and `result 6`.

`FreeIO.lean` is the same program in Lean, written against a class of
operations with one instance in `IO` and one in the free monad, so the source
also runs natively. It is erased by lean-to-lambdabox (`#erase_lcnf`, or
`#erase`, with `extern := .preferAxiom` and `nat := .machine`); the OCaml
primitives are then `def__FreeIO_primPutNat`, `def__FreeIO_primGetNat` and
`def__Nat_add`.

## SEIO* operations and strings

`seio/` uses the IO operations of SEIO\* (`io_read`, `io_write`, `io_open`,
`io_close` in `seio/Runtime.v`, with SEIO\*'s names and types) and primitive
strings. Because the names and the value conventions agree, the OCaml build
links SEIO\*'s own `axioms.ml`, fetched at the revision the Peregrine CI checks
SEIO\* against; only the C backend has its own realization,
`seio/runtime_prims.c`. `seio/Echo.v` reads standard input to its end and
writes it twice.

These operations take no world argument. The order of their calls is kept
because `interp` performs an operation before it applies the continuation to
the result, and the calls happen inside `interp` on variables, so no
middle-end pass sees two equal closed calls that it could merge.

## Wasm: a host-driven interpreter

The Wasm module that Peregrine emits has no imports, so the primitives cannot
be functions that the module calls. `wasm/WasmIO.v` therefore extracts the
free-monad tree itself (`main : free nat`, the program of `FreeIO.v` on
`nat`, as primitive integers do not reach the Wasm backend yet, #125), and the
host interprets it: `wasm/host.mjs` runs `main_function`,
reads the value from the exported global `result`, and while it is `Op o k`
performs `o`, writes the response into the module's memory at `mem_ptr`, and
calls the code of the closure `k` on its environment and the response. The
module exports every function, its memory and the globals `mem_ptr` and
`result`; the host reads the function index of each export from the binary's
export section, since the closure holds a table index and the module's table
maps index *i* to function *i*. Numbers are unary `nat`, so their size is bounded by the
program and not by the host: the host handles inputs of several million, but the
module's non-tail `x + x` exhausts Node's stack from an input of about 20000.

The host relies on the value layout and the calling convention of
CertiRocq's Wasm backend (unboxed constructors as `2 * ordinal + 1`, boxed ones
as a pointer to the ordinal and the arguments, closures as blocks holding a
table index and an environment, code taking the environment and then the
argument), and on the default direct-style pipeline (with `--cps` the closure
calls do not match). The host is trusted and outside the proof, and it is more
than the primitives: on OCaml and C `interp` is compiled with the program,
here the host is the interpreter. CertiCoq-Wasm's theorem covers the run of
`main_function` up to the first `Op o k`; the calls of `k` from the host, the
responses the host writes into memory and the layout it reads are not part of
its statement. `make check` runs it with Node on input 3.
