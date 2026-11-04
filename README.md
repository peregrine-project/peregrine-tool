# Peregrine
[![Build](https://github.com/peregrine-project/peregrine-tool/actions/workflows/build.yml/badge.svg)](https://github.com/peregrine-project/peregrine-tool/actions/workflows/build.yml)
[![GitHub](https://img.shields.io/github/license/peregrine-project/peregrine-tool)](https://github.com/peregrine-project/peregrine-tool/blob/master/LICENSE)

Peregrine extracts code from proof assistants. Its frontends erase Rocq, Agda and Lean programs to $\lambda_\square$ (LambdaBox), the untyped lambda calculus of MetaRocq's verified erasure. Its middle-end, written and partly verified in Rocq, validates and transforms $\lambda_\square$. Its backends then compile the result to C, WebAssembly, LLVM IR, OCaml, CakeML, Rust, Elm, Lean, F# or Koka.

See [overview.md](doc/overview.md) for the pipeline and [usage.md](doc/usage.md) for every command and option.


## Install
Peregrine needs OCaml 4.14 and [opam](https://opam.ocaml.org/doc/Install.html):
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam install rocq-peregrine
```
This installs the `peregrine` command and the Rocq frontend. The Agda and Lean frontends are installed separately (see [Frontends](#frontends)). To build from source, see [dev.md](doc/dev.md).


## Quick start
```
peregrine BACKEND INPUT [-o OUTPUT] [OPTIONS]
```
`INPUT` is a proof-assistant source file or a $\lambda_\square$ program. Peregrine picks the frontend from the extension, runs it, and compiles the result with `BACKEND`:

```bash
# Rocq: extract the definition `main` of Prog.v to C (Prog.c and Prog.h); the load
# path comes from the nearest _RocqProject or _CoqProject
peregrine c Prog.v --entry main

# Agda: extract the definitions marked {-# COMPILE AGDA2LAMBOX main #-} to OCaml (Prog.mlf)
peregrine ocaml Prog.agda

# Lean: extract `main` of Prog.lean, in a Lake project that requires LeanToLambdaBox, to Rust
peregrine rust Prog.lean --entry main -o prog.rs

# A lambda box program, written by any frontend, to WebAssembly
peregrine wasm prog.ast -o prog.wasm

# Run the frontend only, or evaluate the program without any target toolchain
peregrine erase Prog.v --entry main -o prog.ast
peregrine eval prog.ast
```


## Frontends

| Frontend | Input | Tool that Peregrine runs | Typed $\lambda_\square^T$ | Verification | Project |
|----------|-------|--------------------------|---------------------------|--------------|---------|
| Rocq | `.v` | `rocq compile` with the Peregrine plugin (installed with `rocq-peregrine`) | yes | verified erasure (MetaRocq) | [plugin/](plugin/) |
| Agda | `.agda`, `.lagda`, `.lagda.md`, `.lagda.tex`, `.lagda.rst`, `.lagda.org`, `.lagda.typ`, `.lagda.tree` | `agda2lambox` | yes | unverified | [agda2lambox](https://github.com/agda/agda2lambox) |
| Lean | `.lean` | `lake env lean`, in a Lake project that requires LeanToLambdaBox | no; typed backends infer the types | partially verified | [lean-to-lambdabox](https://github.com/peregrine-project/lean-to-lambdabox) |

Any other file is read as a $\lambda_\square$ program ([format.md](doc/format.md)). See [usage.md](doc/usage.md#frontends) for frontend setup and options, and [frontends.md](doc/frontends.md) for how each frontend works.


## Backends

| Command | Output | Input | Needed to run the output | Verification |
|---------|--------|-------|--------------------------|--------------|
| `c` | `.c` and `.h` (Clight) | untyped | a C compiler and the CertiRocq runtime | verified compiler (CertiRocq); printer unverified |
| `wasm` | `.wasm` | untyped | a Wasm engine with tail calls (e.g. Wasmtime, Node.js) | verified compiler and printer (CertiRocq-Wasm) |
| `llvm` (experimental) | `.ll` | untyped | clang 15 or later and the CertiRocq runtime | partial, see [backends.md](doc/backends.md#llvm) |
| `ocaml` | `.mlf` (Malfunction) | untyped | `malfunction` and the OCaml compiler | verified compiler (verified extraction); the glue assumes the axiom `trust_coq_kernel` |
| `cakeml` | `.cml` | untyped | the CakeML compiler | verified compiler; the glue assumes the axiom `trust_coq_kernel` |
| `rust` | `.rs` | typed (types of untyped input are inferred) | `rustc` or `cargo` and the `bumpalo` crate (`rug` for some `--numbers`) | typed erasure verified; printer unverified |
| `elm` | `.elm` | typed (types of untyped input are inferred) | the Elm compiler | typed erasure verified; printer unverified |
| `lean` | `.lean` | untyped | Lake and the runtime in [lean/](lean/) | unverified |
| `fsharp` (experimental) | `.fs` | untyped | the .NET SDK | unverified |
| `koka` (experimental) | `.kk` | untyped | the Koka compiler | unverified |
| `eval` | the value, printed | untyped | nothing | debugging tool |
| `ast` | `.ast` | either | nothing | debugging tool |

The middle-end is only partly verified. Evaluation preservation for the passes that implement $\square$ and `lazy`/`force` is admitted (the first of them runs for every untyped backend except `ast`), and so are some pipeline preconditions ([Transforms.v](theories/erasure/Transforms.v)). The optional passes rest on axioms ([middleend.md](doc/middleend.md#optional-passes)). For each backend's output and runtime requirements, see [backends.md](doc/backends.md).
