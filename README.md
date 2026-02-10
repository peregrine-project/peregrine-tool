# Peregrine
[![Build](https://github.com/peregrine-project/peregrine-tool/actions/workflows/build.yml/badge.svg)](https://github.com/peregrine-project/peregrine-tool/actions/workflows/build.yml)
[![GitHub](https://img.shields.io/github/license/peregrine-project/peregrine-tool)](https://github.com/peregrine-project/peregrine-tool/blob/master/LICENSE)

The Peregrine Project provides a unified middle-end for code generation from proof assistants. It supports Agda, Lean, and Rocq and can generate code in CakeML, C, Rust, OCaml.

It puts a focus on correct code extraction: The middle end is verified in the Rocq proof assistant, and some of the frontends and backends are. It is based on an intermediate language called $\lambda_\square$ (LambdaBox).

## Setup
The backend requires OCaml 4.13 or later to run. The development also depends on Rocq 9.0, and developer builds of CertiCoq.

The backend can be installed using [Opam](https://opam.ocaml.org/doc/Install.html) with:
```bash
git clone https://github.com/peregrine-project/peregrine-tool.git
cd peregrine-tool
opam switch create . 4.14.2 --repositories default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
opam install .
```

## Usage
```
peregrine TARGETLANGUAGE FILE [-o FILE]
```
E.g. compiling `prog.ast` file to WebAssembly.
```
peregrine wasm prog.ast -o prog.wasm
```
Valid values for `TARGETLANGUAGE` are:
* `wasm`
* `c`
* `ocaml`
* `rust`
* `elm`

For detailed usage on all commands and flags see [here](#command-line-interface) or use `peregrine --help`.


## Pipeline
$\lambda_\square$ is an untyped lambda-calculus with inductive types, explicit fixpoint combinator, case expressions, and $\square$ box terms which represent erased computationally irrelevant terms.
$\lambda_\square^T$ is an extension of $\lambda_\square$ which contains typing information.

$\lambda_\square$ and $\lambda_\square^T$ are intermediate languages used in the [MetaCoq](https://github.com/MetaRocq/metarocq) framework. Several other frameworks built on top of MetaCoq and implement verified extraction. MetaCoq implements quoting and verified erasure of Coq terms to $\lambda_\square$ terms, it also includes verified optimizations.

![](/doc/pipeline.png)

### Supported Languages (backends)
The tool currently supports extracting $\lambda_\square$ to WebAssembly, C and OCaml, and $\lambda_\square^T$ to Rust and Elm.

#### WebAssembly
Verified extraction to WebAssembly is implemented in [CertiCoq-Wasm](https://github.com/womeier/certicoqwasm).
It extends on the CertiCoq with an additional translation from $\lambda_{ANF}$ to WebAssembly.
More information can be found in the [paper](https://womeier.de/files/certicoqwasm-cpp25-paper.pdf).
##### Running the extracted Wasm code
Extracted Wasm code can be run using any WebAssembly engine supporting the [tail call extension](https://webassembly.org/features/) of WebAssembly.

Examples of how to run Wasm in [browsers](https://developer.mozilla.org/en-US/docs/WebAssembly/Guides/Loading_and_running), [Node.js](https://nodejs.org/en/learn/getting-started/nodejs-with-webassembly), [Wasmtime](https://docs.wasmtime.dev/lang.html).

The program main function will be exported as `main_function` in extracted Wasm module.


#### C (Clight)
[Clight](https://link.springer.com/article/10.1007/s10817-009-9148-3) is a subset of C used by the verified [CompCert](https://compcert.org/) compiler.
Clight includes pointer arithmetic, struct and union types, loops, and structured switch statements.

A verified compiler to Clight is implemented in [CertiCoq](https://github.com/CertiCoq/certicoq).
##### Compiling Clight
Clight can be compiled using [CompCert](https://compcert.org/) or any ordinary C compiler (GCC, clang, ...).
The generated C code must be linked with the garbage collector and glue code as described [here](https://github.com/CertiCoq/certicoq/wiki/The-CertiCoq-plugin#compiling-the-generated-c-code).


#### OCaml (malfunction)
https://github.com/yforster/coq-verified-extraction implements verified extraction to OCaml or more specifically [Malfunction](https://github.com/stedolan/malfunction) which is an internal language used in the OCaml compiler.

For more details see the paper [Verified Extraction from Coq to OCaml](https://dl.acm.org/doi/10.1145/3656379).

##### Compiling Malfunction
Malfunction can compiled using the [malfunction](https://github.com/stedolan/malfunction) tool.


#### Rust
The Rust extraction uses the certified typed erasure of MetaCoq to extracted programs to $\lambda_\square^T$ which is printed to Rust, the printing step is unverified.
For more details see the paper [Extracting functional programs from Coq, in Coq](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/extracting-functional-programs-from-coq-in-coq/ACA1A3F43DD4EA96646F705BC2F8E370).
##### Compiling extracted Rust code
Extracted Rust code depends on [bumpalo](https://docs.rs/bumpalo/latest/bumpalo/) v3 or later.


#### Elm
The Elm extraction uses the certified typed erasure of MetaCoq to extracted programs to $\lambda_\square^T$ which is printed to Elm, the printing step is unverified.
For more details see the paper [Extracting functional programs from Coq, in Coq](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/extracting-functional-programs-from-coq-in-coq/ACA1A3F43DD4EA96646F705BC2F8E370).
##### Compiling extracted Elm code
The extracted Elm code does not depend on any external libraries and can be compiled with the [Elm compiler](https://guide.elm-lang.org/install/elm).



### Frontends
The peregrine tool compiles $\lambda_\square$ and $\lambda_\square^T$ to various languages, the $\lambda_\square$ programs can be obtained from either Coq or Agda using the frontends described here.

#### Agda (Agda2lambox)
[Agda2lambox](https://github.com/agda/agda2lambox) is a frontend translating [Agda](https://github.com/agda/agda) programs into $\lambda_\square$ and $\lambda_\square^T$.

To use the Agda2lambox frontend you should first annotate the definition you wish to translate with `{-# COMPILE AGDA2LAMBOX DEF_NAME #-}`.
For example
```
test = ...
{-# COMPILE AGDA2LAMBOX test #-}
```

The program can then be translated to $\lambda_\square$ using
```
agda2lambox FILE
```
or to $\lambda_\square^T$ using
```
agda2lambox --typed --no-block FILE
```

#### Coq (MetaCoq)
[MetaCoq](https://github.com/MetaRocq/metarocq) is a project formalizing Coq in Coq and providing tools for manipulating Coq terms and developing certified plugins (i.e. translations, compilers or tactics) in Coq.
It can be used to translate Coq programs into $\lambda_\square$ and $\lambda_\square^T$ using the Peregrine Rocq plugin.

```coq
From Peregrine Require Import Loader.

Definition add_5 (n : nat) : nat := n + 5.

(* Extract to untyped lambda box *)
Peregrine Extract "test.ast" add_5.

(* Extract to typed lambda box *)
Peregrine Extract Typed "test.ast" add_5.
```


 It can be used to translate Coq programs into $\lambda_\square$ and $\lambda_\square^T$ using [CoqToLambdaBox.v](theories/CoqToLambdaBox.v).

For extracting Coq programs it is recommended to use the respective extraction backends in Coq rather than using the standalone peregrine tool.

#### Lean (lean-to-lambox)
The [lean-to-lambox](https://github.com/peregrine-project/lean-to-lambdabox) frontend produces $\lambda_\square$ for [Lean]() programs.

Usage
To use the lean-to-lambox frontend use the `#erase DEF_NAME to "FILE"` notation in Lean.
```
import LeanToLambdaBox

def val_at_false (f: Bool -> Nat): Nat := f .false

#erase val_at_false to "out.ast"
```

## Command Line Interface
### Common arguments
* `-o FILE` output file for extracted program
* `--quiet`, `--verbose`, `--debug` controls the level of feedback from the program

### Extraction commands
```
peregrine TARGETLANGUAGE FILE [-o FILE]
```
Valid values for `TARGETLANGUAGE` are:
* `wasm`
* `c`
* `ocaml`
* `rust`
* `elm`

The `wasm` and `c` targets also supports the `--cps` flag that uses verified cps translation during compilation instead of the unverified direct translation.
