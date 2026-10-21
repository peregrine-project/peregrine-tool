# Peregrine Backends

Peregrine backends compiles a $\lambda_\square$ or $\lambda_\square^T$ program down to one of several target languages. The choice of target is encoded in the `backend_config` field of the [configuration](format.md).

The table below summarises supported the backends


| Backend      | Source  | Verified | Verified printer | Target format       | Readability | Memory handling |
|--------------|---------|----------|------------------|---------------------|-------------|-----------------|
| C            | untyped | ✓ | ✗ | C-light                    | ✗ | Verified GC |
| WebAssembly  | untyped | ✓ | ✓ | Binary format              | ✗ | Bump allocator, no GC |
| OCaml        | untyped | ✓ | ✗ | Malfunction Serialized AST | ✗ | GC |
| CakeML       | untyped | ✓ | ✓ | Serialized AST             | ✗ | GC |
| Rust         | typed (untyped: experimental) | ✗ | ✗ | Source language            | ✓ | Bump allocator, no GC |
| Elm          | typed (untyped: experimental) | ✗ | ✗ | Source language            | ✓ | - |
| Lean         | untyped | ✗ | ✗ | Source language            | ✗ | Reference counting (Lean runtime) |
| F# (experimental) | untyped | ✗ | ✗ | Source language       | ✗ | .NET GC |
| AST (debug)  | either  | ✓ | ✓ | Serialized AST             | ✗ | - |
| Eval (debug) | either  | ✓ | ✗ | -                          | ✗ | -  |


## C

C backend extracting to surface level C-light (a subset of C). It accepts both typed and untyped ASTs as input.
Implemented in [CertiRocq](https://github.com/CertiRocq/certirocq/).

Output — a C-light program as a single `.c` and `.h` file. The CLI writes a `.c` file plus a `.h` header; the C must be linked against the CertiRocq runtime and glue code (see the [CertiRocq plugin docs](https://github.com/CertiRocq/certirocq/wiki/The-CertiRocq-plugin#compiling-the-generated-c-code)). The C output can then be compiled with [CompCert](https://compcert.org/) or any standard C compiler.

## WebAssembly

WebAssembly(Wasm) backend extracting to Wasm binary format. It uses the Wasm 2.0 standard with tail-call extension. It accepts both typed and untyped ASTs as input.
Implemented in [CertiRocq](https://github.com/CertiRocq/certirocq/).

Output — a file the binary-encoded Wasm module. The CLI writes a `.wasm` file. The module exports the main function as `main_function`.
The code can be executed by any Wasm 2.0 compatible runtime that supports the [tail-call extension](https://webassembly.org/features/) (e.g. recent Node.js, Wasmtime, modern browsers).

## OCaml

OCaml backend extracting to serialized [malfunction](https://github.com/stedolan/malfunction) AST. It accepts both typed and untyped ASTs as input.
Implemented in [coq-verified-extraction](https://github.com/yforster/coq-verified-extraction).

Output — serialized malfunction AST. The CLI writes a `.mlf` file containing the source; it is compiled with the [malfunction](https://github.com/stedolan/malfunction) tool.

## CakeML

CakeML backend extracting to serialized CakeML AST 

Output — serialized AST. The CLI writes a `.cml` file.
The `.cml` file can be compiled using the [CakeML compiler](https://cakeml.org/) using the flags `--sexp=true --exclude_prelude=true --skip_type_inference=true`.

## Rust

Rust backend extracting to surface level Rust code. The backend works on typed AST.
Untyped input is accepted as well: the middle-end first annotates it with types by Hindley-Milner inference ([EHindleyMilner.v](/theories/erasure/EHindleyMilner.v)), reconstructing the datatype signatures (type parameters, constructor field types) from how the constructors are used in the program. It is proved that erasing the annotations gives back the input and that the annotations are well scoped; the annotations themselves are unverified. When the program is not typable this way (dependent elimination, type-level computation, an inductive used at two incompatible field types, a constant used before its declaration, unsupported term forms such as primitives) peregrine fails with a message naming the constant and the types that did not unify; provide a typed program in that case. The reconstructed signature is the most general one consistent with the uses seen, so it can be more polymorphic than the source declaration (a record field may become a type parameter), and the body of an erased type parameter is typed `()`. Only type parameters become type parameters of the output: a parameter to which some constructor application passes a value (a syntactic criterion), or that no field type mentions (a `Prop` or phantom parameter), is dropped. Typed extraction drops value and `Prop` parameters too, but keeps phantom ones. `let`-bound and local fixpoint definitions are not generalised, so a `let`-bound function used at two types is rejected, and an axiom gets the type `forall a. a`. Postponed work, including a proof that the annotations type the terms, is tracked in [#79](https://github.com/peregrine-project/peregrine-tool/issues/79).
The backend is located in [`peregrine-project/rocq-typed-extraction`](https://github.com/peregrine-project/rocq-typed-extraction).

Output
* A single file; written to `<file>.rs` by the CLI.
* The generated Rust depends on [bumpalo](https://docs.rs/bumpalo/) v3 or later.
* Is compiled with the [Rust compiler](https://rust-lang.org/tools/install/)

### Numeric representations
The CLI has one Rust verb per representation of `nat`, `positive`, `N` and `Z`. Each verb is a backend configuration together with constant and inductive remappings ([theories/backends/](/theories/backends/)); `peregrine compile` with a configuration file uses no remapping unless the file gives one.

| Verb     | `nat`/`positive`/`N`/`Z` | Operations | Remaps | Extra crate |
|----------|--------------------------|------------|--------|-------------|
| `rust`   | the inductive types, as extracted | the extracted functions | none | - |
| `rust-gmp` | `&'a rug::Integer` (GMP) | GMP arithmetic | [RustGMPRemaps.v](/theories/backends/RustGMPRemaps.v) | [rug](https://docs.rs/rug/) 1 |
| `rust-i64` | `i64` | native `i64` arithmetic, overflow not checked | [RustNativeRemaps.v](/theories/backends/RustNativeRemaps.v) | - |
| `rust-mixed` | `&'a rug::Integer` | GMP, except `Nat.add`/`mul`/`sub`/`div`/`modulo`/`pow`/`eqb`/`leb`/`ltb` in `i64` | [RustMixedRemaps.v](/theories/backends/RustMixedRemaps.v) | rug 1 |
| `rust-mixed-narrow` | `&'a rug::Integer` | GMP, except `Nat.div`/`modulo`/`pow` in `i64` | [RustMixedRemaps.v](/theories/backends/RustMixedRemaps.v) | rug 1 |

`rust-gmp`, `rust-i64`, `rust-mixed` and `rust-mixed-narrow` also remap `bool` to the Rust `bool` and `comparison` to `std::cmp::Ordering`. `rust` remaps nothing and produces what `peregrine compile` produces with an empty configuration.
The remapped operations are hand-written Rust strings; nothing about them is verified.

* `rust-i64` computes in `i64` and does not check overflow: a result outside the `i64` range panics in a debug build and wraps around in a release build. `Nat.pow` casts its exponent to `u32`. Use it only for programs whose numbers stay in `i64`.
* `rust-mixed` and `rust-mixed-narrow` convert the arguments of the operations they run in `i64` with `to_i64().unwrap()`, which panics on an argument outside `i64`; the result of the `i64` operation is not checked, as for `rust-i64`. [RustMixedCoherence.v](/theories/backends/RustMixedCoherence.v) proves, for a ZArith model of these operations, that they agree with the `nat` operations when arguments and result fit in `i64`; it says nothing about the emitted Rust.
* The GMP eliminators of `rust-gmp`, `rust-mixed` and `rust-mixed-narrow` leak (`Box::leak`) the predecessor they compute.

## Elm

Elm backend extracting to surface level Elm code. The backend works on typed AST.
Untyped input is accepted and annotated as for [Rust](#rust).
The backend is located in [`peregrine-project/rocq-typed-extraction`](https://github.com/peregrine-project/rocq-typed-extraction).

Output
* A single file; written to `<file>.elm` by the CLI.
* The result has no external dependencies and is compiled with the [Elm compiler](https://guide.elm-lang.org/install/elm).

## Lean

Lean backend extracting to surface level Lean 4 code. It accepts both typed and untyped ASTs as input.
The backend is unverified. It is implemented in [`theories/lean/`](/theories/lean/) and [`theories/backends/LeanBackend.v`](/theories/backends/LeanBackend.v).

Output
* A single file; written to `<file>.lean` by the CLI.
* The generated Lean depends on the runtime library [`lean/Peregrine/Runtime.lean`](/lean/Peregrine/Runtime.lean).
* Is compiled with [Lake](https://lean-lang.org/install/), see [`lean/README.md`](/lean/README.md).

## F# (experimental)

Experimental F# backend extracting to surface level F# code. It accepts both typed and untyped ASTs as input.
The backend is unverified. It shares the intermediate representation and the compiler of the [Lean backend](#lean) ([`theories/lean/`](/theories/lean/)); its printer is [`theories/fsharp/PrintFSharp.v`](/theories/fsharp/PrintFSharp.v), and [`theories/backends/FSharpBackend.v`](/theories/backends/FSharpBackend.v) wraps both.

Output
* A single, self-contained `.fs` file, including an inlined runtime helper, so it has no external dependencies. Note the emitted file cannot run under `dotnet fsi` (scripts reject top-level `module` declarations); compile it inside a .NET project.
* Every value is printed as `obj`; source inductives become `[<RequireQualifiedAccess>]` discriminated unions, and nullary constants are wrapped in `Lazy<obj>` so they are not forced at module-init time.
* Compile and run with [`dotnet`](https://dotnet.microsoft.com/) in `Release` mode — `Debug` builds and `dotnet fsi` disable .NET tail calls. Deep non-tail recursion should run on a large-stack thread (the test harness uses a 512 MiB stack).
* Programs with primitive values (`tPrim`) are rejected at compile time. Remapping is not supported, as in the Lean backend.
* A nested mutual fixpoint, which no current frontend produces, compiles to code that fails when it is evaluated.

## Debug backends

Backends used for debugging.

### AST

Output the AST after running the middle-end pipeline.
Useful for debugging the pipeline and for inspecting intermediate steps in the middle-end.
Implemented in [`theories/backends/ASTBackend.v`](/theories/backends/ASTBackend.v); used by `peregrine ast`.

Output — a single file written by the CLI to `<file>.ast` (default extension is preserved across IR choices).

### Eval

Evaluates the $\lambda_\square$ input using an interpreter.
Implemented in [`theories/backends/EvalBackend.v`](/theories/backends/EvalBackend.v); used by `peregrine eval`.

Output — a string containing the printed value. The CLI prints it on stdout.



# Backend support
TODO

# Writing a new backend

Adding a new backend to Peregrine consists of two tasks.

1) Writing the backend
   - Implementing translation from $\lambda_\square$ or $\lambda_\square^T$ to the target language
   - Implementing printing or serialization of the target language. To properly integrate with Peregrine the result of the backend must be a string or list of strings. 
   - Optionally handling optional features such as remapping or split extraction
2) Integrating with Peregrine
   - Declare option format and default options and implement serialization
   - Declare which transformations and optimizations are required, optional, or incompatible with the backend, and provide default options for passes
   - Declare which features are supported by the backend
   - Implement name sanitization for the backend if necessary
   - Add wrapper function calling the backend and add it to `run_backend` in [`Pipeline.v`](/theories/Pipeline.v)
