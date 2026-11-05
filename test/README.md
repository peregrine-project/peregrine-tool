# Peregrine tests

To run the tests suite run `npm install` once and then `npm run test`.

To run only some of the test configurations listed in `test_configurations` ([src/tests.ts](src/tests.ts)), name them on the command line:
```bash
npm run test -- Rust Elm WebAssembly-cps
```
The names are the ones the runner prints (`Running Rust tests:`), matched exactly; an unknown name is an error.

The test suite depends on the following:
* Node.js v22 or later
* cargo and rust compiler (the Rust tests fetch their crates from crates.io)
* [elm compiler](https://elm-lang.org/) 0.19.1, as `elm` on the `PATH` (the Elm tests fetch their packages from package.elm-lang.org)
* elm-test (installed by `npm install`)
* gcc
* clang 15 or later, for the LLVM tests (`CLANG` names another binary, e.g. `CLANG=clang-15`)
* [Lean](https://lean-lang.org/install/) (`lake`, installed with elan)
* [.NET SDK](https://dotnet.microsoft.com/) 10 or later (`dotnet`), for the F# backend (experimental); without it the `FSharp-experimental` configuration fails
* [Koka](https://koka-lang.github.io/) 3.2.9 (`koka`), for the Koka backend (experimental); without it the `Koka-experimental` configuration fails

## Expected failures

Every test runs on every configuration, and either its result is compared with the expected one and passes, or it fails as an expected failure that an open issue tracks. No test is skipped, and no result goes unchecked: a driver that cannot print the result of a test fails it.

* A test marked `xfail` for a configuration (keyed by the name the runner prints, e.g. `Rust-untyped`) runs there and must fail. The runner reports it as an expected failure with its reason. If it passes, the suite fails with "remove the mark", so that a fix is noticed.
* A test marked `rejected` must be rejected by type inference in `Rust-untyped` and `Elm-untyped` (see below). `rejected: true` means that the program cannot be ML-typed, so the rejection is the correct behaviour. A string instead of `true` is the reason for a rejection that comes from a limitation of the backends.
* The reason of every `xfail` and of every limitation `rejected` names its issue, as `#N` (this repository) or `owner/repo#N`. The runner refuses to start if one does not. An issue still to be filed is written `#TBD-<slug>`.
* [check-issues.sh](check-issues.sh), which CI runs, collects the issue references of [src/tests.ts](src/tests.ts) and fails if one of the issues is closed, or if a placeholder `#TBD-<slug>` is left. When an issue is closed, its tests pass, or their marks need a new issue.


## Configurations

The Rust and Elm backends take typed programs, so the `Rust`, `Elm`, `Rust-verb`, `Rust-i64` and `Rust-hybrid` configurations compile the `tsrc` of each test: the Rocq programs extracted with `Peregrine Extract Typed`, and the Agda programs compiled with `--typed`. A test without a `tsrc` (the Lean programs: the Lean frontend has no typed output) fails there, and is marked as an expected failure.
The `Rust-untyped` and `Elm-untyped` configurations give the same backends the untyped `src` of every test, whose types peregrine then infers, and expect the outputs of the typed sources.
A test marked as `rejected` is a program whose types cannot be inferred, or that uses a feature the typed backends lack: there peregrine must fail with `Could not infer types`.
All four compile with `peregrine compile` and the pipeline configurations [src/rust/config.sexp](src/rust/config.sexp) and [src/elm/config.sexp](src/elm/config.sexp).
The `Rust-verb` and `Rust-i64` configurations compile the typed sources with the `rust` and `rust-i64` commands instead; `rust-i64` represents numbers as `i64`, so its tests have their own expected outputs (`rust_i64_output`), which `Rust-hybrid` shares; a test without one fails there. The `rust-gmp` command is not tested here: its `rug` crate builds GMP from source, which takes longer than the compile timeout.
The `LLVM` configuration links the emitted `.ll` module with CertiRocq's C runtime and the C glue, as the `C` configuration does.
The `OCaml-passes` configuration runs the OCaml tests with the optional `--specialize-instances` and `--cse` passes enabled and expects the same outputs.
The `OCaml-cofix`, `C-cofix` and `WebAssembly-cofix` configurations lower cofixpoints (`--lower-cofix true`) and run every test: the lowering changes nothing in a program without cofixpoints. Without that option, the C, LLVM, Wasm, OCaml and CakeML configurations must reject a test marked `cofix`.
The tests `rocq/theories/Demo.v`, `agda-src/*.agda` and `lean/source/Demo.lean` give peregrine the source of a program instead of a `.ast` file: peregrine runs the frontend, so `rocq` with the Peregrine plugin, `agda2lambox` and `lake` must be installed, and `test/lean` must be built.
The `CLI` configuration ([src/cli.ts](src/cli.ts)) checks the choice of the frontend from the extension of the input, and the errors of the frontend options, without running any frontend. It also checks the Rocq load path read from [rocq-project/_RocqProject](rocq-project/_RocqProject) or given with `--frontend-arg`, the names of a Rocq input with and without a logical path, and `--lean-config`, so it needs `rocq` and `lake`, and fails without them.
A test can give each backend an attribute file, passed with `--attributes`: the `Remap` test remaps an axiom and a definition, and `agda/Postulates` a postulate, with the `remap.sexp` file of each backend's directory under [src/](src/) (the C and LLVM tests link the C functions of [src/c/remap.c](src/c/remap.c)).
The `FSharp-experimental` configuration compiles every test with the experimental `fsharp` command, builds all the generated programs as one .NET project and runs each of them; it checks the outputs that the universal printers of [src/fsharp/TestPrinters.fs](src/fsharp/TestPrinters.fs) can print (booleans, natural numbers and lists of them).


## Agda frontend tests
These tests are Agda programs compiled to $\lambda_\square$ with the [agda2lambox](https://github.com/agda/agda2lambox/tree/master) tool.
The tests are from the [agda2lambox test suite](https://github.com/agda/agda2lambox/tree/master/test).

The programs of agda2lambox's `test/untyped` are compiled to untyped $\lambda_\square$, those of `test/typed` and `test/agda2rust` to typed $\lambda_\square^T$ (`--typed`); all are `.ast` files in `agda/`. The typed ones are the `tsrc` of their tests, and the untyped backends take the same file. The programs of `test/untyped` are also compiled with `--typed`, to `agda/typed/`, which are their `tsrc`. `agda2rust/Postulates` gets the realisation of its postulate `TODO` from the same attribute files as `Remap`. `untyped/Exports` and `untyped/Input` compute records of functions, and `untyped/Irr` a vector, which no driver can print: the tests [agda-src/Exports.agda](agda-src/Exports.agda), [agda-src/Input.agda](agda-src/Input.agda) and [agda-src/Irr.agda](agda-src/Irr.agda) are copies, with the flags of agda2lambox's test library, whose entry point computes a number, a boolean or a list from that result.

CI builds agda2lambox at the commit named in [.github/workflows/build.yml](../.github/workflows/build.yml) and runs its test suite, which compiles every test program to `test/dist/` and checks each one with `peregrine validate`. To reproduce the files, with `peregrine` on the `PATH`:
```bash
git clone https://github.com/agda/agda2lambox.git
cd agda2lambox
make test
mv test/dist/ ../peregrine-tool/test/agda/
mkdir ../peregrine-tool/test/agda/typed
cd test/untyped
for f in *.agda; do agda2lambox --typed -o ../../../peregrine-tool/test/agda/typed "$f"; done
```

## Directory
* [src/](src/): Test runner source code
* [rocq/](rocq/): Rocq test programs
* [lean/](lean/): Lean test programs
