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

No test is skipped. A test marked `xfail` for a configuration is a known failure: it runs, the runner reports it as an expected failure with its reason (which names the issue), and if it passes the suite fails, so that the mark is removed. A test marked `unsupported` for a configuration needs something that configuration cannot do by design; it is not run, and the runner prints it with the reason. Both are keyed by the configuration names that the runner prints.

The Rust and Elm backends take typed programs, so the `Rust` and `Elm` configurations only run the tests that have a `tsrc`, currently the Rocq ones.
The `Rust-untyped` and `Elm-untyped` configurations give the same backends the untyped `src` of every test, whose types peregrine then infers, and expect the outputs of the typed sources.
A test marked as `rejected` is a program whose types cannot be inferred, or that uses a feature the typed backends lack (cofixpoints, primitive values): there peregrine must fail with `Could not infer types`.
All four compile with `peregrine compile` and the pipeline configurations [src/rust/config.sexp](src/rust/config.sexp) and [src/elm/config.sexp](src/elm/config.sexp).
The `Rust-verb` and `Rust-i64` configurations compile the typed sources with the `rust` and `rust-i64` commands instead; `rust-i64` represents numbers as `i64`, so its tests have their own expected outputs (`rust_i64_output`). The `rust-gmp` command is not tested here: its `rug` crate builds GMP from source, which takes longer than the compile timeout.
The `LLVM` configuration links the emitted `.ll` module with CertiRocq's C runtime and the C glue, as the `C` configuration does.
The `OCaml-passes` configuration runs the OCaml tests with the optional `--specialize-instances` and `--cse` passes enabled and expects the same outputs.
The tests `rocq/theories/Demo.v`, `agda-src/Demo.agda` and `lean/source/Demo.lean` give peregrine the source of a Demo program instead of a `.ast` file: peregrine runs the frontend, so `rocq` with the Peregrine plugin, `agda2lambox` and `lake` must be installed, and `test/lean` must be built.
The `CLI` configuration ([src/cli.ts](src/cli.ts)) checks the choice of the frontend from the extension of the input, and the errors of the frontend options, without running any frontend. It also checks the Rocq load path read from [rocq-project/_RocqProject](rocq-project/_RocqProject) or given with `--frontend-arg`, the names of a Rocq input with and without a logical path, and `--lean-config`, so it needs `rocq` and `lake`, and fails without them.
The `FSharp-experimental` configuration compiles every test with the experimental `fsharp` command, builds all the generated programs as one .NET project and runs each of them; it checks the outputs that the universal printers of [src/fsharp/TestPrinters.fs](src/fsharp/TestPrinters.fs) can print (booleans, natural numbers and lists of them).


## Agda frontend tests
These tests are Agda programs compiled to $\lambda_\square$ with the [agda2lambox](https://github.com/agda/agda2lambox/tree/master) tool.
The tests are from the [agda2lambox test suite](https://github.com/agda/agda2lambox/tree/master/test).

CI builds agda2lambox at the commit named in [.github/workflows/build.yml](../.github/workflows/build.yml) and runs its test suite, which compiles every test program to `test/dist/` and checks each one with `peregrine validate`. To reproduce the files, with `peregrine` on the `PATH`:
```bash
git clone https://github.com/agda/agda2lambox.git
cd agda2lambox
make test
mv test/dist/ ../peregrine-tool/test/agda/
```

## Directory
* [src/](src/): Test runner source code
* [rocq/](rocq/): Rocq test programs
* [lean/](lean/): Lean test programs
