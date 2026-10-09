# Peregrine tests

To run the tests suite run `npm install` once and then `npm run test`.

To run only some of the test configurations listed in `test_configurations` ([src/tests.ts](src/tests.ts)), name them on the command line:
```bash
npm run test -- Rust Elm WebAssembly-cps
```

The test suite depends on the following:
* Node.js v22 or later
* cargo and rust compiler (the Rust tests fetch their crates from crates.io)
* [elm compiler](https://elm-lang.org/) 0.19.1, as `elm` on the `PATH` (the Elm tests fetch their packages from package.elm-lang.org)
* elm-test (installed by `npm install`)
* gcc
* [Lean](https://lean-lang.org/install/) (`lake`, installed with elan)

The Rust and Elm backends take typed programs, so their configurations only run the tests that have a `tsrc`, currently the Rocq ones.
They compile with `peregrine compile` and the pipeline configurations [src/rust/config.sexp](src/rust/config.sexp) and [src/elm/config.sexp](src/elm/config.sexp).


## Agda frontend tests
These tests are Agda programs compiled to $\lambda_\square$ with the [agda2lambox](https://github.com/agda/agda2lambox/tree/master) tool.
The tests are from the [agda2lambox test suite](https://github.com/agda/agda2lambox/tree/master/test).

The untyped programs (`*.ast`) were compiled with default configuration.

The type programs (`*.tast`) were compiled with `--typed --no-block` flags.

To reproduce the files run:
```bash
#!/bin/bash
git clone git@github.com:agda/agda2lambox.git
cd agda2lambox
cabal install

for f in test/*.agda; do
  agda2lambox $f -o dist/
  agda2lambox --typed --no-block $f -o dist-typed/
done

for f in dist-typed/*.ast; do
    mv "$f" "${f%.ast}.tast"
done

find dist/. -type f -name "*.txt" -delete
find dist-typed/. -type f -name "*.txt" -delete
```

## Directory
* [src/](src/): Test runner source code
* [rocq/](rocq/): Rocq test programs
* [lean/](lean/): Lean test programs
