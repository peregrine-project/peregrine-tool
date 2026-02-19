# Rocq Typed Extraction
[![Build](https://github.com/peregrine-project/rocq-typed-extraction/actions/workflows/build.yml/badge.svg)](https://github.com/peregrine-project/rocq-typed-extraction/actions/workflows/build.yml)
[![GitHub](https://img.shields.io/github/license/peregrine-project/rocq-typed-extraction)](https://github.com/peregrine-project/rocq-typed-extraction/blob/master/LICENSE)
[![Documentation](https://img.shields.io/github/deployments/peregrine-project/rocq-typed-extraction/github-pages?label=docs)](https://peregrine-project.github.io/rocq-typed-extraction/)


A framework for extracting Rocq programs to Rust and Elm.

## Meta

- Author(s):
  - Danil Annenkov (initial)
  - Mikkel Milo (initial)
  - Jakob Botsch Nielsen (initial)
  - Bas Spitters (initial)
  - Eske Hoy Nielsen
- License: [MIT](LICENSE)
- Compatible Rocq versions: 9.0
- Additional dependencies: MetaRocq
- Rocq namespace: `TypedExtraction`
- Related publication(s):
  - [Extracting functional programs from Coq, in Coq](https://arxiv.org/abs/2108.02995) doi:[10.1017/S0956796822000077](https://doi.org/10.1017/S0956796822000077)
  - ["Extending MetaCoq Erasure: Extraction to Rust and Elm"](https://dannenkov.me/papers/extraction-rust-elm-coq-workshop2021.pdf)
  - ["Extracting Smart Contracts Tested and Verified in Coq"](https://arxiv.org/abs/2012.09138) doi:[10.1145/3437992.3439934](https://doi.org/10.1145/3437992.3439934)

## Building and installation instructions

The easiest way to install the latest released version is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-typed-extraction
```

To instead build and install manually, do:

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
git clone https://github.com/peregrine-project/rocq-typed-extraction.git
cd rocq-typed-extraction
opam install . --deps-only
./configure.sh local
make #or make -j <number-of-cores-on-your-machine>
make install
```

## Documentation

For documentation see [examples](/tests/theories/) and [generated RocqDoc](https://peregrine-project.github.io/rocq-typed-extraction/).

Additional examples can be found in [ConCert](https://github.com/AU-COBRA/ConCert).
