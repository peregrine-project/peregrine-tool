# agda2lambox

An [Agda] backend to generate [MetaCoq] λ□ (LambdaBox) programs
for further verified extraction to WASM or Rust using the [Peregrine] tool.
The backend builds off Agda 2.7.0.1.
Compatible with Coq 8.19.0, MetaCoq 1.3.1 and CertiCoq 0.9.

[Agda]: https://github.com/agda/agda
[MetaCoq]: https://metacoq.github.io/

To install the backend, setup GHC (tested with `9.10.1`) and cabal.

```
git clone git@github.com:agda/agda2lambox.git
cd agda2lambox
cabal install
```

```
agda2lambox [AGDAFLAGS] [--out-dir DIR] [--typed] [--blocks] FILE
```

Then, use the [following tool][Peregrine] to further compile the generated `.ast` files to WASM, Rust, OCaml, C, and Elm.

## Setup

The backend generates `.v` and `.txt` files that contain the extracted λ□ environment.
To check what's generated, setup CertiCoq and compile the minimal Coq prelude.

```
opam pin add certicoq 0.9+8.19
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

## TODO

- [ ] Type aliases (See #3)
- [ ] Improve type compilation
    - The (re)implementation of the type translation is currently incomplete.
      In particular, when compiling an application, we should retrieve the type of the head and compile the elims with it.
- [ ] Check support for Agda-specific edge cases
  - [ ] Projection-like (See #6)
- [ ] Support primitives (ints and floats)
- [ ] Setup compilation to Wasm/Rust using Certicoq
- [ ] Setup proper testing infrastructure

## Icebox

Things that ought to be implemented, but not right now.

- [ ] Caching of compiled modules.

## References

- [The MetaCoq Project](https://github.com/MetaCoq/metacoq)
- [The CertiCoq Compilation pipeline](https://github.com/CertiCoq/certicoq/wiki/The-CertiCoq-pipeline)
- [CertiCoqWASM](https://github.com/womeier/certicoqwasm)
- [Pierre Letouzey's thesis introducing λ□](https://www.irif.fr/~letouzey/download/these_letouzey.pdf) (in French)
- [Verified Extraction from Coq to OCaml](https://github.com/yforster/coq-verified-extraction/)
  and its [accompanying paper](https://dl.acm.org/doi/10.1145/3656379)
- [Certified Erasure for Coq, in Coq](https://inria.hal.science/hal-04077552)
- [Extracting functional programs from Coq, in Coq](https://arxiv.org/pdf/2108.02995)
- [Lambdabox syntax and untyped environments](https://github.com/MetaCoq/metacoq/blob/coq-8.20/erasure/theories/EAst.v)
- [Lambdabox typed environments](https://github.com/MetaCoq/metacoq/blob/coq-8.20/erasure/theories/Typed/ExAst.v)
