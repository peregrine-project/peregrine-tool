# Verified Extraction from Rocq to OCaml

This repository contains the current development state of a new verified extraction from Rocq to OCaml, based on MetaRocq.
Technically, the extraction targets [Malfunction](https://github.com/stedolan/malfunction), which is a specification of Lambda, the internal language of the OCaml compiler.
We use Malfunction as target for extraction from Rocq, and rely on the Malfunction and OCaml compilers to obtain `.cmx` files that will behave like `.cmx` files created by Rocq's current extraction process and the Ocaml compiler.
In particular, Rocq programs extracted like this can interact with other OCaml programs and with Rocq programs extracted using the existing extraction.

The implementation of extraction is fully functional and supports all of Rocq's constructs including
primitive integers, floats and arrays, but the cofixpoint to lazy/force translations is not verified yet.
The article ["Verified Extraction from Coq to OCaml"](https://dl.acm.org/doi/10.1145/3656379) by Yannick Forster,
Matthieu Sozean and Nicolas Tabareau, published and awarded at PLDI'24, describes this development.

See the online [documentation](https://metarocq.github.io/rocq-verified-extraction-9.0/toc.html) for more information on the development.

## Installation

```
opam switch create coq-malfunction --packages="ocaml-variants.4.14.1+options,ocaml-option-flambda"
eval $(opam env --switch=coq-malfunction)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin -n -y "https://github.com/MetaRocq/metarocq.git#v1.3.2-8.19"
opam pin -n -y "https://github.com/stedolan/malfunction.git#master"
opam install . --deps-only
make -j 4
```

## Usage

After `From VerifiedExtraction Require Import Extraction.`
the commands `Verified Extraction <definition>` and `Verified Extraction <definition> "<file>.mlf"` can be used to run the new extraction process.
Multiple functions can be extracted at the same time with `Verified Extraction (<d1>,<d2>,...)`.
To add an `mli` file one can add the output of the (unverified) generator `MetaRocq Run Print mli <definition>.` to a `.mli` file.
Note that this metaprogram does not (yet) take into account the reordering of constructors, besides the one for booleans (see `Extract Inductives` below).
It won't output declarations for `unit`, `bool`, `list`, `option` and `prod` that have matching representations in OCaml. 

`Verified Extraction` supports the following options:

- `-time`: prints compilation and run times
- `-typed`: uses typed extraction to perform more agressive argument removal
- `-bypass-qeds`: by default, Qed's proofs are turned into opaque constants during reification in MetaRocq, so 
   that the reified environment is smaller, this bypasses this behavior and reifies everything (can be uterly slow).
   Axioms are turned into external function calls, so if some remain in the extracted code they will have to be implemented
   (in the produced `Axioms.ml` file)
- `-compile-plugin`: compile the code as a Rocq plugin that can be loaded.
- `-compile-with-coq`: compile the code as a standalone program that however links with Rocq's codebase (c.f. the `RocqMsgFFi.v` file)
- `-compile`: compile the code as a fully standalone program not depending on Rocq (can be run from the shell)
- `-optimize`: Use "malfunction -O2" to compile produced code.
- `-load`: load the plugin into Rocq
- `-run`: Runs the compiled program or linked plugin and readback it's computed value. Plugins using the `RocqMsgFFI.v` can 
  output information in Rocq's info, notice and error channels while running.
- `-verbose`: More verbose compiler output
- `-fmt`: Use malfunctions automatic formatting to produce the .mlf file (for more readable generated code)
- `-unsafe`: Use unsafe optimizations (all of them, or a subset by listing some of the following flags separated by spaces):
    + `cofix-to-lazy`: unverified cofixpoints to lazy/force translation
    + `inlining`: honor `Verified Extract Inline` directives.
    + `unboxing`: perform unboxing of types having a single constructor with a single computational argument 
      This is run after typed erasure for more opportunities to unbox.
    + `betared`: perform apparent beta reductions (useful when combined with inlining)

`Verified Extraction` also supports the directives:
  + `Verified Extract Inductives [ ind [ name [ tags ] ], .. ]`: this declares a reordering of constructors 
    to match existing ocaml datatype representations (tags are natural numbers). This reordering phase is 
    verified. By default, Rocq's booleans `Inductive bool := true | false` are mapped to OCaml's 
    `type bool = false | true` by swapping their constructor tags.
  + `Verified Extract Inline cst`: declares `cst` to be inlined (expanded everywhere) during extraction.
    This phase is NOT verified at the moment.
    
## Structure

- the [`theories`](theories) directory contains the Rocq files with implementation and verification of the plugin
  - [`Malfunction.v`](theories/Malfunction.v) contains the syntax definition of Malfunction. It is a direct, line-to-line port of the OCaml file [`malfunction.ml`](https://github.com/stedolan/malfunction/blob/master/src/malfunction.ml) to Rocq.
  - [`SemanticsSpec.v`](theories/SemanticsSpec.v) defines an inductive big-step evaluation predicate.
  - [`Compile.v`](theories/Compile.v) defines a compilation function of lambda box to Malfunction.
  - [`CompileCorrect.v`](theories/CompileCorrect.v) proves the correctness of this function, using the correctness proof of case analysis in [`Mcase.v`](theories/Mcase.v)
  - [`Interpreter.v`](theories/Interpreter.v) contains an interpretation function, which is close to [`malfunction_interpreter.ml`](https://github.com/stedolan/malfunction/blob/master/src/malfunction_interpreter.ml), and a proof that values according to the evaluation predicate are also found by the interpreter. Note that since the interpreter is not necessarily terminating we switch of Rocq's termination checker, meaning this proof can only be seen as a sanity check.
  - [`Serialize.v`](theories/Serialize.v) contains seralization functions into s-expressions. There is also a parser in [`Deserialize.v`](theories/Deserialize.v), used for testing.
  - [`Pipeline.v`](theories/Pipeline.v) composes the full extraction pipeline from Rocq to Malfunction
  - [`PipelineCorrect.v`](theories/PipelineCorrect.v) composes the correctness proof of the extraction pipeline 
  - [`Firstorder.v`](theories/Firstorder.v) derives interoperability results for first-order functions
- the [`plugin`](plugin) directory contains the code of the extraction plugin extracted using Rocq's OCaml extraction via [`theories/Extraction.v`](theories/Extraction.v). This is packaged into an intermediate extraction plugin.
- the [`plugin/plugin-bootstrap`](plugin/plugin-bootstrap) directory contains the code of the extraction plugin extracted using the intermediate extraction plugin. This is packaged into the final verified extraction plugin.
- the [`examples`](examples) directory contains various examples how to use the new verified extraction plugin.
- the [`benchmarks`](benchmarks) directory allows re-producing benchmarks from the paper.

## Team & Credits

The project is developed by Yannick Forster, Matthieu Sozeau, Pierre-Marie Pédrot, and Nicolas Tabareau.

```
Copyright (c) 2022--2025 Yannick Forster, Matthieu Sozeau, Nicolas Tabareau
```
