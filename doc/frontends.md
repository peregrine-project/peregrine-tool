# Peregrine Frontends

A *frontend* is a tool that takes a program written in a source language (general programming language or proof assistant like Agda, Lean, Rocq, …) and performs proof-erasure (for proof assistants) and translates it to $\lambda_\square$, which can be consumed by the Peregrine middle-end.

The Peregrine middle-end intentionally has nothing to say about the source language — it only sees an [S-expression-encoded `PAst`](/doc/format.md).
Frontends are not part of this repository proper: each is its own project.
Given a source file, `peregrine` runs the Rocq, Agda or Lean frontend itself; [usage.md](usage.md#frontends) describes how it invokes each one and the options it passes. This page describes the frontends themselves.

A frontend's job is, for a given top-level definition, to:

1. perform proof and type erasure and obtain a $\lambda_\square$ or $\lambda_\square^T$ AST of the definition together with its transitive dependencies
2. serialize that AST in the format described in [format.md](/doc/format.md)
3. expose options and produce a serialized configuration file as described in [format.md](/doc/format.md)

## Frontends
Peregrine comes with the Rocq, Agda and Lean frontends described below. The [SEIO\*](#f-seio) project also targets Peregrine.

### Rocq

[MetaRocq](https://github.com/MetaRocq/metarocq) is a project formalizing Rocq in Rocq and providing tools for manipulating Rocq terms and developing certified plugins. Peregrine's Rocq frontend is a small MetaRocq plugin built on top of these tools using MetaRocq's verified erasure.

The frontend located in [plugin/](/plugin/) and comes installed together with the Peregrine middle-end.
For more details on MetaRocq erasure and program extraction see [MetaRocq papers](https://github.com/MetaRocq/metarocq#papers).

The Rocq frontend supports both $\lambda_\square$ and $\lambda_\square^T$, and all Rocq language features.

#### Basic usage

```coq
From Peregrine.Plugin Require Import Loader.

(* Program that we want ot extract *)
Definition add_5 (n : nat) : nat := n + 5.

(* Extract to untyped lambda box *)
Peregrine Extract "test.ast" add_5.

(* Extract to typed lambda box *)
Peregrine Extract Typed "test.ast" add_5.
```

From the command line, `peregrine BACKEND FILE.v --entry add_5` runs the same command on `FILE.v` ([usage.md](usage.md#rocq)).



### Agda

[agda2lambox](https://github.com/agda/agda2lambox) is a frontend translating [Agda](https://github.com/agda/agda) programs into $\lambda_\square$ and $\lambda_\square^T$. It is shipped as a standalone executable.

#### Basic usage
Mark the definitions to translate with the `AGDA2LAMBOX` pragma:

```agda
test = ...
{-# COMPILE AGDA2LAMBOX test #-}
```

Then run

```
agda2lambox FILE            # → untyped λ_□
agda2lambox --typed FILE    # → typed λ_□^T
```

The output is the same `PAst` S-expression format that `peregrine` reads. `peregrine BACKEND FILE.agda` runs agda2lambox itself ([usage.md](usage.md#agda)).

#### Limitations
agda2lambox doesn't support
* Type aliases (are inlined in translation)
* Let bindings (are inlined in translation)
* Primitives
* Projection-like definitions
* Some edgecases of where clauses are not supported
* Peregrine configuration files

The agda2lambox frontend is unverified.



### Lean

[lean-to-lambox](https://github.com/peregrine-project/lean-to-lambdabox) produces $\lambda_\square$ for [Lean](https://leanprover-community.github.io/) programs.

#### Basic usage

Within a Lean source file:

```lean
import LeanToLambdaBox

def val_at_false (f: Bool -> Nat): Nat := f .false

#erase val_at_false to "out.ast"
```

`#erase` also writes `out.ast.inlinings`, an [attribute file](/doc/format.md#attribute-files) listing the constants to inline. Pass it to Peregrine with `--attributes=out.ast.inlinings`. `peregrine BACKEND FILE.lean --entry NAME` runs `#erase` itself and passes the inlinings on ([usage.md](usage.md#lean)).

#### Relation to LCNF

The frontend erases Lean's kernel terms (`Expr`) directly, with a translation adapted from Lean's `toLCNF`. It runs before Lean's LCNF pipeline, so the only Lean compiler steps it applies are matcher and `macro_inline` inlining and `csimp` replacement. The optimizations of the LCNF pipeline, such as specialization, do not apply.

#### Primitives

By default (`nat := .machine`), `Nat` literals become `primInt`, which panics on overflow, and functions marked `@[extern]`, such as `Nat.add`, become axioms that the target must implement. With `nat := .peano`, `Nat` stays an inductive.

#### Limitations

The Lean frontend doesn't support
* $\lambda_\square^T$
* String literals, or primitive floats and arrays
* Lean IO monad
* Lean Task API
* computed fields
* Writing a complete Peregrine configuration file, or attributes other than inlinings

The Lean frontend is partially verified.

### F\* (SEIO\*)

[SEIO\*](https://github.com/andricicezar/fstar-io/tree/main/seiostar) compiles $\lambda_{io}$, a small language with IO operations quoted from F\* programs, to untyped $\lambda_\square$. IO operations become constants without a body, implemented by a linked OCaml runtime. Its pipeline uses the OCaml backend of an older Peregrine, and its output has no `Untyped` constructor, which the current parser requires. Its proof of robust relational hyperproperty preservation ends at $\lambda_{io}$.



## Writing a new frontend

A frontend only needs to produce a value of type `PAst` (defined in [`theories/PAst.v`](/theories/PAst.v)) and serialize it with the format in [format.md](format.md). The simplest path is:

1. Build an MetaRocq-shaped erased program (`EAst.global_context * option EAst.term` for untyped, `ExAst.global_env * option EAst.term` for typed) directly in OCaml/Haskell/your-host-language. The OCaml extraction of `PAst`/`EAst`/`ExAst` is available under [`src/extraction/`](/src/extraction/) (and in extracted form under [`hs-lib/`](/hs-lib/) for Haskell-based frontends).
2. Wrap it in `Untyped` / `Typed`.
3. Call the extracted `SerializePAst.string_of_PAst`, or write the same S-expression shape by hand (it is small and stable).

The `validate` subcommand of the CLI (`peregrine validate FILE`) parses and well-formedness-checks a candidate `.ast` file without running any backend, which is the easiest way to check that a new frontend produces a valid program.
