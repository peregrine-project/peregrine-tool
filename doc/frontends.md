# Peregrine frontends

A *frontend* is a tool that takes a program written in a source language (Agda, Lean, Rocq, …) and emits the S-expression format consumed by `peregrine compile`. Frontends are not part of this repository proper: each is its own project. The peregrine middle-end intentionally has nothing to say about the source language — it only sees an [S-expression-encoded `PAst`](format.md).

A frontend's job is, for a given top-level definition, to:

1. obtain a $\lambda_\square$ or $\lambda_\square^T$ AST of the definition together with its transitive dependencies, and
2. serialize that AST in the format described in [format.md](format.md) (the printer is given by `SerializePAst.string_of_PAst`).

The Rocq plugin shipped under [plugin/](/plugin/) is a *reference* frontend: it goes through MetaRocq's quoting + erasure, then through Peregrine's `SerializePAst`. The other frontends mirror the same shape in their respective ecosystems.

## Coq / Rocq (MetaCoq)

[MetaCoq](https://github.com/MetaRocq/metarocq) is a project formalizing Coq in Coq and providing tools for manipulating Coq terms and developing certified plugins. Peregrine's Rocq frontend is a small MetaCoq plugin built on top of these tools.

### Loader and entry points

The user-facing entry point lives in [`plugin/theories/Loader.v`](/plugin/theories/Loader.v):

```coq
From Peregrine Require Import Loader.

Definition add_5 (n : nat) : nat := n + 5.

(* Extract to untyped lambda box *)
Peregrine Extract "test.ast" add_5.

(* Extract to typed lambda box *)
Peregrine Extract Typed "test.ast" add_5.

(* If no path is given, the result is printed on Coq's notice channel. *)
Peregrine Extract add_5.
```

`Peregrine Extract` is implemented by the OCaml module [`g_peregrine.ml`](/plugin/src/g_peregrine.ml). It calls `Ast_quoter.quote_term_rec` to get a MetaCoq AST of the definition and its dependencies (including opaque proofs, accessed via `opaque_access`), runs the erasure, and serializes the resulting `PAst`.

### Erasure backbone

The actual erasure pipelines live in [`theories/erasure/`](/theories/erasure/) and are re-exported to OCaml via `Separate Extraction` in [`plugin/theories/ExtractPlugin.v`](/plugin/theories/ExtractPlugin.v):

* `CoqToLambdaBox.erase_untyped_past` — runs `Erasure.run_erase_only` and wraps the result as `Untyped`.
* `CoqToLambdaBox.erase_typed_past` — runs `ErasureTyped.run_typed_erase_only` and wraps it as `Typed`.
* `CoqToLambdaBox.serialize_past` — prints a `PAst` value using `SerializePAst.string_of_PAst`.

Both erasure variants reuse MetaRocq's verified pipelines: the untyped path uses `pcuic_expand_lets_transform ▷ erase_transform ▷ rebuild_env`, and the typed path uses `pcuic_expand_lets_transform ▷ typed_erase_transform`. The MetaRocq trust assumption (`assume_that_we_only_erase_on_welltyped_programs`) is inherited.

### When to skip Peregrine and use a Rocq backend directly

For programs that originate in Rocq, the typed-erasure-based backends (Rust, Elm) and the verified backends shipped by MetaRocq (OCaml/Malfunction, Wasm via CertiRocq-Wasm, C via CertiRocq) can be invoked directly inside Rocq — they are the same underlying tools that Peregrine wraps. Going through the standalone `peregrine` binary is the right choice when you want a single tool that can be driven from a build system, an Agda/Lean program, or a checked-in `.ast` file.

## Agda (agda2lambox)

[agda2lambox](https://github.com/agda/agda2lambox) is a frontend translating [Agda](https://github.com/agda/agda) programs into $\lambda_\square$ and $\lambda_\square^T$. It is shipped as a standalone executable.

Mark the definitions to translate with the `AGDA2LAMBOX` pragma:

```agda
test = ...
{-# COMPILE AGDA2LAMBOX test #-}
```

Then run

```
agda2lambox FILE              # → untyped λ_□
agda2lambox --typed --no-block FILE  # → typed λ_□^T
```

The output is the same `PAst` S-expression format consumed by `peregrine compile`. The repository's `test/agda/` directory exercises a subset of features that the Agda frontend currently supports.

## Lean (lean-to-lambox)

[lean-to-lambox](https://github.com/peregrine-project/lean-to-lambdabox) produces $\lambda_\square$ for [Lean](https://leanprover-community.github.io/) programs.

Within a Lean source file:

```
import LeanToLambdaBox

def val_at_false (f: Bool -> Nat): Nat := f .false

#erase val_at_false to "out.ast"
```

Only untyped lambda box is supported by this frontend at the moment.

## Writing a new frontend

A frontend only needs to produce a value of type `PAst` (defined in [`theories/PAst.v`](/theories/PAst.v)) and serialize it with the format in [format.md](format.md). The simplest path is:

1. Build an MetaRocq-shaped erased program (`EAst.global_context * option EAst.term` for untyped, `ExAst.global_env * option EAst.term` for typed) directly in OCaml/Haskell/your-host-language. The OCaml extraction of `PAst`/`EAst`/`ExAst` is available under [`src/extraction/`](/src/extraction/) (and in extracted form under [`hs-lib/`](/hs-lib/) for Haskell-based frontends).
2. Wrap it in `Untyped` / `Typed`.
3. Call the extracted `SerializePAst.string_of_PAst`, or write the same S-expression shape by hand (it is small and stable).

The `validate` subcommand of the CLI (`peregrine validate FILE`) parses and well-formedness-checks a candidate `.ast` file without running any backend, which is the easiest way to check that a new frontend produces a valid program.
