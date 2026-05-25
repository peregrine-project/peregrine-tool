# Project structure

The repository is a Rocq plugin + extracted OCaml CLI. The Rocq side defines the verified middle-end (S-expression parsers/printers, well-formedness checking, name sanitization, the erasure transforms, and the backend drivers). The OCaml side glues everything together as a `cmdliner`-based binary.

## Directory layout

| Path | Contents |
|------|----------|
| [`theories/`](/theories/) | Rocq sources for the extraction pipeline. See [Rocq sources](#rocq-sources) below for a per-file breakdown. |
| [`theories/serialization/`](/theories/serialization/) | S-expression serialization of $\lambda_\square$ programs and Peregrine configurations. The `Serialize*` modules print, the `Deserialize*` modules parse, and the `Serialize*Sound`/`Serialize*Complete` modules carry the round-trip lemmas. |
| [`theories/backends/`](/theories/backends/) | One Rocq module per target language; each exposes `default_<name>_config`, `<name>_phases`, and an `extract_<name>` entry point used by `theories/Pipeline.v`. |
| [`theories/erasure/`](/theories/erasure/) | Wrappers around MetaRocq's erasure passes. `Erasure.v` is the untyped pipeline, `ErasureTyped.v` the typed one, `Transforms.v` defines the optional Peregrine-specific phases, and `EImplementLazyForce.v` implements the `tLazy`/`tForce` lowering. |
| [`plugin/`](/plugin/) | The `Peregrine Extract` Rocq plugin (MetaRocq-based) and its extraction. Built separately with `make plugin`. |
| [`src/extraction/`](/src/extraction/) | OCaml code extracted from `theories/Extraction.v` (overwritten on every `make`). |
| [`src/printC/`](/src/printC/) | OCaml library for printing Clight, vendored from [CertiRocq](https://github.com/CertiRocq/certirocq/tree/master/plugin/static). |
| [`bin/`](/bin/) | OCaml sources defining the `peregrine` command-line interface: `main.ml` wires up `cmdliner`, `compile.ml` invokes the extracted middle-end, `common.ml` defines shared option records. |
| [`hs-lib/`](/hs-lib/) | Haskell extraction of the middle-end, for frontends that prefer to drive Peregrine from Haskell. Built with `make hs-lib`. |
| [`test/`](/test/) | Test suite and TypeScript-based runner. Sub-directories: `test/rocq` for Rocq programs that are extracted and exercised, `test/lean` for Lean programs (compiled with `lean-to-lambox`), `test/agda/` for Agda fixtures (compiled with `agda2lambox`), and `test/src/` for the per-backend test drivers. |

## Rocq sources

The complete dependency order is in [`_CoqProject`](/_CoqProject). The most important entry points:

* [`theories/PAst.v`](/theories/PAst.v) — defines `PAst`, the tagged union of untyped (`EAst.global_context * option EAst.term`) and typed (`ExAst.global_env * option EAst.term`) programs that all frontends produce. Also provides the projections used by backends to drop down to `EAst.program` / `ExAst.global_env`.
* [`theories/Config.v`](/theories/Config.v) — the canonical definition of every configuration record used by the pipeline (general config, backend configs, erasure-phases table, remappings, custom attributes). See [format.md](format.md) for the full S-expression encoding.
* [`theories/ConfigUtils.v`](/theories/ConfigUtils.v) — the *optional* mirror of `Config.v` (`<record>'` types where every defaultable field is wrapped in `option`), the `mk_<record>` functions that fill defaults, and `merge_attributes_config` for combining a base config with `--attributes` files.
* [`theories/Pipeline.v`](/theories/Pipeline.v) — the top-level entry points `peregrine_pipeline` and `peregrine_validate`. Drives parse → well-formedness check → backend-compatibility check → name sanitization → optional transforms → backend dispatch.
* [`theories/CheckWf.v`](/theories/CheckWf.v) — checks both `EAst` and `ExAst` programs against `EWellformed.all_env_flags` and produces a human-readable error when something fails.
* [`theories/NameSanitize.v`](/theories/NameSanitize.v) — per-target identifier sanitizers. Each backend picks one via `get_sanitizer`; sanitization runs over both the AST and the configuration before transforms.
* [`theories/Unicode.v`](/theories/Unicode.v), [`theories/UnicodeXID.v`](/theories/UnicodeXID.v) — UTF-8 handling and the Unicode XID tables (needed by the Rust sanitizer).
* [`theories/EvalBox.v`](/theories/EvalBox.v) — the in-process evaluator used by `peregrine eval`.
* [`theories/CoqToLambdaBox.v`](/theories/CoqToLambdaBox.v) — the helper functions invoked by the Rocq plugin (`erase_untyped_past`, `erase_typed_past`, `serialize_past`).
* [`theories/Extraction.v`](/theories/Extraction.v) — `Separate Extraction` directives that produce `src/extraction/`.

## Build system

The top-level [`Makefile`](/Makefile) wires together three build steps:

```text
make            ≡  make theory && make mllib && make plugin
make theory     →  rocq makefile -f _CoqProject -o RocqMakefile && make -f RocqMakefile
make mllib      →  dune build           (builds the extracted CLI from src/extraction/)
make plugin     →  make -C plugin       (builds the MetaRocq plugin)
make hs-lib     →  make -C hs-lib       (optional Haskell extraction)
make test       →  make -C test test    (runs the cross-language test runner)
make install    →  installs Rocq theories, dune library, and plugin
make clean      →  full clean, including regenerated files under src/extraction/
```

Unknown targets are forwarded to the generated `RocqMakefile`, so `make all`, `make Pipeline.vo`, etc. work as expected.

## Dev environment setup

```bash
git clone https://github.com/peregrine-project/peregrine-tool.git
cd peregrine-tool
opam switch create . 4.14.2 --repositories default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
opam install . --deps-only
```

The project can then be built with `make`. The dev CLI is launched with `dune exec peregrine -- <ARGS>`.

For interactive development the usual workflow is:

* iterate on Rocq files under `theories/`, rebuilding with `make theory`;
* re-run extraction + CLI with `make mllib` (or `make` for a full rebuild including the plugin);
* exercise an end-to-end run with `dune exec peregrine -- <target> path/to/prog.ast -o out`.

## Running the test suite

The test suite is a TypeScript runner that drives `peregrine` against pre-extracted Rocq, Lean, and Agda fixtures, compiles the output with the relevant external tool, and checks the result. From the repo root:

```bash
make test       # or: cd test && npm install && npm run test
```

Prerequisites (see [`test/README.md`](/test/README.md)):

* Node.js v22 or later, with `npm`,
* `cargo` and `rustc` (Rust backend),
* the [Elm compiler](https://elm-lang.org/) and `elm-test` (Elm backend),
* `gcc` (C backend),
* `wasmtime` (Wasm backend),
* `malfunction` (OCaml backend).

Inputs live as `*.ast` (untyped) and `*.tast` (typed) files. The Agda fixtures are imported from [`agda2lambox`](https://github.com/agda/agda2lambox/tree/master/test); see `test/README.md` for the regeneration recipe.

# Coq Extractions

## Pipeline

![extraction](pipeline.png)

The picture corresponds to the `peregrine_pipeline` function in [`theories/Pipeline.v`](/theories/Pipeline.v):

1. `parse_ast` — parse the input file as a `PAst` (`DeserializePAst.v`).
2. `get_config` — parse the configuration file as `config'` (`DeserializeConfig.v`) and merge any `--attributes` files via `merge_attributes_config`.
3. `check_wf` — well-formedness check against MetaRocq's `EWellformed.all_env_flags`.
4. `validate_ast_type` — verifies that the AST shape (typed/untyped) is compatible with the selected backend (`Rust`/`Elm`/`AST LambdaBoxTyped` require typed; others accept either).
5. `sanitize_PAst` / `sanitize_config` — rewrite identifiers through the backend-specific `get_sanitizer`.
6. `apply_transforms` — run `run_untyped_transforms`, `run_typed_transforms`, or `run_typed_to_untyped_transforms` (in `theories/erasure/Transforms.v`) depending on the AST kind and on `needs_typed c`.
7. `run_backend` — dispatch to the chosen `extract_<name>` function.

## Translations

* Coq -> $\lambda_{CIC}$
  * Quote function (Coq -> Coq AST) implemented in OCaml: https://github.com/MetaCoq/metacoq/blob/coq-8.20/template-coq/src/run_template_monad.ml#L442
  * Translation from Coq AST -> $\lambda_{CIC}$: https://github.com/MetaCoq/metacoq/blob/coq-8.20/template-pcuic/theories/TemplateToPCUIC.v
  * Coq AST definition: https://github.com/MetaCoq/metacoq/blob/coq-8.20/template-coq/theories/Ast.v
  * $\lambda_{CIC}$ definition: https://github.com/MetaCoq/metacoq/blob/coq-8.20/pcuic/theories/PCUICAst.v
* $\lambda_{CIC}$ -> $\lambda_{\square}$
  * Translation: https://github.com/MetaCoq/metacoq/blob/coq-8.20/erasure-plugin/theories/ETransform.v
  * $\lambda_{\square}$ definition: https://github.com/MetaCoq/metacoq/blob/coq-8.20/erasure/theories/EAst.v
* $\lambda_{CIC}$ -> $\lambda_{\square}^T$
  * Translation: https://github.com/MetaCoq/metacoq/blob/coq-8.20/erasure/theories/Typed/Erasure.v#L1505
  * $\lambda_{\square}^T$ definition: https://github.com/MetaCoq/metacoq/blob/coq-8.20/erasure/theories/Typed/ExAst.v
* $\lambda_{\square}$ -> $\lambda_{ANF}$
  * https://github.com/CertiRocq/certirocq/wiki/The-CertiRocq-pipeline
  * AST: https://github.com/CertiRocq/certirocq/blob/master/theories/LambdaANF/cps.v
* $\lambda_{\square}^T$ -> Rust
  * Printing: https://github.com/peregrine-project/rocq-typed-extraction/blob/master/elm/theories/RustExtract.v
* $\lambda_{\square}^T$ -> Elm
  * Printing: https://github.com/peregrine-project/rocq-typed-extraction/blob/master/rust/theories/ElmExtract.v
* $\lambda_{ANF}$ -> Clight
* $\lambda_{ANF}$ -> WASM
  * https://github.com/womeier/certicoqwasm/blob/master/theories/CodegenWasm/LambdaANF_to_Wasm.v

## Examples

* Rust
  * https://github.com/peregrine-project/rocq-typed-extraction/tree/master/tests/theories
* Elm
  * https://github.com/peregrine-project/rocq-typed-extraction/tree/master/tests/theories
* WASM
  * https://github.com/womeier/certicoqwasm-testing
* C (Clight)
  * https://github.com/CertiRocq/certirocq/blob/master/benchmarks/tests.v
