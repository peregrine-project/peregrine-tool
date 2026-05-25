# Feature support

This page summarises which language features are currently supported by each Peregrine frontend and backend. "Supported" means the feature actually round-trips through the pipeline; "TODO" means the underlying machinery is present but no glue is wired up yet (see [tasks.md](tasks.md)).

## Backend feature matrix

| Feature                         | Rust          | Elm           | C   | Wasm | OCaml | CakeML | Eval | AST |
|---------------------------------|---------------|---------------|-----|------|-------|--------|------|-----|
| AST input                       | $\lambda_\square^T$ | $\lambda_\square^T$ | $\lambda_\square$ | $\lambda_\square$ | $\lambda_\square$ | $\lambda_\square$ | $\lambda_\square$ | both |
| Verified printer                | ✗             | ✗             | ✓ (via CertiRocq) | ✓ (via CertiRocq-Wasm) | ✓ (via Malfunction)\* | ✗ | n/a | ✓ |
| Top-level term required         | optional      | optional      | required | required | required | required | required | depends on `ast_type` |
| `implement_box`                 | optional, default off | optional, default off | required | required | required | required | required | optional |
| `implement_lazy`                | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional |
| `cofix_to_lazy`                 | optional      | optional      | optional | optional | optional | optional | optional | optional |
| `betared` / `unboxing`          | optional      | optional      | optional | optional | optional (`unboxing` defaults on) | optional (`unboxing` defaults on) | off by default | off by default |
| `dearg_ctors` / `dearg_consts`  | default on    | default on    | default on | default on | default on | default on | off by default | off by default |
| Constant remapping (symbol)     | ✓             | ✓             | ✓ (CertiRocq primitives) | ✓ (CertiRocq primitives) | ✓ (Malfunction `Global`) | ✗ | ✓ | n/a |
| Constant remapping (inline)     | ✓             | TODO          | ✗ | ✗ | TODO | ✗ | ✗ | n/a |
| External libraries (`re_const_ext`) | TODO     | TODO          | ✓ (collected as `#include`s) | ✗ | TODO | ✗ | ✗ | n/a |
| Constant remapping (GC)         | n/a           | n/a           | ✓ (`re_const_gc`) | ✓ (`re_const_gc`) | n/a | n/a | n/a | n/a |
| Inductive remapping (`StringIndRemap`) | ✓     | TODO          | n/a (untyped) | n/a (untyped) | n/a (untyped) | n/a (untyped) | n/a | n/a |
| Inductive remapping (`KnIndRemap`) | n/a (typed) | n/a (typed)   | ✓ | ✓ | ✓ | ✓ | ✓ | n/a |
| Constructor reordering (`cstr_reorders`) | ✓   | ✓             | ✓ | ✓ | ✓ | ✓ | ✓ | optional |
| Custom inductive attributes     | ✓ (Rust derives) | ✗          | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ |
| Identifier sanitization         | `rust_sanitizer` (full XID, keyword-aware) | `ocaml_sanitizer` | `ocaml_sanitizer` | `ocaml_sanitizer` | `ocaml_sanitizer` | `ocaml_sanitizer` | skip | skip |
| Primitive integers (`tPrim primInt`) | inherited from typed printer | inherited | ✓ via CertiRocq | ✓ via CertiRocq | ✓ via Malfunction | ✓ | ✓ | ✓ |
| Primitive floats / strings      | TODO          | TODO          | TODO (CertiRocq dependent) | TODO | TODO | TODO | TODO | ✓ (preserves them in dump) |
| Primitive arrays                | TODO          | TODO          | TODO | TODO | TODO | TODO | TODO | ✓ |
| `tLazy` / `tForce`              | ✗ (use `implement_lazy`) | ✗ | ✗ (use `implement_lazy`) | ✗ | ✗ | ✗ | ✗ | ✓ |
| Output                          | `.rs` (multiple lines) | `.elm` (single module) | `.c` + `.h` | `.wasm` (binary) | `.mlf` (Malfunction) | `.cml` | stdout | `.ast` (S-expr) |

\* The OCaml backend relies on `Axiom trust_coq_kernel` to discharge the Malfunction pipeline's preconditions; this matches the upstream coq-verified-extraction trust assumption.

A "TODO" entry corresponds to a marker in the source code of the relevant backend (`theories/backends/<Name>Backend.v`). The general items from [tasks.md](tasks.md) — primitive support, inlining, remapping of Agda stdlib types, separate extraction, reserved-keyword checking and identifier validation — apply across the matrix.

## Frontend feature matrix

| Feature                         | Rocq (Peregrine plugin) | Agda (agda2lambox) | Lean (lean-to-lambox) |
|---------------------------------|-------------------------|--------------------|------------------------|
| Untyped $\lambda_\square$       | ✓ (`Peregrine Extract`) | ✓ (`agda2lambox`)  | ✓ (`#erase`)           |
| Typed $\lambda_\square^T$       | ✓ (`Peregrine Extract Typed`) | ✓ (`--typed --no-block`) | ✗ |
| Inductive types                 | ✓                       | ✓                  | ✓                      |
| Mutual inductives               | ✓                       | ✓                  | inherits Lean's frontend treatment |
| Co-inductive types              | ✓ (via MetaRocq erasure) | inherits Agda | depends on Lean's elaborator |
| Records / projections           | ✓                       | ✓                  | ✓                      |
| `Prop`/erased terms             | ✓ (erased to `tBox`)    | ✓                  | ✓                      |
| Primitive integers              | ✓                       | partial            | partial                |
| Primitive floats                | ✓                       | TODO               | TODO                   |
| Primitive strings               | ✓ (via `PrimString`)    | TODO               | TODO                   |
| Primitive arrays                | ✓                       | TODO               | TODO                   |
| Opaque proofs                   | ✓ (`tmQuoteRecTransp` with `opaque_access`) | n/a | n/a |
| Identifier handling             | MetaRocq kernames preserved | Agda qualified names | Lean kernames |

The Rocq plugin reuses MetaRocq end-to-end and therefore tracks MetaRocq's coverage closely; gaps usually correspond to features that MetaRocq itself does not yet erase. The Agda and Lean frontends live in their own repositories — file feature requests there.

## Trust assumptions

In addition to the trust placed in the source toolchains, Peregrine's middle-end relies on:

* MetaRocq's erasure correctness (assumed for `assume_that_we_only_erase_on_welltyped_programs`).
* The `trust_coq_kernel` axiom used by the OCaml and CakeML backends, discharging the Malfunction-pipeline preconditions exactly as in coq-verified-extraction.
* Two `Admitted` obligations on the `implement_box` and `implement_lazy_force` transformations in [`theories/erasure/Transforms.v`](/theories/erasure/Transforms.v); these establish observational equivalence between the source and target evaluations and are part of the ongoing verification work.
* For Rust/Elm output, the *printer* itself is unverified (`TypedExtraction.RustExtract`/`ElmExtract`). Everything before the printer is verified.

See [notes.md](notes.md) for additional context.
