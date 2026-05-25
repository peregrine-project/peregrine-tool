# Peregrine backends

Peregrine compiles a $\lambda_\square$ or $\lambda_\square^T$ program down to one of several target languages. The choice of target is encoded in the `backend_config` field of the [configuration](format.md). Each backend is implemented as a small Rocq module under [theories/backends/](/theories/backends/) that exposes three things:

* `default_<name>_config` — the values used when the corresponding configuration fields are omitted.
* `<name>_phases` — declares, for each optional erasure pass (`implement_box`, `implement_lazy`, `cofix_to_lazy`, `betared`, `unboxing`, `dearg_ctors`, `dearg_consts`), whether it is `Required`, `Incompatible`, or `(Compatible <default>)` for the backend. The user-facing `erasure_phases` is reconciled against this table by `enforce_phases` (in [`ConfigUtils.v`](/theories/ConfigUtils.v)).
* `extract_<name>` — the actual extraction function, called by `run_backend` in [`Pipeline.v`](/theories/Pipeline.v).

The pipeline runs in this order (see `peregrine_pipeline`):

1. parse the AST and the configuration;
2. check that the AST is well-formed (`CheckWf.v`);
3. check that the AST kind is compatible with the chosen backend (e.g. Rust/Elm require `Typed`, see `validate_ast_type`);
4. sanitize identifiers via a backend-specific `get_sanitizer` (see [`NameSanitize.v`](/theories/NameSanitize.v));
5. run the backend's preferred erasure/optimization passes (`apply_transforms` in [`Pipeline.v`](/theories/Pipeline.v));
6. dispatch to the backend's `extract_*` function.

The table below summarises which AST shape each backend consumes and which sanitizer it uses.

| Backend | Source       | Driver                                                | Sanitizer |
|---------|--------------|-------------------------------------------------------|-----------|
| Rust    | $\lambda_\square^T$ | TypedExtraction's `RustExtract`                | `rust_sanitizer` |
| Elm     | $\lambda_\square^T$ | TypedExtraction's `ElmExtract`                 | `ocaml_sanitizer` (Elm rules ≈ OCaml) |
| C       | $\lambda_\square$   | CertiRocq pipeline → Clight                    | `ocaml_sanitizer` |
| Wasm    | $\lambda_\square$   | CertiRocq pipeline → CertiCoq-Wasm             | `ocaml_sanitizer` |
| OCaml   | $\lambda_\square$   | MetaRocq's verified Malfunction pipeline       | `ocaml_sanitizer` |
| CakeML  | $\lambda_\square$   | MetaRocq pipeline + CakeML serializer          | `ocaml_sanitizer` |
| Eval    | $\lambda_\square$   | CertiRocq evaluator (ANF or LambdaBoxMut)      | none |
| AST     | either              | dump an intermediate representation            | none |

Identifier sanitization happens *before* the backend's transforms run, so users never need to encode target-language naming rules in their input programs.

## Rust

The Rust backend lives in [`theories/backends/RustBackend.v`](/theories/backends/RustBackend.v) and reuses the unverified printer from [`peregrine-project/rocq-typed-extraction`](https://github.com/peregrine-project/rocq-typed-extraction) (`TypedExtraction.RustExtract`).

Input
* Requires a typed environment (`Typed ...`); a `LambdaBox` input is rejected by `validate_ast_type`.

Configuration ([`rust_config`](/theories/Config.v))
* `rust_preamble_top` / `rust_preamble_program` are concatenated onto Peregrine's built-in preambles (allow-lints + `hint_app` at module level, the bumpalo `alloc`/`closure` helpers at program level).
* The three box symbols (`rust_term_box_symbol`, `rust_type_box_symbol`, `rust_any_type_symbol`) replace erased terms, erased types, and `Any` types respectively in the printer.
* `rust_print_full_names` toggles fully-qualified names.
* `rust_default_attributes` is the derive attribute prepended to each generated `enum`/`struct`. A per-inductive override can be supplied via `custom_attributes_opts` in the general config (`mk_attributes` in `RustBackend.v`).

Erasure defaults — `Compatible false` for everything except `dearg_ctors` and `dearg_consts`, which default to `true`. Implementing boxes/lazy is unnecessary because the typed pipeline keeps the box markers and Rust represents them directly with the configured symbols.

Remapping
* Constant remapping uses `re_const_inl` to choose between an inline remap (`remap_inline_constant`) and a remap-to-symbol (`remap_constant`). The external-symbol field (`re_const_ext`) is currently unused (TODO in the source).
* Only `StringIndRemap` entries are honored for inductive remapping; `KnIndRemap` entries are skipped.

Output
* A list of strings; written to `<file>.rs` by the CLI.
* The generated Rust depends on [bumpalo](https://docs.rs/bumpalo/) v3 or later.

## Elm

Implemented in [`theories/backends/ElmBackend.v`](/theories/backends/ElmBackend.v); printer from `TypedExtraction.ElmExtract`.

Input — requires a typed AST.

Configuration ([`elm_config`](/theories/Config.v))
* The output module declaration is `module <elm_module_name> exposing (..)`. When `elm_module_name` is `None`, the input file's basename is used.
* `elm_preamble` is inserted after the module header.
* `elm_false_elim_def` provides the definition for the `false_rec` shim used when eliminating from `False`.
* Box-symbol fields mirror their Rust counterparts.

Erasure defaults — same as Rust.

Remapping — only `re_const_s` is honored for constant remapping; inline/external/inductive remapping are TODOs in the source. The Elm sanitizer reuses `ocaml_sanitizer`.

Output
* A single string; written to `<file>.elm` by the CLI.
* The result has no external dependencies and is compiled with the [Elm compiler](https://guide.elm-lang.org/install/elm).

## C (Clight)

Implemented in [`theories/backends/CBackend.v`](/theories/backends/CBackend.v); built on top of the shared CertiRocq driver in [`CertiRocqBackend.v`](/theories/backends/CertiRocqBackend.v) which wires the user's `certirocq_config` and constant remappings into CertiRocq's `Options` and `primitives`. The actual pipeline (`anf_pipeline compile_Clight`) goes
$\lambda_\square \;\to\; \text{LambdaBoxMut} \;\to\; \text{LambdaBoxLocal} \;\to\; \text{LambdaANF} \;\to\; \text{Clight}$.

Input — accepts both AST variants; typed ASTs are first dropped down to untyped by `apply_transforms`.

Configuration ([`c_config = certirocq_config`](/theories/Config.v))
* `direct` controls direct-style vs CPS lowering; the CLI flag `--cps` sets this to `false`.
* `c_args`, `o_level`, `anf_conf`, `prefix`, `body_name` are passed verbatim to CertiRocq.

Erasure defaults — `implement_box` is `Required` (CertiRocq's $\lambda_\square$ frontend does not handle boxes), the lazy/cofix/betared/unboxing passes default off, and the deargers default on.

Remapping — constant remappings are turned into CertiRocq `primitives` (with `re_const_arity` and `re_const_gc`). The `re_const_ext` field of each entry collects header names to `#include`; the GC header (`gc_stack.h` for direct style, `gc.h` for CPS) is added automatically. Inductive remappings and inline remappings are not used by this backend.

Output — a CertiRocq `Cprogram` paired with the list of imports. The CLI writes a `.c` file plus a `.h` header; the C must be linked against the CertiRocq runtime and glue code (see the [CertiRocq plugin docs](https://github.com/CertiRocq/certirocq/wiki/The-CertiRocq-plugin#compiling-the-generated-c-code)). The C output can then be compiled with [CompCert](https://compcert.org/) or any standard C compiler.

## WebAssembly

Implemented in [`theories/backends/WasmBackend.v`](/theories/backends/WasmBackend.v). Uses [CertiRocq-Wasm](https://github.com/womeier/certicoqwasm), which extends CertiRocq with a $\lambda_{ANF} \to \text{WebAssembly}$ codegen.

Input/Configuration — identical to the C backend (`wasm_config = certirocq_config`, `wasm_phases = c_phases` modulo defaults). The CLI flag `--cps` likewise toggles `direct`.

Erasure defaults — same as C.

Remapping — constant remappings are passed as CertiRocq `primitives`. Headers from `re_const_ext` are ignored (Wasm has no preprocessor); inductive and inline remappings are not used.

Output — a string containing the binary-encoded Wasm module (`Wasm.binary_format_printer.binary_of_module`). The CLI writes a `.wasm` file. The module exports the main function as `main_function`; it must be executed by a Wasm engine that supports the [tail-call extension](https://webassembly.org/features/) (e.g. recent Node.js, Wasmtime, modern browsers).

## OCaml (Malfunction)

Implemented in [`theories/backends/OCamlBackend.v`](/theories/backends/OCamlBackend.v). Reuses the verified Malfunction pipeline from [coq-verified-extraction](https://github.com/yforster/coq-verified-extraction).

Pipeline
```
enforce_extraction_conditions
  ▷ name_annotation
  ▷ compile_to_malfunction
```
Pre/post obligations are admitted via the `trust_coq_kernel` axiom; this is the same trust assumption used upstream.

Input — accepts both AST variants; typed input is downgraded first.

Configuration ([`ocaml_config`](/theories/Config.v))
* `program_type` is one of `Standalone` or `(Shared_lib <module-name> <reexports>)`, forwarded to the Malfunction printer.

Erasure defaults — `implement_box` is `Required`; `unboxing`, `dearg_ctors`, `dearg_consts` default on.

Remapping — constant remappings are translated to Malfunction `Global` references using `split_name` on `re_const_s`. Other remapping fields are not used (Malfunction primitives `Primitive`/`Erased` are TODOs).

Output — a pair `(<list of binding names>, <Malfunction source>)`. The CLI writes a `.mlf` file containing the source; it is compiled with the [malfunction](https://github.com/stedolan/malfunction) tool.

## CakeML

Implemented in [`theories/backends/CakeMLBackend.v`](/theories/backends/CakeMLBackend.v). Uses the same erasure prefix as the OCaml backend (`enforce_extraction_conditions ▷ name_annotation ▷ compile_to_malfunction`) and serializes the result through the CakeML backend's pretty-printer.

Configuration — `cakeml_config = unit`; nothing is user-tunable.

Erasure defaults — match the OCaml backend: `implement_box` is `Required`, `unboxing`/`dearg_ctors`/`dearg_consts` default on.

Output — a pair `(<list of names>, <CakeML source>)`. The CLI writes a `.cml` file.

## Eval (in-process evaluator)

Implemented in [`theories/backends/EvalBackend.v`](/theories/backends/EvalBackend.v); used by `peregrine eval`. Runs the program through the C-pipeline prefix and then evaluates it inside Rocq.

Configuration ([`eval_config`](/theories/Config.v))
* `copts : certirocq_config` — drives the C-pipeline prefix (in particular `direct` controls ANF vs CPS).
* `fuel : nat` — bound on reduction steps; the CLI default is `10000` (`mk_eval_config`'s default is `2^14`).
* `eval_anf : bool` — `true` runs the ANF evaluator (`eval_anf_pipeline`); `false` stops earlier at LambdaBoxMut and runs `eval_mut`.

Erasure defaults — `implement_box` is `Required`; all other phases default off (the evaluator runs on the raw program).

Output — a string containing the printed value. The CLI prints it on stdout.

## AST (intermediate dump)

Implemented in [`theories/backends/ASTBackend.v`](/theories/backends/ASTBackend.v); used by `peregrine ast`. Useful for debugging the pipeline and for inspecting CertiRocq's intermediate languages.

Configuration ([`ast_config`](/theories/Config.v))
* `ast_type : ASTType` selects which IR to dump:
  * `LambdaBox` — re-prints the (sanitized, transformed) input as a `PAst` S-expression.
  * `LambdaBoxTyped` — same but for typed inputs (requires a `Typed` AST).
  * `(LambdaBoxMut <certirocq_config>)` — runs the C pipeline up to CertiRocq's LambdaBoxMut and prints it.
  * `(LambdaBoxLocal <certirocq_config>)` — continues through to LambdaBoxLocal.
  * `(LambdaANF <certirocq_config>)` — runs the full ANF pipeline (including the final cleanup) and dumps the result.
  * `(LambdaANFC <certirocq_config>)` — like `LambdaANF` but skips the final ANF→ANF cleanup transformation, useful for inspecting the raw ANF.

Erasure defaults — every phase defaults to `Compatible false`, so by default no transformation is applied before the dump.

Output — a single string written by the CLI to `<file>.ast` (default extension is preserved across IR choices).
