# Design notes

A grab-bag of notes about the parts of the codebase that are not obvious from the source. Read this alongside [dev.md](dev.md) and [format.md](format.md).

## Trust assumptions

Peregrine inherits MetaRocq's verification but adds a small number of trust assumptions of its own:

* **`Axiom trust_coq_kernel`** appears in both [`OCamlBackend.v`](/theories/backends/OCamlBackend.v) and [`CakeMLBackend.v`](/theories/backends/CakeMLBackend.v). It discharges the precondition of the Malfunction `compile_to_malfunction` pipeline; this matches the trust assumption used by [coq-verified-extraction](https://github.com/yforster/coq-verified-extraction) upstream. Effectively, we trust that the Rocq kernel only feeds us well-formed programs.
* **`Admitted` obligations.** Two preservation obligations are left admitted on the optional `implement_box_transformation` and `implement_lazy_force_transformation` in [`theories/erasure/Transforms.v`](/theories/erasure/Transforms.v). These establish observational equivalence between the source and target evaluations of `EImplementBox.implement_box` and `EImplementLazyForce.implement_lazy_force`; finishing these proofs is part of the ongoing verification work. The OCaml and CakeML backends additionally admit the second `Final Obligation` of their respective Malfunction pipeline assemblies, mirroring the same pattern.
* **`assume_that_we_only_erase_on_welltyped_programs`** — MetaRocq's standard assumption, inherited by both the untyped and typed erasure entry points (`run_erase_only`, `run_typed_erase_only`).
* **Unverified printers.** The Rust and Elm backends end with a pretty-printer from [`rocq-typed-extraction`](https://github.com/peregrine-project/rocq-typed-extraction), which is not verified. Everything before the printer (typed erasure, dearging, etc.) is.

## Serializer/deserializer correctness

The serialization layer is set up to support a full round-trip proof:

* For every `Serialize_X` instance there is (or will be) a matching `Deserialize_X`.
* `theories/serialization/SerializeSound.v` and `SerializeComplete.v` group the round-trip lemmas at the program level; per-section lemmas live in `Serialize<Topic>Sound.v` / `Serialize<Topic>Complete.v` files.
* "Verifying serialization" is still listed in [tasks.md](tasks.md) — not every lemma is closed yet, but the file skeleton anticipates the completion.

The format itself is described in [format.md](format.md) and intentionally mirrors the constructor names from `EAst`/`ExAst` so that the printer/parser pair can be derived more or less mechanically.

## Identifier sanitization

Sanitization happens *before* the backend transforms run (`peregrine_pipeline` in [`Pipeline.v`](/theories/Pipeline.v)):

```
sanitize_PAst   → rewrites every name in the AST
sanitize_config → rewrites every name appearing in remappings/custom-attributes
```

The sanitizer is chosen by `NameSanitize.get_sanitizer` based on the backend. The C, Wasm, OCaml, CakeML and Elm sanitizers are all `ocaml_sanitizer` (escape non-`[A-Za-z0-9_']` characters, prefix with `_` if the result starts with a digit). The Rust sanitizer is more elaborate: it operates at the UTF-8 codepoint level, uses the Unicode XID tables in [`UnicodeXID.v`](/theories/UnicodeXID.v), recognises Rust's full reserved-keyword set (`is_rust_keyword` / `is_forbidden_rust_keyword` in [`NameSanitize.v`](/theories/NameSanitize.v)), and prefixes a discriminator codepoint when necessary. The `Eval` and `AST` backends skip sanitization (the names are not consumed by a target compiler).

Because sanitization rewrites both the AST and the configuration, kernames given as keys in `const_remappings_opts`, `ind_remappings_opts`, etc. should be written using the *unsanitized* MetaRocq names — Peregrine takes care of matching them against the sanitized AST.

## Erasure phases

The seven optional phases in `erasure_phases` correspond to MetaRocq passes. They are intentionally exposed as user toggles because the right setting depends on the target:

| Phase            | What it does                                                        | Where |
|------------------|---------------------------------------------------------------------|-------|
| `implement_box`  | Inlines `tBox` and rewrites `tCase`/projections accordingly         | `EImplementBox` in MetaRocq, wrapped by `implement_box_transformation` in `Transforms.v` |
| `implement_lazy` | Lowers `tLazy`/`tForce` and (with `cofix_to_lazy`) co-fixpoints     | `theories/erasure/EImplementLazyForce.v` |
| `cofix_to_lazy`  | Translates `tCoFix` to `tLazy` thunks                               | MetaRocq |
| `betared`        | Beta-reduce `(λx.t) u`                                              | MetaRocq's `EBeta` |
| `unboxing`       | Singleton-constructor unboxing                                      | MetaRocq |
| `dearg_ctors`    | Remove erased arguments from constructors                            | MetaRocq's typed `Optimize` (dearger) |
| `dearg_consts`   | Remove erased arguments from constants                              | MetaRocq's typed `Optimize` (dearger) |

Each backend declares an `<name>_phases : erasure_phases_config` with one of three values per phase: `Required`, `Incompatible`, or `(Compatible <default>)`. The reconciliation logic in `ConfigUtils.enforce_phases` makes `Required`/`Incompatible` non-negotiable; `Compatible` lets the user override the default. See [backends.md](backends.md) for the per-backend tables.

## Configuration "optional" layer

`Config.v` defines the *final* configuration records (every field mandatory). `ConfigUtils.v` mirrors each record with a `'`-suffixed version where every defaultable field is wrapped in `option`. The deserializer parses into the `'` layer; `mk_<record>` then fills missing fields from the backend's `default_<name>_config`.

This is the only place where defaulting happens — Peregrine does not silently fall back to "anything reasonable" later in the pipeline. If a config field is non-`None` in the parsed `config'`, it survives unchanged into the `config` consumed by `run_backend`.

## CLI ↔ middle-end

The OCaml CLI in [`bin/`](/bin/) builds a `config'` programmatically (via `compile.ml`) for the per-target commands (`peregrine rust`, `peregrine wasm`, etc.), or reads a full config file for `peregrine compile`. Either way the result is fed to the extracted `Pipeline.peregrine_pipeline`, and the result type (`extracted_program`) tells the OCaml side how to write the output (`write_program`):

* `RustProgram (list string)` → write as `.rs`.
* `ElmProgram string` → write as `.elm`.
* `CProgram ((nenv,header) * prg * libs)` → write `.c` + `.h` with the printed Clight from [`src/printC/`](/src/printC/).
* `WasmProgram string` → write the binary as `.wasm`.
* `OCamlProgram (names * source)` → write `.mlf` (Malfunction source).
* `CakeMLProgram (names * source)` → write `.cml`.
* `EvalProgram string` → print on stdout (no output file).
* `ASTProgram string` → write `.ast` (S-expression intermediate).

## Planned extensions

Aspirational items currently tracked in [tasks.md](tasks.md):

* Closing remaining `Admitted` obligations in `theories/erasure/Transforms.v`.
* Finishing the serialization soundness/completeness proofs.
* Wiring up primitive arrays/floats/strings end-to-end (the format already supports them; some backends still need to thread them through).
* Adding `Lean -> λANF` as a more direct alternative to the current `Lean -> λ□` frontend.
* Adding F\* as a frontend.
* Verified Haskell backends (GHC core), verified Scheme/OCaml replacements for Coq's built-in extraction, and possibly TypeScript/JavaScript backends.
