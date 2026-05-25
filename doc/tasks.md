# Tasks

In-progress and planned work, grouped by area. Pointers reference the file (and, where useful, the specific construct) where the work needs to land.

## Verification

* **Close `Admitted` obligations.** Two preservation obligations on `implement_box_transformation` and `implement_lazy_force_transformation` are admitted in [`theories/erasure/Transforms.v`](/theories/erasure/Transforms.v). Three further obligations (the `dearging_transform_mapping` precondition for `EReorderCstrs.wf_inductives_mapping`) are admitted with the note "assumed for now, check_wf should ensure this".
* **Verify serialization.** The `Serialize*Sound` / `Serialize*Complete` files under [`theories/serialization/`](/theories/serialization/) lay out the round-trip lemmas; not every section is closed yet.
* **Discharge the `trust_coq_kernel` axioms** in [`OCamlBackend.v`](/theories/backends/OCamlBackend.v) and [`CakeMLBackend.v`](/theories/backends/CakeMLBackend.v) once the Malfunction pipeline's preconditions can be proven instead of assumed.

## Pipeline coverage

* **Integrate MetaCoq's erasure passes into the pipeline.** Surface every remaining optional MetaRocq pass through `erasure_phases` / `<backend>_phases` rather than hard-coding it.
* **Support primitives.** The S-expression format already encodes `primInt` / `primFloat` / `primString` / `primArray` (see [format.md](format.md) and [`SerializePrimitives.v`](/theories/serialization/SerializePrimitives.v)). Most backends still need to thread floats, strings and arrays through.
* **Inlining.** `config.inlinings_opts` is wired into the typed erasure (`mk_opts` in [`ConfigUtils.v`](/theories/ConfigUtils.v)). Inlining for the untyped backends still needs to be wired up.
* **Separate extraction.** Allow producing a `PAst` for a single definition while reusing previously extracted environments for its dependencies.
* **Benchmarking.** Build a reproducible benchmark harness covering each backend's output (size, compile time, runtime).

## Remapping

* **Support remapping** broadly: cover both `KnIndRemap` and `StringIndRemap`, and the external/inline/symbol variants of `remapped_constant` across all backends. See the per-backend TODOs in [`theories/backends/`](/theories/backends/).
* **Remapping of Agda stdlib types** — provide a ready-to-use `attributes_config` file that remaps the most common Agda standard library inductives onto target-language equivalents.
* Specific gaps already marked in source:
  * `RustBackend.v`: external remapping (`re_const_ext`) not yet honored.
  * `ElmBackend.v`: external, inline-constant, and inductive remapping not yet honored.
  * `OCamlBackend.v`: Malfunction `prim_def.Primitive` / `prim_def.Erased` not yet supported; the list of packages to compile against is not yet collected.

## Identifier handling

* **Pass checking for reserved keywords** — extend the per-backend keyword set (currently most complete for Rust) and run it as a validation step.
* **Validate / rename invalid identifiers** — turn today's silent sanitization into a validation pass that reports rewrites (or rejects the input, depending on a CLI flag).

# Possible extensions

## Other frontends

* F\* to $\lambda_\square$
* Lean to $\lambda_\square$ or $\lambda_{ANF}$ — go more directly than the current `lean-to-lambox` route.

## Other backends

* Replacements for Coq's built-in unverified extraction to Scheme, Haskell, and OCaml using typed erasure.
* Verified GHC core extraction.
* TypeScript / JavaScript.
