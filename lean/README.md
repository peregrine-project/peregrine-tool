# Lean 4 backend

`peregrine lean prog.ast -o prog.lean` compiles an untyped $\lambda_\square$ program to a single Lean 4 source file.
The file imports `Peregrine.Runtime`, the support library in this directory.

The backend is **unverified**. See [Verification status](#verification-status).

## Pipeline

```
.ast (untyped λ□)
  ↓ middle-end: parse, validate, sanitize names, transforms
EAst.program
  ↓ LeanCompile.compile_program     theories/lean/LeanCompile.v
LeanIR.lprogram                     theories/lean/LeanIR.v
  ↓ PrintLean.print_program         theories/lean/PrintLean.v
Lean 4 source
```

The backend requires the *implement box*, *implement lazy*, and *cofix to lazy* passes. Beta reduction, unboxing, and dearging are optional and off by default (`lean_phases` in [`theories/backends/LeanBackend.v`](/theories/backends/LeanBackend.v)).

`LeanIR` is a small named-variable IR loosely modelled on Lean 4's $\lambda_{pure}$: variables, constants, constructors, projections, application, lambda, `let`, `case`, and nested fixpoints. It is not in ANF.

## Generated code

$\lambda_\square$ is untyped, so every value has the single type `Peregrine.Obj`.

* Each inductive becomes an `unsafe inductive` whose fields all have type `Obj`. Type and constructor names get a trailing `_` (`nat_`, `S_`).
* Each constant with parameters becomes an `unsafe def` from `Obj`s to `Obj`.
* Each constant without parameters becomes a `Thunk Obj`, and references to it go through `.get`. Its body then runs on first use instead of at module initialization.
* A top-level fixpoint becomes a recursive `unsafe def`. A top-level mutual fixpoint becomes a `mutual` block. A nested fixpoint becomes a term-mode `let rec`.
* Application goes through `Peregrine.apply`, and matching through `Peregrine.cast`. Both are `unsafeCast`s.
* All declarations live in one namespace, `Generated` by default.
* A definition `f` in the input file `Prog.ast` is named `Prog_f`. Definitions inside inner modules keep the module path (`Prog_M_f`). Names that still collide also get their source file name.
* The term in the program's `main` position is not emitted. Call the entry point by its name.

## Usage

The output is meant to be compiled natively with Lake, in a package that contains the runtime. A minimal package has four files:

```
lakefile.toml
lean-toolchain            # leanprover/lean4:v4.30.0
Peregrine/Runtime.lean    # copy of lean/Peregrine/Runtime.lean
Main.lean                 # peregrine output, plus a main function
```

```toml
name = "prog"
defaultTargets = ["prog"]

[[lean_lib]]
name = "Peregrine"
roots = ["Peregrine.Runtime"]

[[lean_exe]]
name = "prog"
root = "Main"
```

Generate `Main.lean` and append an entry point to it:

```
peregrine lean Prog.ast -o Main.lean
```

```lean
unsafe def main : IO Unit :=
  let _ := Generated.Prog_f.get   -- drop `.get` if Prog_f takes parameters
  pure ()
```

Then run `lake build prog` and `./.lake/build/bin/prog`.

The result is an `Obj`. To print it, cast it to an inductive with the same constructor order and arities, as [`test/src/lean/Peregrine/TestPrinters.lean`](/test/src/lean/Peregrine/TestPrinters.lean) does for booleans, naturals, and lists.

The `lakefile.toml` at the repository root builds the runtime alone (`lake build`). The runtime is tested with Lean 4.30.0.

## Configuration

`lean_config` has two fields; see [format.md](/doc/format.md).

* `lean_namespace` — the namespace wrapped around the generated code. Default `"Generated"`.
* `lean_print_full_names` — prefix names with the file name and module path. Default `true`. When `false`, only the last component of each name is printed, quoted as `«f»` so that it cannot clash with a Lean keyword, and same-named definitions from different modules collide.

## Limitations

* `tPrim` (primitive integers, floats, strings, arrays), `tCoFix`, and `tEvar` are not supported. They compile to the placeholder `()` without a compile-time error, so a program that uses them misbehaves at run time.
* A mutual fixpoint nested inside a term compiles to a run-time `panic!`.
* Axioms (constants without a body) are skipped. A program that references one does not compile in Lean.
* Constant remappings (`remaps`) and custom attributes (`custom_attr`) are ignored.
* Erased terms are represented by `()`. A program that inspects one at run time has undefined behaviour.
* Names are sanitized with the OCaml sanitizer, so they can contain escapes such as `_UU2e`.
* Numerals are unary constructor towers. The generated file sets `maxRecDepth 1000000` so that Lean can elaborate them.

## Verification status

* The config serializer and deserializer for `lean_config` are covered by the soundness and completeness proofs in [`theories/serialization/`](/theories/serialization/). This is the only verified part.
* `extract_lean_semantics_preservation` in `LeanBackend.v` is stated as `True`. It is a placeholder, not a correctness proof.
* `extract_lean_total` is proved, but only says that the backend never returns an error.
* The translation, the printer, and the runtime are unverified. The generated code is `unsafe` Lean and relies on `unsafeCast`.

## Tests

[`test/src/lean.ts`](/test/src/lean.ts) runs the shared test programs through the backend. For each program it builds a native executable with Lake and compares the printed result with the expected output. It needs `lake` on the `PATH`.
