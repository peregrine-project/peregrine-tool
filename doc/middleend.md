# Peregrine Middle-end

The middle-end connects frontends and backends and serves three purposes:

1) Defines a common IR and configuration format and is responsible for converting to the formats expected by the backends
   
   For more details on IR and configuration format see [format.md](format.md).

2) Validates and ensure $\lambda_\square$ and frontend/backend configuration is compatible
3) Lower $\lambda_\square$ to the necessary subset compatible with the backends, and apply common program transformations and optimizations

This document details points 2 and 3 and shows the general middle-end pipeline.
For more details on frontends and backends, see [frontends.md](frontends.md), [backends.md](backends.md).

The middle-end is exposed as a CLI, for more details on how to use the middle-end, see [usage.md](usage.md)

## Pipeline

![](middleend_pipeline.png)

### Serialization/Deserialization
The first step in the pipeline is deserializing the input program and optionally configuration file if provided.
This step is fully verified.
The serialization/deserialization is implemented in [theories/serialization](/theories/serialization/).

### Validate program
Next step is validating that the program is wellformed. This check is implemented in [theories/CheckWf.v](/theories/CheckWf.v) and is verified.
This step checks:
1) that the environment doesn't contain undefined global declarations or inductive declarations
2) environment sorted topologically
3) that the program is closed
4) doesn't use block representation of constructors
5) cases are exhaustive
6) that the program doesn't contain any language constructs not supported

### Validate config
This step validates the options provided by the user and determines the final values that will be used for all options.
The final options used will depend on the user provided configuration, whether the input is typed, and which backend is being targeted. The middle-end ensures that the final options are compatible with the backend.

By default, all option fields are optional in the configuration file format. Any option left unspecified in the provided configuration object will be filled with the default value for the chosen backend.

Validation does the following:
1) Fill undeclared option with default values
2) Check that options are compatible with the backend
3) Untyped input for a typed backend is annotated by type inference (see below); every other combination of AST type and backend is accepted as is
4) Determine which transformations to apply based on configurations, and whether a transformations is required or incompatible with the chosen backend.
5) Validate configuration values 

If the configuration is invalid the pipeline either fails or prints a warning and ignores the invalid options.

### Sanitize identifiers
Some frontends have fewer restrictions on valid identifier names than the backends, thus a name sanitization pass is performed if necessary based on the target backend.
The pipeline first checks that no two global names of the program or the configuration sanitize to the same name, and fails otherwise.
Under that check the pass preserves well-formedness and evaluation: `NameSanitizeCorrect.sanitize_correct`, through the general renaming theorem `ERenameGlobals.eval_rename`.

### Apply transformations
The transformations that will be applied will depend on both the AST type, backend, and user configuration. See support matrix below for more details.

![](middleend_transforms.png)


* **reorder constructors**:
  a pass which reorder constructor in the inductive definition. This is useful when the trying to remap types to native types in the target language and the constructor order is different.
* **fixpoints**:
  a pass which changes the semantics of recursive functions to always unfold
* **remove parameters**:
  a pass which removes parameters of inductive types, because they cannot play a computational role
* **remove match $\square$**:
  a pass that removes the rule that case analysis on $\square$ is permitted by locally reducing them away
* **dearging**:
  Remove dead arguments
* **inline projections**:
  a pass replacing primitive projections by case analysis
* **fully applied constructors**:
  a pass inlining constructor arguments via application into the arguments carried by the constructors, i.e. constructors cannot be partially applied anymore
* **remove singleton types**:
  Unboxes singleton types by, i.e. inductive types with 1 constructor with 1 argument 
* **inlining**:
  a pass inlining declarations. Only declarations declared as inline will be inlined (the `inlinings` of the configuration and attribute files, plus the program's recursors when `--inline-recursors` is given). This is MetaRocq's `EInlining.inline_transformation`, proved correct for any list of inlined constants.
* **beta reduction**:
  a pass performing beta reduction (MetaRocq's `EBeta`; assumed correct by the axioms `trust_betared_wf`, `trust_betared_pres`)
* **remap inductives**:
  a pass for remapping of inductive declaratiuons. Constructors and eliminator are remapped to axioms, which can be further remapped using the global declaration remapping feature.
* **implement $\square$**:
  a pass replacing $\square$ by an explicit recursive function ignoring its argument
* **implement lazy**:
  a pass replacing lazy/force 
* **annotate names**:
  a pass replacing de Bruijn variables by names
* **specialize instances**:
  a pass that clones a function at call sites that pass a statically known dictionary (single-constructor record) value, and reduces the clone (beta, case of a known constructor); see [optional passes](#optional-passes)
* **common subexpression elimination**:
  a pass that binds a closed subterm occurring at least twice, always in evaluated positions, with a `let`; see [optional passes](#optional-passes)
* **identity cases**:
  a pass rewriting `match e with C xs => C xs` to `e`, as Rocq's extraction does; see [optional passes](#optional-passes)
* **lambda-box simplifications**:
  fixpoint eta-hoisting (`fun xs => (fix F ..) xs` becomes the fixpoint; an argument may also be $\square$ when the corresponding parameter of the fixpoint is dead), case/function permutation (`match x with C => fun y => e` becomes `fun y => match x with C => e` for a variable `x`) and inlining of atomic lets (`let z := a in e` becomes `e[a/z]` for a variable, box, constant or constant constructor `a`) with applied lets and cases (the convoy pattern), as Rocq's extraction does in `Mlutil`; see [optional passes](#optional-passes)
* **lift constants**:
  a pass that replaces every maximal closed constructor value of at least two constructors (typically a `nat` literal) by a reference to a fresh global constant whose body is that value, sharing structurally equal values program-wide; see [optional passes](#optional-passes)


### Transformation support (Untyped target AST)

| Pass                       | C, LLVM | Wasm | OCaml | CakeML | Eval | AST |
|----------------------------|---------------|---------------|-----|------|-------|--------|
| reorder constructors       | optional, default on | optional, default on | optional, default on | optional, default on | optional, default on | optional, default on |
| fixpoints                  | required | required | required | required | required | required |
| remove parameters          | required | required | required | required | required | required |
| remove match $\square$     | required | required | required | required | required | required |
| dearging                   | optional, default on (requires typed) | optional, default on (requires typed) | optional, default on (requires typed) | optional, default on (requires typed) | optional, default on (requires typed) | optional, default on (requires typed) |
| inline projections         | required | required | required | required | required | required |
| fully applied constructors | required | required | required | required | required | required |
| remove singleton types     | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off |
| inlining                   | optional, default on | optional, default on | optional, default on | optional, default on | optional, default on | optional, default on |
| beta reduction             | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off |
| remap inductives           | optional, default on | optional, default on | optional, default on | optional, default on | optional, default on | optional, default on |
| implement $\square$        | required | required | required | required | required | off |
| implement lazy             | off | off | off | off | off | off |
| annotate names             | optional, default off | optional, default off | required | required | optional, default off | optional, default off |
| specialize instances       | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off |
| common subexpression elimination | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off |
| identity cases             | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off |
| lambda-box simplifications | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off |
| lift constants             | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off | optional, default off |

Peregrine does not support cofixpoints: the input check rejects every program that contains `tCoFix` ("Program contains tCoFix"), for every backend, and the middle-end is proved correct for programs without cofixpoints. MetaRocq's `cofix to fix` pass, whose correctness rests on the false axiom `ECoInductiveToInductive.trust_cofix`, is not part of the pipeline. CertiRocq and the verified Malfunction and CakeML compilers have no translation for `tLazy` and `tForce` either, and turn them into placeholders. The C, Wasm, LLVM, OCaml, CakeML and eval backends therefore reject a program that still contains one of these terms after the passes above. The Lean, F# and Koka backends require `implement lazy`. Implement $\square$ and implement lazy are not user settings: each backend runs them if it requires them and otherwise not (the `implement_box` and `implement_lazy` fields of a configuration file are ignored, [format.md](format.md)). The `implement` $\square$ and `implement lazy` passes are MetaRocq's, proved correct for programs without cofixpoints.

### Transformation support (Typed target AST)

If the input is untyped, it is first annotated with types by Hindley-Milner inference ([EHindleyMilner.v](/theories/erasure/EHindleyMilner.v)): constants get generalized type schemes, inductive declarations get their type parameters and constructor field types reconstructed from the constructor uses in the program, and the inference fails (as a pipeline error) when the program is not typable. Erasing the annotations gives back the input program and the annotations are well scoped (both proved, [EHindleyMilnerSound.v](/theories/erasure/EHindleyMilnerSound.v)); that the annotations describe the terms is not proved (postponed, with the other follow-up work, to [#79](https://github.com/peregrine-project/peregrine-tool/issues/79)). Only type parameters of an inductive become type variables; value, `Prop` and phantom parameters are dropped (see [backends.md](backends.md#rust)).

| Pass                       | Rust                 | Elm                  | AST                   |
|----------------------------|----------------------|----------------------|-----------------------|
| remove parameters          | required             | required             | required              |
| dearging                   | optional, default on | optional, default on | optional, default off |
| identity cases             | optional, default off | optional, default off | optional, default off |
| lambda-box simplifications | optional, default off | optional, default off | optional, default off |

### Optional passes
Instance specialization ([EInstanceSpecialize.v](/theories/erasure/EInstanceSpecialize.v)), common subexpression elimination ([ECommonSubexpr.v](/theories/erasure/ECommonSubexpr.v)) and constant lifting ([ELiftConstants.v](/theories/erasure/ELiftConstants.v)) are off in every backend's default and are enabled with the `specialize_instances`, `cse` and `lift_constants` fields of the configuration ([format.md](format.md)) or the `--specialize-instances`, `--share-common-subterms` and `--lift-constants` flags. The command line's default set of passes has `--lift-constants` (and beta reduction), unless `-O0` ([usage.md](usage.md#middle-end-passes)). They run only in the untyped pipeline, in this order (with the $\lambda_\square$ simplifications below between `cse` and `lift_constants`), after the other optional passes (`optional_unsafe_transforms`) and before implement $\square$ (`extra_unsafe_transforms` in [Transforms.v](/theories/erasure/Transforms.v)), so beta reduction and dearging do not see their output; the Rust and Elm backends never run them (for constant lifting, the typed AST would need the lifted constants to carry a type scheme).

Constant lifting exists because a closed constructor value in a function body, such as the `nat` literal `1009` (a chain of 1010 constructor cells), is rebuilt by the generated code at every evaluation of the body in every backend that does not itself hoist constant data (C, Wasm, CakeML, Lean, Rust; `ocamlopt` does hoist it). The pass walks the environment from the deepest declaration up, collects in each constant body (and in the main term) the maximal closed constructor values of at least two constructors, and replaces each by `tConst kn` for a constant `kn` whose body is the value. Structurally equal values share one constant. The new constants `Peregrine.LiftConstants.lifted_constant_<i>` are inserted directly below the declaration that first uses them, so the environment stays well-formed. A constant whose whole body is such a value becomes a reference to the lifted constant too: it is not used as the shared constant itself, since it may be remapped. The pass is the identity when the environment already contains a name under `Peregrine.LiftConstants` or when the flags forbid `tConst`/`tConstruct`.

Instance specialization, common subexpression elimination and constant lifting are proved:

* Instance specialization: well-formedness preservation is proved (`specialize_instances_program_wf`). Evaluation preservation is proved without axioms (`specialize_instances_program_pres`, at the flags of this pipeline stage, [EExtraFlags.v](/theories/erasure/EExtraFlags.v)): if the source evaluates to `v`, the target evaluates to some `v'` related to `v` by `spec_rel`, a chain of one-pass simulation steps (unfolding, beta, iota, fixpoint unfolding and redirection to a specialized copy, with `v'` possibly holding closed unevaluated terms that evaluate to the corresponding parts of `v` under binders; [ESpecRel.v](/theories/erasure/ESpecRel.v)). The names `f$specN` of the specialized copies are checked for freshness against the environment and each other, and each copy is emitted below its first use and above everything it refers to.
* Common subexpression elimination: proved, without axioms. Well-formedness preservation is `cse_wf`, and the `TransformExt` instances are proved. Evaluation preservation with the same value is `cse_pres_eval`. It is a simulation (`cse_sim`) over `cse_rel`, which replaces closed subterms at strict positions (always evaluated before a value is produced) by their values. `candidate_ok` only hoists terms all of whose occurrences are strict.
* Constant lifting: proved, without axioms. Well-formedness preservation is `lift_program_wf`, and evaluation preservation (up to `lift_rel`, which lets a closed constructor value of the result be replaced by a reference to its lifted constant) is `lift_program_pres`. The proof is a simulation over `lift_rel` (`lift_rel_simulation`) together with the invariants of the transformed environment (`lift_env_inv`). The pass has no `TransformExt` instances: the lifted names are numbered by table position, so they are not stable under extension of the environment, and the pipeline does not use these instances.

Generalised iota reduction (`--iota-reduce`, `iota_case` in [ELboxOpts.v](/theories/erasure/ELboxOpts.v)) is a further rewrite of the same framework, run as its own transformation `iota_transformation` in `extra_unsafe_transforms` (and as its own stage of `typed_lbox_transform_pipeline` for the typed pipeline), after common subexpression elimination and before the identity-case pass. It rewrites a `match` on a constructor (a block or the application of a constructor, whose parameters are dropped) into lets binding the arguments, moves a `match` under a `let` in its scrutinee, and moves a `match` into the branches of a `match` in its scrutinee when these all end in constructors (with a guard against duplicating large branches). In the simulation it is a single rule `Rh_case_tgt`, stating that the target may apply one of the rewrites `crw` to a related `match`; these preserve evaluation of closed terms, for either representation of constructors (`crw_eval` in [ELboxOptsSim.v](/theories/erasure/ELboxOptsSim.v)). The static part is `iota_case_chain` in ELboxOptsSimStatic.v and well-formedness is `wellformed_iota_case` in ELboxOptsWf_case.v. The constants to inline before it can be computed automatically (`--inline-standard-constants`, on by default, and `--inline-small-constants`, [AutoInlining.v](/theories/AutoInlining.v)); this computation is not verified and need not be, since inlining is correct for any list.

The $\lambda_\square$ simplifications of [ELboxOpts.v](/theories/erasure/ELboxOpts.v) (identity cases, fixpoint eta-hoisting, case/function permutation, atomic lets and applied lets) are in the command line's default set of passes, off under `-O0`, and each has its own flag (`--drop-identity-matches`, `--unwrap-fixpoints`, `--hoist-case-lambdas`, `--inline-atomic-lets`; `--no-PASS` disables one), see [usage.md](usage.md#middle-end-passes). The record `lbox_opts` of ELboxOpts.v still has the earlier names of these options (`lbox_case_id`, `lbox_fix_eta`, `lbox_case_fun`, `lbox_let_fun`). In the untyped pipeline they run in `extra_unsafe_transforms`, after common subexpression elimination and before constant lifting and implement $\square$: first the identity-case pass, then the other three in one bottom-up traversal. For the Rust and Elm backends they run, in the same stages (after eta-expansion), inside the proved typed pipeline (`typed_lbox_transform_pipeline` in [Transforms.v](/theories/erasure/Transforms.v)). Well-formedness preservation is proved in [ELboxOptsWf.v](/theories/erasure/ELboxOptsWf.v), from one lemma per rewrite (`wellformed_fix_eta`, `wellformed_case_fun`, `wellformed_case_id`, `wellformed_let_inline`, `wellformed_beta_let`, in ELboxOptsWf_case.v, ELboxOptsWf_fix.v and ELboxOptsWf_let.v). Evaluation preservation, at the flags of this pipeline stage:

All four passes are proved, without axioms (`case_id_terminates`, `lbox_opts_eval`). If the source evaluates to `v`, the target evaluates to a `v'` related to `v` by `lbox_obs`, a chain of steps of the rewrite relation `R` of [ELboxOptsSim.v](/theories/erasure/ELboxOptsSim.v) ("`v'` is `v` with some subterms rewritten"). `R` is a forward simulation ([ELboxOptsSimEval.v](/theories/erasure/ELboxOptsSimEval.v)) and each pass is a chain of `R` steps ([ELboxOptsSimStatic.v](/theories/erasure/ELboxOptsSimStatic.v)).
Fixpoint eta-hoisting rewrites `fun x1 .. xk => (fix F ..) a1 .. ak` to the fixpoint when the fixpoint does not mention the `xi`, each `ai` is `xi` or a $\square$ in a position whose parameter the fixpoint body does not use, and the fixpoint body starts with at least `k` lambdas (`fix_arity_ok`). The last condition makes the partial applications of the fixpoint values, like those of the eta-expansion it replaces: where the source value is the closure `fun xj .. xk => (fix F ..) c1 .. c(j-1) xj .. xk`, the target value is what `(fix F ..) c1 .. c(j-1)` evaluates to, and `R` relates the two (`R_fix_part`) as long as the target value can take the remaining arguments one by one (`tarity`). A $\square$ passed for a dead parameter is related to any closed value (`Rh_app_dead`).
