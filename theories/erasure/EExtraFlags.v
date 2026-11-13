(** * Flags of the extra (unverified) middle-end transformations

    The environment and evaluation flags in force where [extra_unsafe_transforms]
    (Transforms.v) runs: after constructors-as-blocks, before box
    implementation.  The termination axioms of the extra passes are stated at
    these flags only.

    Peregrine does not compile cofixpoints: [check_wf] (Pipeline.v) rejects a
    program with a [tCoFix], and the middle-end is instantiated at
    [nocofix_env_flags], [all_env_flags] without [tCoFix].  The extra flags
    are derived from them, so that the implementation of boxes and of
    lazy/force can use MetaRocq's correctness lemmas, which require
    [has_tCoFix = false]. *)

From MetaRocq.Erasure Require Import EWellformed EWcbvEval.
From MetaRocq.Erasure Require EConstructorsAsBlocks EInlineProjections ERemoveParams EImplementBox.

Definition nocofix_term_flags : ETermFlags :=
  {| has_tBox := true
   ; has_tRel := true
   ; has_tVar := false
   ; has_tEvar := false
   ; has_tLambda := true
   ; has_tLetIn := true
   ; has_tApp := true
   ; has_tConst := true
   ; has_tConstruct := true
   ; has_tCase := true
   ; has_tProj := true
   ; has_tFix := true
   ; has_tCoFix := false
   ; has_tPrim := all_primitive_flags
   ; has_tLazy_Force := true
  |}.

(** [all_env_flags] without cofixpoints. *)
Definition nocofix_env_flags : EEnvFlags :=
  {| has_axioms := true;
     term_switches := nocofix_term_flags;
     has_cstr_params := true;
     cstr_as_blocks := false |}.

Definition extra_env_flags : EEnvFlags :=
  EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag
      (ERemoveParams.switch_no_params nocofix_env_flags)).

Definition extra_wcbv_flags : WcbvFlags := EImplementBox.block_wcbv_flags.
