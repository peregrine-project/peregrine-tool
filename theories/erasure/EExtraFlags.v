(** * Flags of the extra (unverified) middle-end transformations

    The environment and evaluation flags in force where [extra_unsafe_transforms]
    (Transforms.v) runs: after constructors-as-blocks, before box
    implementation.  The termination axioms of the extra passes are stated at
    these flags only. *)

From MetaRocq.Erasure Require Import EWellformed EWcbvEval.
From MetaRocq.Erasure Require EConstructorsAsBlocks EInlineProjections ERemoveParams EImplementBox.

Definition extra_env_flags : EEnvFlags :=
  EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag
      (ERemoveParams.switch_no_params all_env_flags)).

Definition extra_wcbv_flags : WcbvFlags := EImplementBox.block_wcbv_flags.
