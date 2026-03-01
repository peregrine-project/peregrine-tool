From MetaRocq.Erasure Require Import EImplementBox.
From MetaRocq.Erasure Require Import EProgram.

From MetaRocq.Common Require Import Transform.
From MetaRocq.Utils Require Import bytestring.
Import Transform.

Local Open Scope bs.

Program Definition implement_box_transformation efl :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram block_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "implementing box";
    transform p _ := EImplementBox.implement_box_program p ;
    pre p := True ;
    post p := wf_eprogram (switch_off_box efl) p ;
    obseq p hp p' v v' := v' = implement_box v |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Axiom trust_coq_kernel : forall p efl, pre (implement_box_transformation efl) p.

Definition implement_box {efl} p :=
  run (implement_box_transformation efl) p (trust_coq_kernel p efl).
