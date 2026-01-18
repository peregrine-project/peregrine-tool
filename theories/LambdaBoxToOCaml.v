From MetaRocq.Erasure Require EAst.
From MetaRocq.Common Require Import Kernames.
From Malfunction Require Import Pipeline.
From Stdlib Require Import List.

Import ListNotations.



Definition extract_names (t : EAst.term) : list ident :=
  match t with
  | EAst.tConst kn => [Kernames.string_of_kername kn]
  (* | EAst.tApp (EAst.tConstruct _ _ _) [_ ; _ ; l ; Ast.tConst kn _ ] => (Kernames.string_of_kername kn) :: extract_names l *) (* TODO? *)
  | _ => []
  end.

From Malfunction Require Import Serialize SemanticsSpec.
From Ceres Require Import CeresSerialize.
From MetaRocq.Common Require Import Transform.
Import Transform.

Definition print_program config nms p :=
  let serialize p_c := @to_string _ (Serialize_module config.(prims) Standalone (rev nms)) p_c in
  let code := serialize p in
  (nms, code).

Local Existing Instance CanonicalHeap.
Local Existing Instance CanonicalPointer.

Program Definition malfunction_pipeline :
  Transform.t _ _ _ _ _ _ _ _ :=
  post_verified_named_erasure_pipeline ▷
  compile_to_malfunction.
Next Obligation.
  intuition auto; destruct H; intuition eauto.
Qed.


Axiom trust_coq_kernel : forall p, pre malfunction_pipeline p.

Definition box_to_ocaml (p : EAst.program) :=
  let config := default_malfunction_config in (* TODO: handle constructor reordering *)
  let nms := extract_names (snd p) in
  let p := run malfunction_pipeline p (trust_coq_kernel p) in
  print_program config nms p.
