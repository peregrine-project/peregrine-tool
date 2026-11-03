From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import LeanIR.
From Peregrine Require Import LeanCompile.
From Peregrine Require Import PrintKoka.
From Peregrine Require Import LeanCheck.

Import MonadNotation.

Local Open Scope bs_scope.

(* The Koka backend is experimental and unverified.  It shares the IR and
   compiler of the Lean backend ([LeanIR], [LeanCompile]); [PrintKoka]
   prints Koka source in which every value has type [any]. *)



Definition default_koka_config := {|
  koka_module           := "";
  koka_print_full_names := true;
|}.

Definition koka_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Required;
  cofix_to_laxy_c  := Required;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible false;
  dearg_consts_c   := Compatible false;
  specialize_instances_c := Compatible false;
  cse_c            := Compatible false;
|}.



Definition extract_koka (remaps : constant_remappings)
                        (custom_attr : custom_attributes)
                        (opts : koka_config)
                          (file_name : string)
                          (p : EAst.program)
                          : result' string :=
  check_supported "Koka" remaps p;;
  let ir := compile_program remaps p in
  Ok (print_program (remap_modules remaps) opts.(koka_print_full_names) file_name opts.(koka_module) ir).



(* ----- Stub verification scaffolding -------------------------------

   These statements document the verification goals for the new
   backend.  They mirror the names used by CertiRocq's correctness
   lemmas so a future formalisation effort can find them by grep. *)

Theorem extract_koka_total :
  forall remaps attrs opts file p,
    check_supported "Koka" remaps p = Ok tt ->
    exists s, extract_koka remaps attrs opts file p = Ok s.
Proof.
  intros * H. unfold extract_koka. rewrite H. eexists. reflexivity.
Qed.

(* Semantics preservation: ⟦p⟧_λ□ ≈ ⟦extract_koka p⟧_Koka.
   Stated as [True] for now — to be replaced with a real relation
   between the EWcbvEval semantics and Koka's reduction. *)
Theorem extract_koka_semantics_preservation : True.
Proof. exact I. Qed.
