From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import LeanIR.
From Peregrine Require Import LeanCompile.
From Peregrine Require Import PrintFSharp.
From Peregrine Require Import LeanCheck.

Import MonadNotation.

Local Open Scope bs_scope.

(* The F# backend is experimental and unverified. *)



Definition default_fsharp_config := {|
  fsharp_namespace        := "Generated";
  fsharp_print_full_names := true;
|}.

Definition fsharp_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible false;
  dearg_consts_c   := Compatible false;
  specialize_instances_c := Compatible false;
  cse_c            := Compatible false;
  lift_constants_c := Compatible false;
|}.



Definition extract_fsharp (remaps : constant_remappings)
                          (custom_attr : custom_attributes)
                          (opts : fsharp_config)
                          (file_name : string)
                          (p : EAst.program)
                          : result' string :=
  check_supported "F#" remaps p;;
  let ir := compile_program remaps p in
  Ok (print_program (remap_modules remaps) opts.(fsharp_print_full_names) file_name opts.(fsharp_namespace) ir).



(* ----- Stub verification scaffolding -------------------------------

   These statements document the verification goals for the new
   backend.  They mirror the names used by CertiRocq's correctness
   lemmas so a future formalisation effort can find them by grep. *)

Theorem extract_fsharp_total :
  forall remaps attrs opts file p,
    check_supported "F#" remaps p = Ok tt ->
    exists s, extract_fsharp remaps attrs opts file p = Ok s.
Proof.
  intros * H. unfold extract_fsharp. rewrite H. eexists. reflexivity.
Qed.

(* Semantics preservation: ⟦p⟧_λ□ ≈ ⟦extract_fsharp p⟧_F#.
   Stated as [True] for now — to be replaced with a real relation
   between the EWcbvEval semantics and F#'s reduction. *)
Theorem extract_fsharp_semantics_preservation : True.
Proof. exact I. Qed.
