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

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_fsharp_config := {|
  fsharp_namespace        := "Generated";
  fsharp_print_full_names := true;
|}.

Definition fsharp_phases := {|
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



(* Terms the compiler has no translation for.  [compile_term] would turn
   them into [LPanic], which the printer emits as the erased-value
   placeholder, so the program would compute a wrong result instead of
   failing.  The required phases above remove [tBox], [tLazy], [tForce]
   and [tCoFix]; [tCoFix] is still listed so that it fails loudly should
   that ever change. *)
Fixpoint unsupported_term (t : EAst.term) : option string :=
  let first := fix first (l : list (option string)) :=
    match l with
    | [] => None
    | Some s :: _ => Some s
    | None :: l => first l
    end in
  match t with
  | EAst.tEvar _ _ => Some "tEvar"
  | EAst.tCoFix _ _ => Some "tCoFix"
  | EAst.tPrim _ => Some "tPrim (primitive integers, floats, strings and arrays)"
  | EAst.tLambda _ b | EAst.tProj _ b | EAst.tLazy b | EAst.tForce b =>
    unsupported_term b
  | EAst.tLetIn _ b u | EAst.tApp b u =>
    first [unsupported_term b; unsupported_term u]
  | EAst.tConstruct _ _ args => first (List.map unsupported_term args)
  | EAst.tCase _ d brs =>
    first (unsupported_term d :: List.map (fun br => unsupported_term (snd br)) brs)
  | EAst.tFix mfix _ => first (List.map (fun d => unsupported_term d.(EAst.dbody)) mfix)
  | _ => None
  end.

Definition check_supported (p : EAst.program) : result' unit :=
  let check_body (where_ : string) (t : EAst.term) : result' unit :=
    match unsupported_term t with
    | Some s => Err ("The F# backend does not support " ++ s ++ ", used in " ++ where_)
    | None => Ok tt
    end in
  let check_decl (d : kername * EAst.global_decl) : result' unit :=
    match snd d with
    | EAst.ConstantDecl {| EAst.cst_body := Some t |} => check_body (string_of_kername (fst d)) t
    | _ => Ok tt
    end in
  monad_iter check_decl (fst p);;
  check_body "the main term" (snd p).

Definition extract_fsharp (remaps : constant_remappings)
                          (custom_attr : custom_attributes)
                          (opts : fsharp_config)
                          (file_name : string)
                          (p : EAst.program)
                          : result' string :=
  check_supported p;;
  let ir := compile_program p in
  Ok (print_program opts.(fsharp_print_full_names) file_name opts.(fsharp_namespace) ir).



(* ----- Stub verification scaffolding -------------------------------

   These statements document the verification goals for the new
   backend.  They mirror the names used by CertiRocq's correctness
   lemmas so a future formalisation effort can find them by grep. *)

Theorem extract_fsharp_total :
  forall remaps attrs opts file p,
    check_supported p = Ok tt ->
    exists s, extract_fsharp remaps attrs opts file p = Ok s.
Proof.
  intros * H. unfold extract_fsharp. rewrite H. eexists. reflexivity.
Qed.

(* Semantics preservation: ⟦p⟧_λ□ ≈ ⟦extract_fsharp p⟧_F#.
   Stated as [True] for now — to be replaced with a real relation
   between the EWcbvEval semantics and F#'s reduction. *)
Theorem extract_fsharp_semantics_preservation : True.
Proof. exact I. Qed.
