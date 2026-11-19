(** * Checking the input conditions of the verified Malfunction and CakeML backends

  The backends' verified passes ([name_annotation] and [compile_to_malfunction]
  of rocq-verified-extraction and its CakeML port) are only correct on programs
  that are well formed at the extraction flags (in particular without boxes,
  axioms, projections, lazy/force or primitive strings and arrays) and whose
  inductive types have few enough constructors and constructor arguments
  ([good_for_extraction]).  This file gives a decision procedure for these
  conditions, generic in the bounds; the backends instantiate it and prove it
  sound for their [good_for_extraction].  Axioms are handled separately, see
  [fill_axioms] below. *)

From Stdlib Require Import ZArith List ssreflect ssrbool.
From MetaRocq.Utils Require Import utils ResultMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed EProgram EPrimitive.
From MetaRocq.Erasure Require EWcbvEval.
From Equations Require Import Equations.
From Peregrine Require Import Utils CheckWf.

Import ListNotations.
Import MonadNotation.
Local Open Scope bs_scope.

Section Check.
  (** The number of non-constant constructors before position [i] in a list
      of constructor arities, and the bounds on the number of non-constant
      constructors, constructors and constructor arguments. *)
  Variable blocks_until : nat -> list nat -> nat.
  Variable max_blocks : nat.
  Variables max_ctors max_args : Z.

  Definition check_inductive_body (ob : one_inductive_body) : bool :=
    let args := map cstr_nargs ob.(ind_ctors) in
    (blocks_until #|args| args <? max_blocks)
    && (Z.of_nat #|ob.(ind_ctors)| <? max_ctors)%Z
    && forallb (fun b => Z.of_nat b.(cstr_nargs) <? max_args)%Z ob.(ind_ctors).

  Definition check_inductive_decl (d : kername * global_decl) : bool :=
    match d.2 with
    | InductiveDecl mib => forallb check_inductive_body mib.(ind_bodies)
    | ConstantDecl _ => true
    end.

  Definition check_inductives (Σ : global_declarations) : bool :=
    forallb check_inductive_decl Σ.

  Lemma lookup_env_In' Σ kn d : lookup_env Σ kn = Some d -> In (kn, d) Σ.
  Proof.
    induction Σ as [|[kn' d'] Σ IH]; cbn => //.
    case: eqb_spec => [-> [=<-]|_ h]; [now left|right; now apply IH].
  Qed.

  Lemma check_inductives_lookup Σ i mb ob :
    check_inductives Σ -> lookup_inductive Σ i = Some (mb, ob) ->
    check_inductive_body ob.
  Proof.
    unfold check_inductives, lookup_inductive, lookup_minductive.
    intros hΣ hl.
    destruct (lookup_env Σ (inductive_mind i)) as [[|mib]|] eqn:he; cbn in hl => //.
    destruct (nth_error (ind_bodies mib) (inductive_ind i)) eqn:hn; cbn in hl => //.
    injection hl as <- <-.
    apply lookup_env_In' in he.
    move: hΣ => /forallb_forall /(_ _ he); cbn => /forallb_forall; apply.
    now eapply nth_error_In.
  Qed.

  Lemma check_inductive_body_spec ob : check_inductive_body ob ->
    let args := map cstr_nargs ob.(ind_ctors) in
    blocks_until #|args| args < max_blocks /\
    #|ob.(ind_ctors)| < Z.to_nat max_ctors /\
    (forall n b, nth_error ob.(ind_ctors) n = Some b -> cstr_nargs b < Z.to_nat max_args).
  Proof.
    unfold check_inductive_body.
    move=> /andP [/andP [/Nat.ltb_lt hb /Z.ltb_lt hc] /forallb_forall ha].
    split; [exact hb|]. split; [lia|].
    intros n b hn. apply nth_error_In in hn. move: (ha _ hn) => /Z.ltb_lt. lia.
  Qed.

  Context {efl : EEnvFlags}.

  (** The decision procedure, reporting why a program is rejected. *)
  Definition check_extractable (p : program) : result' unit :=
    map_error (fun e => "Program is not well formed for the backend: " ++ e) (check_wf_program p) ;;
    assert' (check_inductives p.1)
      (fun _ => "Program has an inductive type with too many constructors or constructor arguments for the backend").

  Lemma check_extractable_sound p :
    bool_of_result (check_extractable p) = true ->
    wf_eprogram efl p /\ check_inductives p.1.
  Proof.
    unfold check_extractable.
    rewrite result_bindb result_mapb result_assertb'.
    move=> /andP [hwf hi]. split; [|exact hi].
    now apply check_wf_program_sound.
  Qed.
End Check.

(** ** Axioms

  Axioms, including remapped constants (whose bodies [drop_remapped_bodies]
  removes), are realized outside the program: by the target definition they
  are remapped to, or by an external module ([$Axioms] for Malfunction).  The
  verified passes do not allow axioms, so the backends check and run them on
  the program in which every axiom has the closed placeholder body
  [fun x => x] ([fill_axioms]).  Afterwards, they drop the compiled
  placeholders again ([restore_axioms]), so that the serializers emit the
  external realization exactly as for an axiom.  The compilation of a term
  does not depend on the bodies of constants (a constant compiles to a
  reference to its global name), so all other definitions are compiled as in
  the original program.  Like remapping, the external realization of axioms
  is trusted. *)

Definition axiom_placeholder : term := tLambda BasicAst.nAnon (tRel 0).

Definition is_axiom (d : kername * global_decl) : bool :=
  match d.2 with
  | ConstantDecl {| cst_body := None |} => true
  | _ => false
  end.

Definition fill_axioms (Σ : global_declarations) : global_declarations :=
  map (fun d => if is_axiom d
                then (d.1, ConstantDecl {| cst_body := Some axiom_placeholder |})
                else d) Σ.

Definition axiom_names (Σ : global_declarations) : list string :=
  map (fun d => string_of_kername d.1) (filter is_axiom Σ).

Definition restore_axioms {A} (names : list string) (env : list (string * option A)) :
  list (string * option A) :=
  map (fun '(n, b) => if existsb (eqb n) names then (n, None) else (n, b)) env.

(** ** Warnings

  The OCaml and CakeML backends compile every program, and run
  [check_extractable] only to decide whether the correctness theorem of
  verified extraction covers the output.  When the check fails, they report
  [unverified_warning]; the driver prints it, or with [--strict-verified]
  fails with it. *)
Definition unverified_warning (backend : string) (r : result' unit) : list string :=
  match r with
  | Ok _ => []
  | Err e => [backend ++ " backend: " ++ e ++
              "; this program is outside verified-extraction's correctness theorem, so the generated code is not covered by the proof."]
  end.

Lemma unverified_warning_nil b r :
  unverified_warning b r = [] <-> bool_of_result r = true.
Proof. now destruct r. Qed.

(** ** Evaluation with filled axioms

  Evaluation never unfolds an axiom, so a program that evaluates to a value
  also does so after [fill_axioms]. *)

Lemma lookup_env_fill_axioms Σ kn :
  lookup_env (fill_axioms Σ) kn =
  option_map (fun d => if is_axiom (kn, d)
                       then ConstantDecl {| cst_body := Some axiom_placeholder |}
                       else d) (lookup_env Σ kn).
Proof.
  induction Σ as [|[kn' d] Σ IH]; [reflexivity|].
  unfold fill_axioms in *. cbn [map].
  destruct (is_axiom (kn', d)) eqn:ha; cbn [lookup_env fst snd];
    destruct (eqb kn kn') eqn:he; cbn; try exact IH;
    apply eqb_eq in he; subst kn'; now rewrite ha.
Qed.

Lemma lookup_minductive_fill_axioms Σ kn :
  lookup_minductive (fill_axioms Σ) kn = lookup_minductive Σ kn.
Proof.
  unfold lookup_minductive. rewrite lookup_env_fill_axioms.
  destruct (lookup_env Σ kn) as [d|]; [|reflexivity].
  destruct d as [[b]|]; [destruct b|]; reflexivity.
Qed.

Lemma lookup_inductive_fill_axioms Σ ind :
  lookup_inductive (fill_axioms Σ) ind = lookup_inductive Σ ind.
Proof. unfold lookup_inductive. now rewrite lookup_minductive_fill_axioms. Qed.

Lemma lookup_constructor_fill_axioms Σ ind c :
  lookup_constructor (fill_axioms Σ) ind c = lookup_constructor Σ ind c.
Proof. unfold lookup_constructor. now rewrite lookup_inductive_fill_axioms. Qed.

Lemma constructor_isprop_pars_decl_fill_axioms Σ ind c :
  constructor_isprop_pars_decl (fill_axioms Σ) ind c = constructor_isprop_pars_decl Σ ind c.
Proof. unfold constructor_isprop_pars_decl. now rewrite lookup_constructor_fill_axioms. Qed.

Lemma inductive_isprop_and_pars_fill_axioms Σ ind :
  inductive_isprop_and_pars (fill_axioms Σ) ind = inductive_isprop_and_pars Σ ind.
Proof. unfold inductive_isprop_and_pars. now rewrite lookup_inductive_fill_axioms. Qed.

Lemma declared_constant_fill_axioms Σ kn decl body :
  declared_constant Σ kn decl -> cst_body decl = Some body ->
  declared_constant (fill_axioms Σ) kn decl.
Proof.
  unfold declared_constant. intros h hb. rewrite lookup_env_fill_axioms h. cbn.
  destruct decl as [[]]; cbn in *; congruence.
Qed.

Lemma eval_fill_axioms {wfl : EWcbvEval.WcbvFlags} Σ t v :
  EWcbvEval.eval Σ t v -> EWcbvEval.eval (fill_axioms Σ) t v.
Proof.
  induction 1;
  repeat match goal with
  | H : constructor_isprop_pars_decl Σ _ _ = _ |- _ => rewrite <- constructor_isprop_pars_decl_fill_axioms in H
  | H : inductive_isprop_and_pars Σ _ = _ |- _ => rewrite <- inductive_isprop_and_pars_fill_axioms in H
  | H : lookup_constructor Σ _ _ = _ |- _ => rewrite <- lookup_constructor_fill_axioms in H
  | H : declared_constant Σ _ ?d, H' : cst_body ?d = Some _ |- _ => eapply declared_constant_fill_axioms in H; [|exact H']
  end;
  try solve [econstructor; eassumption].
  - econstructor; tea.
    clear -a iha. induction a; constructor; eauto. apply iha. apply IHa, iha.
  - constructor.
    depelim X; constructor; eauto.
    eapply All2_over_undep in a. now eapply All2_All2_Set.
  - constructor.
    destruct t; try exact i. cbn [EWcbvEval.atom] in i |- *.
    destruct args; [|exact i]. now rewrite lookup_constructor_fill_axioms.
Qed.
