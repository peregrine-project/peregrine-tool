(** * Correctness of beta reduction ([EBeta.betared])

    MetaRocq's [EBeta.betared] contracts beta redexes everywhere in a program
    (under binders and in the bodies of constants), substituting arguments
    that are arbitrary terms, not values.  MetaRocq assumes its correctness
    ([EBeta.trust_betared_wf], [EBeta.trust_betared_pres]); the latter states
    that the value of the reduced program is [betared] of the source value,
    which cannot hold for a pass that substitutes unevaluated arguments.

    This file proves the pass correct for the function [EBeta.betared_program]
    itself:

    - [betared_program_wf]: well-formedness is preserved, at any flags with
      [has_tApp];
    - [betared_program_pres]: evaluation is preserved, the values being
      related by [betared_rel], the hereditary value relation [Gv] of
      [ESpecRel] (a source value against a target value whose bodies contract
      redexes with arbitrary arguments and may contain, in place of a closed
      source value, a closed term evaluating to a related value).

    [betared_transformation] packages the two as a [Transform.t] whose
    [transform] is [EBeta.betared_program]. *)

From Stdlib Require Import List Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames Transform.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
  ECSubst EGlobalEnv EWcbvEval EProgram EWellformed EBeta.
From Peregrine Require Import EExtraFlags ESpecRel EInstanceSpecialize.
Import ListNotations.
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

(** ** [betared] is in the simulation relation [G] *)

Section GBeta.
  Variables Σ Σ' : global_declarations.
  Notation G := (G Σ Σ').

  Lemma G_beta_body f f' args args' :
    G f f' -> Forall2 G args args' -> G (mkApps f args) (beta_body f' args').
  Proof.
    intros Hf H. induction H in f, f', Hf |- *; cbn [beta_body mkApps]; auto.
    destruct f'.
    all: try (apply G_mkApps; auto; apply G_s; constructor; auto; fail).
    apply IHForall2. apply G_s. eapply Gs_beta; eauto.
  Qed.

  Definition G_aux (t : term) :=
    forall args args', Forall2 G args args' -> G (mkApps t args) (betared_aux args' t).

  Lemma G_aux0 t : G_aux t -> G t (betared_aux [] t).
  Proof. intros H. exact (H [] [] (Forall2_nil _)). Qed.

  Lemma G_aux_list l : All G_aux l -> Forall2 G l (map (betared_aux []) l).
  Proof. induction 1; cbn; constructor; auto using G_aux0. Qed.

  Lemma G_aux_brs (l : list (list name × term)) :
    All (fun br => G_aux br.2) l -> brs_rel G l (map (on_snd (betared_aux [])) l).
  Proof. induction 1; cbn; constructor; auto. split; cbn; auto using G_aux0. Qed.

  Lemma G_aux_mfix (m : mfixpoint term) :
    All (fun d => G_aux (dbody d)) m -> fix_rel G m (map (map_def (betared_aux [])) m).
  Proof. induction 1; cbn; constructor; auto. repeat split; cbn; auto using G_aux0. Qed.

  Lemma G_betared_aux t : G_aux t.
  Proof.
    induction t using term_forall_list_ind; intros sp sp' Ha;
      cbn [betared_aux map_subterms].
    - apply G_mkApps; auto. apply G_refl.
    - apply G_mkApps; auto. apply G_refl.
    - apply G_mkApps; auto. apply G_refl.
    - apply G_mkApps; auto. apply G_s; constructor. now apply G_aux_list.
    - apply G_beta_body; auto. apply G_s; constructor. now apply G_aux0.
    - apply G_mkApps; auto. apply G_s; constructor; now apply G_aux0.
    - apply (IHt1 (t2 :: sp)). constructor; auto. now apply G_aux0.
    - apply G_mkApps; auto. apply G_refl.
    - apply G_mkApps; auto. apply G_s; constructor. now apply G_aux_list.
    - apply G_mkApps; auto. apply G_s; constructor; [now apply G_aux0|now apply G_aux_brs].
    - apply G_mkApps; auto. apply G_s; constructor. now apply G_aux0.
    - apply G_mkApps; auto. apply G_s; constructor. now apply G_aux_mfix.
    - apply G_mkApps; auto. apply G_s; constructor. now apply G_aux_mfix.
    - apply G_mkApps; auto.
      destruct p as [? []]; try (apply G_refl).
      depelim X. destruct p as [Hd Hv]. destruct a; cbn in *.
      apply G_s; constructor; [now apply G_aux0|now apply G_aux_list].
    - apply G_mkApps; auto. apply G_s; constructor. now apply G_aux0.
    - apply G_mkApps; auto. apply G_s; constructor. now apply G_aux0.
  Qed.

  Lemma G_betared t : G t (betared t).
  Proof. apply G_aux0, G_betared_aux. Qed.

End GBeta.

(** ** The environment *)

Lemma lookup_env_betared Σ kn :
  lookup_env (betared_env Σ) kn = option_map betared_in_decl (lookup_env Σ kn).
Proof.
  induction Σ as [|[kn' d] Σ IH]; cbn; auto.
  destruct (eqb_spec kn kn'); auto.
Qed.

Lemma env_sim_betared Σ : env_sim Σ (betared_env Σ).
Proof.
  intros kn d hl. rewrite lookup_env_betared hl. eexists; split; [reflexivity|].
  destruct d as [[[b|]]|]; cbn; auto.
Qed.

Lemma fresh_global_betared kn Σ : fresh_global kn Σ -> fresh_global kn (betared_env Σ).
Proof.
  induction 1 as [|[kn' d] Σ]; cbn; constructor; auto.
Qed.

(** ** Well-formedness *)

Section Wf.
  Context {efl : EEnvFlags} {hasapp : has_tApp}.
  Context (Σ : global_declarations).

  Lemma wf_tApp k f a : wellformed Σ k f -> wellformed Σ k a -> wellformed Σ k (tApp f a).
  Proof. intros hf ha. cbn. now rewrite hasapp hf ha. Qed.

  Lemma wf_beta_body k f args :
    wellformed Σ k f -> forallb (wellformed Σ k) args -> wellformed Σ k (beta_body f args).
  Proof.
    induction args as [|a args IH] in f |- *; cbn [beta_body forallb]; auto.
    intros hf. move/andP => [ha hargs].
    destruct f.
    all: try (cbn [mkApps]; rewrite wellformed_mkApps //; apply/andP; split; auto;
              now apply wf_tApp).
    apply IH; auto. apply wellformed_subst.
    - cbn. now rewrite ha.
    - cbn in hf |- *. now move/andP: hf => [_ hf].
  Qed.

  Lemma wf_betared_aux t :
    forall k args, wellformed Σ k t -> forallb (wellformed Σ k) args ->
    wellformed Σ k (betared_aux args t).
  Proof.
    induction t using term_forall_list_ind; intros k sp hw ha.
    all: try solve [cbn [betared_aux map_subterms]; rewrite wellformed_mkApps //;
                    apply/andP; split; [|exact ha]; clear ha;
                    cbn in hw |- *; rtoProp; intuition auto; solve_all].
    - (* tLambda *)
      cbn [betared_aux]. apply wf_beta_body; auto.
      cbn in hw |- *. move/andP: hw => [-> hw] /=. now apply IHt.
    - (* tApp *)
      cbn [betared_aux]. simpl in hw. move/andP: hw => [/andP [happ h1] h2].
      apply IHt1 => //. cbn [forallb]. rewrite ha andb_true_r. now apply IHt2.
    - (* tConstruct *)
      cbn [betared_aux map_subterms]. rewrite wellformed_mkApps //.
      apply/andP; split; [|exact ha]. clear ha.
      simpl in hw |- *. move/andP: hw => [-> hw] /=.
      destruct cstr_as_blocks.
      + move/andP: hw => [h1 h2]. rewrite length_map h1 /=. solve_all.
      + destruct args => //.
    - (* tFix *)
      cbn [betared_aux map_subterms]. rewrite wellformed_mkApps //.
      apply/andP; split; [|exact ha]. clear ha.
      simpl in hw |- *. move/andP: hw => [hl hw].
      apply/andP; split.
      + clear hw X. move/andP: hl => [-> hl] /=. solve_all. destruct x as [? [] ?] => //.
      + unfold wf_fix_gen in *. rewrite length_map.
        move/andP: hw => [-> hw] /=. unfold test_def in *. solve_all.
    - (* tCoFix *)
      cbn [betared_aux map_subterms]. rewrite wellformed_mkApps //.
      apply/andP; split; [|exact ha]. clear ha.
      simpl in hw |- *. move/andP: hw => [-> hw] /=.
      unfold wf_fix_gen in *. rewrite length_map.
      move/andP: hw => [-> hw] /=. unfold test_def in *. solve_all.
    - (* tPrim *)
      cbn [betared_aux map_subterms]. rewrite wellformed_mkApps //.
      apply/andP; split; [|exact ha]. clear ha.
      simpl in hw |- *. rewrite has_prim_map_prim. move/andP: hw => [-> hw] /=.
      destruct p as [? []]; cbn in *; auto.
      depelim X. destruct p as [Hd Hv]. destruct a; unfold test_array_model in *; cbn in *.
      move/andP: hw => [h1 h2]. apply/andP; split; [now apply Hd|]. solve_all.
  Qed.

  Lemma wf_betared k t : wellformed Σ k t -> wellformed Σ k (betared t).
  Proof. intros. now apply wf_betared_aux. Qed.

End Wf.

Lemma betared_env_wf {efl : EEnvFlags} {hasapp : has_tApp} Σ :
  wf_glob Σ -> wf_glob (betared_env Σ).
Proof.
  induction 1 as [|kn d Σ hwf IH hd hfr]; cbn; constructor; auto.
  - destruct d as [[[b|]]|]; cbn in *; auto.
    eapply sim_wellformed; [apply env_sim_betared|]. now apply (wf_betared (hasapp := hasapp)).
  - now apply fresh_global_betared.
Qed.

Theorem betared_program_wf {efl : EEnvFlags} {hasapp : has_tApp} (p : eprogram) :
  wf_eprogram efl p -> wf_eprogram efl (betared_program p).
Proof.
  intros [hwf hm]. split; cbn.
  - now apply (betared_env_wf (hasapp := hasapp)).
  - eapply sim_wellformed; [apply env_sim_betared|]. now apply (wf_betared (hasapp := hasapp)).
Qed.

(** ** Evaluation *)

Theorem betared_program_gstage {efl : EEnvFlags} {hasapp : has_tApp} (p : eprogram) :
  wf_eprogram efl p -> gstage p (betared_program p).
Proof.
  intros hwf. pose proof (betared_program_wf (hasapp := hasapp) p hwf) as [hwf' _].
  destruct hwf as [hwf hm]. split; cbn [betared_program fst snd] in *.
  - now eapply wellformed_closed_env.
  - now eapply wellformed_closed_env.
  - intros kn. unfold lookup_minductive. rewrite lookup_env_betared.
    destruct (lookup_env p.1 kn) as [[]|]; reflexivity.
  - intros c decl b hd hb. unfold declared_constant in *.
    exists (betared_in_constant_body decl), (betared b). split; [|split].
    + now rewrite lookup_env_betared hd.
    + cbn. now rewrite hb.
    + apply G_betared.
  - now eapply wellformed_closed.
  - apply G_betared.
Qed.

(** The relation between the value [v] of a program [p] and the value [v'] of
    [betared_program p]: [Gv] of [ESpecRel], between the two environments. *)
Definition betared_rel (p p' : program) (v v' : term) : Prop := Gv p.1 p'.1 v v'.

Theorem betared_program_pres {efl : EEnvFlags} {hasapp : has_tApp} (p : eprogram) (v : term) :
  wf_eprogram efl p ->
  eval_eprogram extra_wcbv_flags p v ->
  exists v' : term,
    eval_eprogram extra_wcbv_flags (betared_program p) v' /\
    betared_rel p (betared_program p) v v'.
Proof.
  intros hwf [ev].
  destruct (betared_program_gstage (hasapp := hasapp) p hwf) as [cl cl' Hind Hcst Hc HG].
  exact (G_simulation _ _ cl cl' Hind Hcst _ _ _ Hc HG ev).
Qed.

(** ** The transformation *)

Import Transform.

(** Same [transform] as MetaRocq's [EBeta.betared_transformation]; the
    observational equivalence is [betared_rel] and both obligations are
    proved.  The evaluation flags are those of the stage of the pipeline where
    the pass runs (constructors as blocks, unguarded fixpoints). *)
Program Definition betared_transformation (efl : EEnvFlags) {hasapp : has_tApp} :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram extra_wcbv_flags) (eval_eprogram extra_wcbv_flags) :=
  {| name := "betared ";
     transform p _ := betared_program p;
     pre p := wf_eprogram efl p;
     post p := wf_eprogram efl p;
     obseq p _ p' v v' := betared_rel p p' v v' |}.
Next Obligation.
  intros. now apply (betared_program_wf (hasapp := hasapp)).
Qed.
Next Obligation.
  subst p'. eapply (betared_program_pres (hasapp := hasapp)); eauto.
Qed.
