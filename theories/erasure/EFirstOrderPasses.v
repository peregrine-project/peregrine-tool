(** * First-order collapse of the value relations of Peregrine's passes

    For each pass-specific value relation [rel], a lemma of the shape
    [fo_blk v -> rel v v' -> v' = v] (plus, where the relation needs it, the
    fact that [v'] is a value).  These are what [fo_triple_obseq] asks for. *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EGlobalEnv EProgram
  EWcbvEval EWellformed.
From Peregrine Require Import EFirstOrder ESpecRel ELiftConstants.

Set Default Goal Selector "!".
#[local] Set Warnings "-signature-auto-inline".

Lemma Forall2_collapse {A} (P : A -> Prop) (R : A -> A -> Prop) l l' :
  Forall (fun x => forall y, R x y -> y = x) l -> Forall2 R l l' -> l' = l.
Proof.
  intros H H2; induction H2; inversion H; subst; f_equal; auto.
Qed.

(** ** [Gv]: instance specialization and beta-reduction *)

Lemma fo_Gv Σ Σ' v v' : fo_blk v -> Gv Σ Σ' v v' -> v' = v.
Proof.
  intros H; revert v'. induction H using fo_blk_ind'; intros v' HG.
  - now inversion HG.
  - destruct p as [? []]; cbn in H; try (now exfalso);
      now depelim HG.
  - depelim HG. f_equal. eapply (Forall2_collapse (fun _ => True)); tea.
Qed.

Lemma fo_gchain p p' v v' : fo_blk v -> gchain p p' v v' -> v' = v.
Proof.
  intros H Hc; induction Hc as [|p p' p'' v v' v'' Hst HG Hc IH]; auto.
  apply fo_Gv in HG; auto. subst. auto.
Qed.

(** ** [lift_rel]: constant lifting *)

Section Lift.
  Context {wfl : WcbvFlags}.

  Lemma value_construct_args Σ ind c args :
    value Σ (tConstruct ind c args) -> All (value Σ) args.
  Proof.
    intros Hv.
    change (value Σ (mkApps (tConstruct ind c args) [])) in Hv.
    apply value_mkApps_inv in Hv as [[[_ Hat]|[_ Hc]]|[Hne _ _]] => //.
    - destruct args; [constructor|]. depelim Hat; cbn in *; try discriminate;
        depelim p.
    - destruct Hc as (ind' & c' & mdecl & idecl & cdecl & args' & [_ _ [= _ _ <-] _ Hall]).
      exact Hall.
  Qed.

  Lemma value_not_const Σ kn : value Σ (tConst kn) -> False.
  Proof.
    intros Hv. change (value Σ (mkApps (tConst kn) [])) in Hv.
    apply value_mkApps_inv in Hv as [[[_ Hat]|[_ Hc]]|[Hne _ _]] => //.
    - depelim Hat; cbn in *; try discriminate; depelim p.
    - destruct Hc as (? & ? & ? & ? & ? & ? & [_ _ [=] _ _]).
  Qed.

  Lemma fo_lift_rel Σ' v v' :
    fo_blk v -> value Σ' v' -> lift_rel Σ' v v' -> v' = v.
  Proof.
    intros H; revert v'. induction H using fo_blk_ind'; intros v' Hv HG.
    - depelim HG; auto. exfalso. eapply value_not_const; tea.
    - destruct p as [? []]; cbn in H; try (now exfalso).
      all: depelim HG; auto.
      all: exfalso; eapply value_not_const; tea.
    - depelim HG.
      + exfalso. eapply value_not_const; tea.
      + f_equal. apply value_construct_args in Hv.
        clear -H0 H1 Hv. induction H1; inversion H0; subst; depelim Hv; f_equal; auto.
  Qed.
End Lift.
