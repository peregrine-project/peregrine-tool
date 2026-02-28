From Stdlib Require Import List.
From CeresBS Require Import Ceres.
From CeresBS Require Import CeresUtils.
From CeresBS Require CeresParserUtils.
From CeresBS Require CeresString.
From MetaRocq.Utils Require All_Forall.

Import ListNotations.

Local Open Scope list_scope.

(* Completeness helper lemmas *)

Lemma complete_class_list_all {A : Type}
                             `{Serialize A}
                             `{Deserialize A} :
  forall (a xs : list A) (n : nat) (l : loc),
    All_Forall.All
      (fun t : A =>
       forall l : loc, _from_sexp l (to_sexp t) = inr t) a ->
    _sexp_to_list _from_sexp xs n l (map to_sexp a) = inr (rev xs ++ a).
Proof.
  induction a; intros; cbn.
  - rewrite rev_alt, app_nil_r.
    reflexivity.
  - inversion X; subst.
    rewrite H2.
    rewrite app_cons_assoc.
    apply IHa.
    assumption.
Qed.

Lemma complete_class_all_prod {A B : Type}
                             `{Serialize A}
                             `{Deserialize A}
                             `{Serialize B}
                             `{Deserialize B} :
  forall xs,
    CompleteClass A ->
    All_Forall.All
      (fun x : A * B =>
        forall l : loc, _from_sexp l (to_sexp (snd x)) = inr (snd x)) xs ->
      All_Forall.All
        (fun x : A * B =>
        forall l : loc, _from_sexp l (to_sexp x) = inr x) xs.
Proof.
  induction xs; intros.
  - apply All_Forall.All_nil.
  - apply All_Forall.All_cons.
    + intros.
      inversion X; subst.
      cbn.
      rewrite H5.
      rewrite complete_class.
      destruct a; cbn.
      reflexivity.
    + inversion X; subst.
      apply IHxs; assumption.
Qed.
