(** * Raw atoms produced by peregrine's serializers are parseable

    Every [Raw] atom that peregrine's serializers produce is a constant constructor
    tag ("tRel", "Untyped", "true", ...).  We show that all of them satisfy
    [raw_ok], so that the only side condition left for the string-level round trip
    (see [SerializeRoundtrip]) is about the bytes of [Str] atoms. *)

From Stdlib Require Import List ZArith Bool.
From MetaRocq.Utils Require Import bytestring All_Forall.
From MetaRocq.Common Require Import BasicAst Kernames Universes Primitive.
From MetaRocq.Erasure Require Import EPrimitive EAst ExAst EInduction.
From CeresBS Require Import Ceres.
From Peregrine Require Import CeresParserComplete.
From Peregrine Require Import SerializeCommon SerializePrimitives SerializeEAst
  SerializeExAst SerializePAst PAst.

Import ListNotations.
Local Open Scope bs_scope.

Class RawOk (A : Type) `{Serialize A} :=
  raw_ok_to_sexp : forall a : A, sexp_forall_atoms atom_raw_okb (to_sexp a) = true.

Lemma raw_ok_map_All {A} (g : A -> sexp) (l : list A) :
  All (fun x => sexp_forall_atoms atom_raw_okb (g x) = true) l ->
  forallb (sexp_forall_atoms atom_raw_okb) (map g l) = true.
Proof. induction 1 as [|x l Hx _ IH]; cbn; [reflexivity|]. rewrite Hx, IH. reflexivity. Qed.

Lemma raw_ok_map_forall {A} (g : A -> sexp) (l : list A) :
  (forall x, sexp_forall_atoms atom_raw_okb (g x) = true) ->
  forallb (sexp_forall_atoms atom_raw_okb) (map g l) = true.
Proof. intros H. induction l; cbn; [reflexivity|]. rewrite H, IHl. reflexivity. Qed.

Ltac raw_ok_step :=
  match goal with
  | |- true = true => reflexivity
  | |- _ && _ = true => apply andb_true_intro; split
  | |- _ => assumption
  | |- sexp_forall_atoms atom_raw_okb (to_sexp _) = true => apply raw_ok_to_sexp
  | |- raw_ok _ = true => reflexivity
  | |- forallb (sexp_forall_atoms atom_raw_okb) (map _ _) = true =>
      first [apply raw_ok_map_All; eassumption | apply raw_ok_map_forall; intro]
  end.

Ltac raw_ok_tac := cbn -[to_sexp raw_ok]; repeat raw_ok_step.

Ltac raw_ok_inst X :=
  let a := fresh "a" in
  intros a; unfold to_sexp at 1, X; destruct a; raw_ok_tac.

(** ** Ceres instances *)

#[global] Instance RawOk_Integral {A} `{Integral A} : RawOk A.
Proof. intros a. reflexivity. Qed.

#[global] Instance RawOk_bool : RawOk bool.
Proof. intros []; reflexivity. Qed.

#[global] Instance RawOk_unit : RawOk unit.
Proof. intros []; reflexivity. Qed.

#[global] Instance RawOk_string : RawOk string.
Proof. intros a; reflexivity. Qed.

#[global] Instance RawOk_option {A} `{RawOk A} : RawOk (option A).
Proof. raw_ok_inst @Serialize_option. Qed.

#[global] Instance RawOk_sum {A B} `{RawOk A} `{RawOk B} : RawOk (A + B).
Proof. raw_ok_inst @Serialize_sum. Qed.

#[global] Instance RawOk_product {A B} `{RawOk A} `{RawOk B} : RawOk (A * B).
Proof. raw_ok_inst @Serialize_product. Qed.

#[global] Instance RawOk_list {A} `{RawOk A} : RawOk (list A).
Proof. intros l. unfold to_sexp at 1, Serialize_list. raw_ok_tac. Qed.

#[global] Instance RawOk_spec_float : RawOk SpecFloat.spec_float.
Proof. raw_ok_inst Serialize_spec_float. Qed.

#[global] Instance RawOk_prim_float : RawOk PrimFloat.float.
Proof. intros f. apply RawOk_spec_float. Qed.

(** ** Common *)

#[global] Instance RawOk_ident : RawOk ident.
Proof. intros a; reflexivity. Qed.

#[global] Instance RawOk_dirpath : RawOk dirpath.
Proof. intros a. apply RawOk_list. Qed.

#[global] Instance RawOk_modpath : RawOk modpath.
Proof. intros m; induction m; unfold to_sexp at 1; cbn -[to_sexp raw_ok]; repeat raw_ok_step. Qed.

#[global] Instance RawOk_kername : RawOk kername.
Proof. intros a. apply RawOk_product. Qed.

#[global] Instance RawOk_inductive : RawOk inductive.
Proof. raw_ok_inst Serialize_inductive. Qed.

#[global] Instance RawOk_projection : RawOk projection.
Proof. raw_ok_inst Serialize_projection. Qed.

#[global] Instance RawOk_name : RawOk name.
Proof. raw_ok_inst Serialize_name. Qed.

#[global] Instance RawOk_recursivity_kind : RawOk recursivity_kind.
Proof. raw_ok_inst Serialize_recursivity_kind. Qed.

#[global] Instance RawOk_allowed_eliminations : RawOk allowed_eliminations.
Proof. raw_ok_inst Serialize_allowed_eliminations. Qed.

(** ** Primitives *)

#[global] Instance RawOk_prim_tag : RawOk prim_tag.
Proof. raw_ok_inst Serialize_prim_tag. Qed.

#[global] Instance RawOk_prim_string : RawOk PrimString.string.
Proof. intros a; reflexivity. Qed.

(** ** EAst *)

Section WithSer.
  Context {T : Set} (g : T -> sexp).
  Local Notation ok e := (sexp_forall_atoms atom_raw_okb e = true).

  Lemma raw_ok_mfix (m : mfixpoint T) :
    All (fun d => ok (g (dbody d))) m ->
    ok (@to_sexp _ (@Serialize_mfixpoint _ g) m).
  Proof.
    intros H. unfold to_sexp, Serialize_mfixpoint, to_sexp, Serialize_list.
    apply raw_ok_map_All. eapply All_impl; [exact H|]. intros d Hd.
    unfold to_sexp at 1, Serialize_def. raw_ok_tac.
  Qed.

  Lemma raw_ok_prim (p : prim_val T) :
    primProp (fun t => ok (g t)) p ->
    ok (@to_sexp _ (@Serialize_prim_val _ g) p).
  Proof.
    intros H. destruct H as [i|f|s|a [Hd Hv]];
      unfold to_sexp at 1, Serialize_prim_val; cbn -[to_sexp raw_ok]; repeat raw_ok_step.
    unfold to_sexp at 1, Serialize_product. raw_ok_tac.
    unfold to_sexp at 1, Serialize_array_model. raw_ok_tac.
    unfold to_sexp at 1, Serialize_list. raw_ok_tac.
  Qed.

  Lemma raw_ok_branches {A} `{RawOk A} (brs : list (A * T)) :
    All (fun x => ok (g (snd x))) brs ->
    forallb (sexp_forall_atoms atom_raw_okb)
      (map (@to_sexp _ (@Serialize_product _ _ _ g)) brs) = true.
  Proof.
    intros Hb. apply raw_ok_map_All. eapply All_impl; [exact Hb|]. intros [a t] Ht.
    unfold to_sexp at 1, Serialize_product. raw_ok_tac.
  Qed.
End WithSer.

#[global] Instance RawOk_EAst_term : RawOk EAst.term.
Proof.
  intros t. induction t using EInduction.term_forall_list_ind;
    unfold to_sexp at 1, Serialize_term; cbn -[to_sexp raw_ok];
    repeat (first [exact _ | apply raw_ok_branches | apply raw_ok_mfix | apply raw_ok_prim | raw_ok_step]).
  all: try (eapply primProp_impl; [exact X|]; cbn; intros; assumption).
Qed.

#[global] Instance RawOk_EAst_constructor_body : RawOk EAst.constructor_body.
Proof. raw_ok_inst SerializeEAst.Serialize_constructor_body. Qed.

#[global] Instance RawOk_EAst_projection_body : RawOk EAst.projection_body.
Proof. raw_ok_inst SerializeEAst.Serialize_projection_body. Qed.

#[global] Instance RawOk_EAst_one_inductive_body : RawOk EAst.one_inductive_body.
Proof. raw_ok_inst SerializeEAst.Serialize_one_inductive_body. Qed.

#[global] Instance RawOk_EAst_mutual_inductive_body : RawOk EAst.mutual_inductive_body.
Proof. raw_ok_inst SerializeEAst.Serialize_mutual_inductive_body. Qed.

#[global] Instance RawOk_EAst_constant_body : RawOk EAst.constant_body.
Proof. raw_ok_inst SerializeEAst.Serialize_constant_body. Qed.

#[global] Instance RawOk_EAst_global_decl : RawOk EAst.global_decl.
Proof. raw_ok_inst SerializeEAst.Serialize_global_decl. Qed.

#[global] Instance RawOk_EAst_global_declarations : RawOk EAst.global_declarations.
Proof. intros a. apply RawOk_list. Qed.

(** ** ExAst *)

#[global] Instance RawOk_box_type : RawOk box_type.
Proof.
  intros t; induction t; unfold to_sexp at 1, Serialize_box_type; raw_ok_tac.
Qed.

#[global] Instance RawOk_type_var_info : RawOk type_var_info.
Proof. raw_ok_inst Serialize_type_var_info. Qed.

#[global] Instance RawOk_ExAst_constant_body : RawOk ExAst.constant_body.
Proof. raw_ok_inst SerializeExAst.Serialize_constant_body. Qed.

#[global] Instance RawOk_ExAst_one_inductive_body : RawOk ExAst.one_inductive_body.
Proof. raw_ok_inst SerializeExAst.Serialize_one_inductive_body. Qed.

#[global] Instance RawOk_ExAst_mutual_inductive_body : RawOk ExAst.mutual_inductive_body.
Proof. raw_ok_inst SerializeExAst.Serialize_mutual_inductive_body. Qed.

#[global] Instance RawOk_ExAst_global_decl : RawOk ExAst.global_decl.
Proof. raw_ok_inst SerializeExAst.Serialize_global_decl. Qed.

#[global] Instance RawOk_ExAst_global_env : RawOk ExAst.global_env.
Proof. intros a. apply RawOk_list. Qed.

(** ** PAst *)

#[global] Instance RawOk_typed_env : RawOk typed_env.
Proof. intros a. apply RawOk_list. Qed.

#[global] Instance RawOk_untyped_env : RawOk untyped_env.
Proof. intros a. apply RawOk_list. Qed.

#[global] Instance RawOk_PAst : RawOk PAst.
Proof. raw_ok_inst Serialize_PAst. Qed.
