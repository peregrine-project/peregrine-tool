(** * First-order values of λ□ and the framework for first-order correctness

    This file defines, purely syntactically, the first-order values of λ□ in
    their two representations (applied constructors [fo_app], constructors as
    blocks [fo_blk]), the closed-form value translations performed by the
    middle-end on such values, and a small Hoare-style framework
    ([fo_triple]) for composing per-pass statements along [Transform.t]
    pipelines.

    A pass only needs one [fo_triple]; for a pass given by a [Transform.t] with
    an observational-equivalence relation, [fo_triple_obseq] reduces that to a
    "collapse" lemma about its [obseq] on first-order values. *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EGlobalEnv EProgram.
From MetaRocq.Erasure Require EReorderCstrs.
From MetaRocq.ErasurePlugin Require Import ETransform.

Import Common.Transform.Transform.

Set Default Goal Selector "!".

(** ** Hoare triples over transformations *)

Section Triple.
  Context {env env' term term' value value' : Type}
    {eval : program env term -> value -> Prop}
    {eval' : program env' term' -> value' -> Prop}.

  (** [fo_triple o P Q]: whenever the input program [p] evaluates to a value
      [v] with [P p v], the output of [o] evaluates to some [v'] with
      [Q (o p) v']. *)
  Definition fo_triple (o : Transform.t env env' term term' value value' eval eval')
    (P : program env term -> value -> Prop)
    (Q : program env' term' -> value' -> Prop) : Prop :=
    forall p (pr : pre o p) v, eval p v -> P p v ->
      exists v', eval' (transform o p pr) v' /\ Q (transform o p pr) v'.

  Lemma fo_triple_conseq o (P P' : _ -> _ -> Prop) (Q Q' : _ -> _ -> Prop) :
    (forall p v, P' p v -> P p v) ->
    (forall p v, Q p v -> Q' p v) ->
    fo_triple o P Q -> fo_triple o P' Q'.
  Proof.
    intros HP HQ H p pr v ev Hp.
    destruct (H p pr v ev (HP _ _ Hp)) as [v' [ev' Hq]].
    exists v'; split; auto.
  Qed.

  (** The collapse rule: it suffices to show that [obseq] forces the
      postcondition on the related target value. *)
  Lemma fo_triple_obseq o (P : _ -> _ -> Prop) (Q : _ -> _ -> Prop) :
    (forall p (pr : pre o p) v v', eval p v -> P p v ->
       eval' (transform o p pr) v' -> obseq o p pr (transform o p pr) v v' ->
       Q (transform o p pr) v') ->
    fo_triple o P Q.
  Proof.
    intros H p pr v ev Hp.
    destruct (preservation o p v pr ev) as [v' [ev' Hobs]].
    exists v'; split; eauto.
  Qed.
End Triple.

Section TripleCompose.
  Context {env env' env'' term term' term'' value value' value'' : Type}
    {eval : program env term -> value -> Prop}
    {eval' : program env' term' -> value' -> Prop}
    {eval'' : program env'' term'' -> value'' -> Prop}.

  Lemma fo_triple_compose
    (o : Transform.t env env' term term' value value' eval eval')
    (o' : Transform.t env' env'' term' term'' value' value'' eval' eval'') hpp
    (P : _ -> _ -> Prop) (Q : _ -> _ -> Prop) (R : _ -> _ -> Prop) :
    fo_triple o P Q -> fo_triple o' Q R -> fo_triple (compose o o' hpp) P R.
  Proof.
    intros H H' p pr v ev Hp.
    destruct (H p pr v ev Hp) as [v' [ev' Hq]].
    cbn. unfold run, time.
    destruct (H' _ (hpp _ (correctness o p pr)) v' ev' Hq) as [v'' [ev'' Hr]].
    exists v''; split; auto.
  Qed.
End TripleCompose.

Section TripleOptional.
  Context {env term : Type} {eval : program env term -> term -> Prop}.

  Lemma fo_triple_optional b
    (o : Transform.t env env term term term term eval eval)
    (P : _ -> _ -> Prop) (Q : _ -> _ -> Prop) :
    (forall p v, P p v -> Q p v) ->
    fo_triple o P Q -> fo_triple (optional_self_transform b o) P Q.
  Proof.
    intros HPQ H. destruct b; cbn; auto.
    intros p pr v ev Hp. exists v; cbn; split; auto.
  Qed.
End TripleOptional.

(** ** First-order values *)

(** Primitive literals: integers, floats and strings; arrays are excluded. *)
Definition fo_prim (p : prim_val term) : Prop :=
  match p.π2 with
  | primArrayModel _ => False
  | _ => True
  end.

Lemma fo_prim_map f p : fo_prim p -> map_prim f p = p.
Proof. destruct p as [? []]; cbn; intros H; auto; destruct H. Qed.

(** First-order values with applied constructors (the representation at the
    input of the pipeline): [□], a primitive literal, or a constructor applied
    to first-order values. *)
Inductive fo_app : term -> Prop :=
| fo_app_box : fo_app tBox
| fo_app_prim p : fo_prim p -> fo_app (tPrim p)
| fo_app_construct ind c args :
    Forall fo_app args -> fo_app (mkApps (tConstruct ind c []) args).

(** First-order values with constructors as blocks (the representation from
    the constructors-as-blocks stage on). *)
Inductive fo_blk : term -> Prop :=
| fo_blk_box : fo_blk tBox
| fo_blk_prim p : fo_prim p -> fo_blk (tPrim p)
| fo_blk_construct ind c args :
    Forall fo_blk args -> fo_blk (tConstruct ind c args).

Lemma fo_app_ind' (P : term -> Prop) :
  P tBox ->
  (forall p, fo_prim p -> P (tPrim p)) ->
  (forall ind c args, Forall fo_app args -> Forall P args ->
     P (mkApps (tConstruct ind c []) args)) ->
  forall t, fo_app t -> P t.
Proof.
  intros Hb Hp Hc.
  fix F 2. intros t [| p Hprim | ind c args Hargs].
  - exact Hb.
  - exact (Hp p Hprim).
  - apply Hc; auto.
    induction Hargs as [|x l Hx Hl IH]; constructor; auto.
Qed.

Lemma fo_blk_ind' (P : term -> Prop) :
  P tBox ->
  (forall p, fo_prim p -> P (tPrim p)) ->
  (forall ind c args, Forall fo_blk args -> Forall P args ->
     P (tConstruct ind c args)) ->
  forall t, fo_blk t -> P t.
Proof.
  intros Hb Hp Hc.
  fix F 2. intros t [| p Hprim | ind c args Hargs].
  - exact Hb.
  - exact (Hp p Hprim).
  - apply Hc; auto.
    induction Hargs as [|x l Hx Hl IH]; constructor; auto.
Qed.

(** Saturated first-order values: every constructor is applied to at least
    [ar ind c] arguments. *)
Inductive fo_sat (ar : inductive -> nat -> nat) : term -> Prop :=
| fo_sat_box : fo_sat ar tBox
| fo_sat_prim p : fo_prim p -> fo_sat ar (tPrim p)
| fo_sat_construct ind c args :
    ar ind c <= #|args| -> Forall (fo_sat ar) args ->
    fo_sat ar (mkApps (tConstruct ind c []) args).

Lemma fo_sat_ind' ar (P : term -> Prop) :
  P tBox ->
  (forall p, fo_prim p -> P (tPrim p)) ->
  (forall ind c args, ar ind c <= #|args| -> Forall (fo_sat ar) args -> Forall P args ->
     P (mkApps (tConstruct ind c []) args)) ->
  forall t, fo_sat ar t -> P t.
Proof.
  intros Hb Hp Hc.
  fix F 2. intros t [| p Hprim | ind c args Hle Hargs].
  - exact Hb.
  - exact (Hp p Hprim).
  - apply Hc; [exact Hle|exact Hargs|].
    clear Hle. induction Hargs as [|x l Hx Hl IH]; constructor; auto.
Qed.

Lemma fo_sat_app ar t : fo_sat ar t -> fo_app t.
Proof.
  induction 1 using fo_sat_ind'; constructor; auto.
Qed.

Lemma Forall_map_id {A} (f : A -> A) l :
  Forall (fun x => f x = x) l -> map f l = l.
Proof. induction 1; cbn; congruence. Qed.

Lemma Forall_map_eq {A B} (f g : A -> B) l :
  Forall (fun x => f x = g x) l -> map f l = map g l.
Proof. induction 1; cbn; congruence. Qed.

Lemma Forall_skipn' {A} (P : A -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof.
  revert l; induction n; intros l H; cbn; auto.
  destruct H; cbn; [constructor|apply IHn; assumption].
Qed.

(** ** The value translations of the middle-end, in closed form *)

(** Up to constructors-as-blocks: reorder constructors with the mapping [m],
    drop the parameters ([npars] gives the number of parameters of an
    inductive), and turn the application spine into a block. *)
Fixpoint fo_compile (m : EProgram.inductives_mapping) (npars : inductive -> nat)
  (t : term) (acc : list term) : term :=
  match t with
  | tApp f a => fo_compile m npars f (fo_compile m npars a [] :: acc)
  | tConstruct ind c _ =>
      tConstruct ind (EReorderCstrs.lookup_constructor_ordinal m ind c) (skipn (npars ind) acc)
  | _ => t
  end.

Lemma fo_compile_ext m npars npars' :
  (forall ind, npars ind = npars' ind) ->
  forall t acc, fo_compile m npars t acc = fo_compile m npars' t acc.
Proof.
  intros H t. induction t; intros acc; cbn; auto.
  - now rewrite IHt2 IHt1.
  - now rewrite H.
Qed.

Lemma fo_compile_mkApps m npars f l acc :
  fo_compile m npars (mkApps f l) acc =
  fo_compile m npars f (map (fun a => fo_compile m npars a []) l ++ acc).
Proof.
  revert f acc. induction l using rev_ind; intros f acc; cbn; auto.
  rewrite mkApps_app /= IHl map_app /= -app_assoc //.
Qed.

Lemma fo_compile_construct m npars ind c args :
  fo_compile m npars (mkApps (tConstruct ind c []) args) [] =
  tConstruct ind (EReorderCstrs.lookup_constructor_ordinal m ind c)
    (skipn (npars ind) (map (fun a => fo_compile m npars a []) args)).
Proof. rewrite fo_compile_mkApps /= app_nil_r //. Qed.

Lemma fo_compile_blk m npars t : fo_app t -> fo_blk (fo_compile m npars t []).
Proof.
  induction 1 using fo_app_ind'; try solve [constructor; auto].
  rewrite fo_compile_construct. constructor.
  apply Forall_skipn'. now apply Forall_map.
Qed.

(** Unboxing: a block of an unboxable constructor (according to [ub]) with a
    single argument is replaced by that argument. *)
Fixpoint fo_unbox (ub : inductive -> nat -> bool) (t : term) : term :=
  match t with
  | tConstruct ind c args =>
      match args with
      | [a] => if ub ind c then fo_unbox ub a else tConstruct ind c [fo_unbox ub a]
      | _ => tConstruct ind c (map (fo_unbox ub) args)
      end
  | _ => t
  end.

Lemma fo_unbox_blk ub t : fo_blk t -> fo_blk (fo_unbox ub t).
Proof.
  induction 1 using fo_blk_ind'; try solve [constructor; auto].
  assert (Hm : Forall fo_blk (map (fo_unbox ub) args)) by now apply Forall_map.
  cbn. destruct args as [|a [|b l]]; try solve [constructor; auto].
  destruct (ub ind c).
  - now inversion H0.
  - constructor. exact Hm.
Qed.
