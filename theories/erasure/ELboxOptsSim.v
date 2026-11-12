(** * Evaluation preservation for the lambda-box simplifications of [ELboxOpts]

    [R Σ' t t'] relates a source term [t] to a target term [t'] obtained by
    rewriting some subterms of [t] with the local rewrites of [ELboxOpts]
    (one layer of rewrites: every rule looks at the shape of the *source*
    term).  [optimize] is a finite sequence of such steps, and each step is a
    forward simulation for [EWcbvEval.eval] at the flags of the pipeline stage
    (constructors as blocks, unguarded fixpoints, no propositional cases).

    Besides the congruence rules and the rewrite rules, [R] has rules that keep
    the source fixed and expand the target ([R_cofix], ...): they describe the
    terms that appear at run time once the rewritten program has taken steps
    the source program has not (for instance, an identity case on a cofixpoint
    is removed, so the target holds an unfolded-later cofixpoint where the
    source holds a constructor). *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool Relations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst ECSubst
  EGlobalEnv EWcbvEval EProgram EWellformed.
From Peregrine Require Import ELboxOpts.
From Equations Require Import Equations.

Import ListNotations.
Local Open Scope bool_scope.

(** ** Identity-case branches *)

Definition all_rebuild (ind : inductive) (brs : list (list name × term)) : bool :=
  forallb (fun '(i, br) => rebuilds ind i br) (combine (seq 0 #|brs|) brs).

Lemma forallb_combine_seq {A} (f : nat -> A -> bool) (l : list A) s c x :
  forallb (fun '(i, x) => f i x) (combine (seq s #|l|) l) ->
  nth_error l c = Some x -> f (s + c) x.
Proof.
  induction l in s, c |- *; cbn; [destruct c; discriminate|].
  move/andP => [Hx Hl]. destruct c; cbn.
  - intros [= <-]. now rewrite Nat.add_0_r.
  - intros H. rewrite -Nat.add_succ_comm. now apply IHl.
Qed.

Lemma all_rebuild_nth ind brs c br :
  all_rebuild ind brs -> nth_error brs c = Some br -> rebuilds ind c br.
Proof. intros H E. exact (forallb_combine_seq (rebuilds ind) brs 0 c br H E). Qed.

Lemma rels_spec (n : nat) (l : list term) s :
  forallb (fun '(p, a) => match a with tRel r => Nat.eqb r (n - 1 - p) | _ => false end)
    (combine (seq s #|l|) l) ->
  l = map (fun p => tRel (n - 1 - p)) (seq s #|l|).
Proof.
  induction l in s |- *; cbn; auto.
  move/andP => [Hx Hl]. destruct a; try discriminate.
  apply Nat.eqb_eq in Hx. subst. f_equal. now apply IHl.
Qed.

Lemma rebuilds_spec ind i br :
  rebuilds ind i br ->
  exists args0 args1, br.2 = mkApps (tConstruct ind i args0) args1 /\
    args0 ++ args1 = map (fun p => tRel (#|br.1| - 1 - p)) (seq 0 #|br.1|).
Proof.
  unfold rebuilds. destruct decompose_app as [hd args1] eqn:E.
  apply decompose_app_inv in E.
  destruct hd; try discriminate.
  move/andP => [/andP [/andP [Hi Hc] Hn] Hr].
  apply Nat.eqb_eq in Hc, Hn.
  match type of Hi with is_true (_ == ?x) => destruct (eqb_spec ind x); [|discriminate] end.
  subst. exists args, args1. split; [exact E|].
  rewrite -Hn in Hr |- *. now apply rels_spec.
Qed.

Lemma rebuilds_closed ind i br : rebuilds ind i br -> closedn #|br.1| br.2.
Proof.
  intros (args0 & args1 & -> & E)%rebuilds_spec.
  rewrite closedn_mkApps /=.
  rewrite -forallb_app E forallb_map.
  apply forallb_forall. intros p Hp%in_seq. cbn. apply Nat.ltb_lt. lia.
Qed.

Lemma all_rebuild_csubst ind brs a k :
  all_rebuild ind brs ->
  map (fun br => (br.1, csubst a (#|br.1| + k) br.2)) brs = brs.
Proof.
  intros H. rewrite -{2}(map_id brs). apply map_ext_in. intros br Hbr.
  apply In_nth_error in Hbr as [c Hc].
  have Hcl := rebuilds_closed _ _ _ (all_rebuild_nth _ _ _ _ H Hc).
  destruct br; cbn in *. f_equal. apply csubst_closed.
  eapply closed_upwards; tea. lia.
Qed.

(** ** The relation *)

Section Rel.
  Context {wfl : WcbvFlags} (Σ' : global_declarations).

  Inductive R : term -> term -> Prop :=
  | R_head t t' : Rh t t' -> R t t'
  (** the target is a cofixpoint whose unfolding evaluates to (something
      related to) the source constructor *)
  | R_cofix ind c args v0 mfix idx args' narg fn :
      R (tConstruct ind c args) v0 ->
      ∥ eval Σ' (mkApps fn args') v0 ∥ ->
      cunfold_cofix mfix idx = Some (narg, fn) ->
      ∥ value Σ' (mkApps (tCoFix mfix idx) args') ∥ ->
      closed (mkApps (tCoFix mfix idx) args') -> closed v0 ->
      R (tConstruct ind c args) (mkApps (tCoFix mfix idx) args')
  with Rh : term -> term -> Prop :=
  | Rh_box : Rh tBox tBox
  | Rh_rel n : Rh (tRel n) (tRel n)
  | Rh_var na : Rh (tVar na) (tVar na)
  | Rh_const kn : Rh (tConst kn) (tConst kn)
  | Rh_evar n ts ts' : Rs ts ts' -> Rh (tEvar n ts) (tEvar n ts')
  | Rh_lambda na b b' : R b b' -> Rh (tLambda na b) (tLambda na b')
  | Rh_letin na v v' b b' : R v v' -> R b b' -> Rh (tLetIn na v b) (tLetIn na v' b')
  | Rh_app f f' a a' : R f f' -> R a a' -> Rh (tApp f a) (tApp f' a')
  | Rh_case ci d d' brs brs' : R d d' -> Rbrs brs brs' -> Rh (tCase ci d brs) (tCase ci d' brs')
  | Rh_proj p u u' : R u u' -> Rh (tProj p u) (tProj p u')
  | Rh_fix mf mf' idx : Rdefs mf mf' -> Rh (tFix mf idx) (tFix mf' idx)
  | Rh_cofix mf mf' idx : Rdefs mf mf' -> Rh (tCoFix mf idx) (tCoFix mf' idx)
  | Rh_construct ind c args args' : Rs args args' -> Rh (tConstruct ind c args) (tConstruct ind c args')
  | Rh_prim_int i : Rh (tPrim (prim_int i)) (tPrim (prim_int i))
  | Rh_prim_float f : Rh (tPrim (prim_float f)) (tPrim (prim_float f))
  | Rh_prim_string s : Rh (tPrim (prim_string s)) (tPrim (prim_string s))
  | Rh_prim_array d d' v v' :
      R d d' -> Rs v v' ->
      Rh (tPrim (prim_array {| array_default := d; array_value := v |}))
         (tPrim (prim_array {| array_default := d'; array_value := v' |}))
  | Rh_lazy u u' : R u u' -> Rh (tLazy u) (tLazy u')
  | Rh_force u u' : R u u' -> Rh (tForce u) (tForce u')
  (** [case_id] *)
  | Rh_case_id ind p d d' brs :
      R d d' -> all_rebuild ind brs -> Rh (tCase (ind, p) d brs) d'
  with Rs : list term -> list term -> Prop :=
  | Rs_nil : Rs [] []
  | Rs_cons t t' l l' : R t t' -> Rs l l' -> Rs (t :: l) (t' :: l')
  with Rbrs : list (list name × term) -> list (list name × term) -> Prop :=
  | Rbrs_nil : Rbrs [] []
  | Rbrs_cons n b b' l l' : R b b' -> Rbrs l l' -> Rbrs ((n, b) :: l) ((n, b') :: l')
  with Rdefs : mfixpoint term -> mfixpoint term -> Prop :=
  | Rdefs_nil : Rdefs [] []
  | Rdefs_cons na b b' r l l' :
      R b b' -> Rdefs l l' ->
      Rdefs ({| dname := na; dbody := b; rarg := r |} :: l)
            ({| dname := na; dbody := b'; rarg := r |} :: l').

  Scheme R_mind := Minimality for R Sort Prop
  with Rh_mind := Minimality for Rh Sort Prop
  with Rs_mind := Minimality for Rs Sort Prop
  with Rbrs_mind := Minimality for Rbrs Sort Prop
  with Rdefs_mind := Minimality for Rdefs Sort Prop.
  Combined Scheme R_mutind from R_mind, Rh_mind, Rs_mind, Rbrs_mind, Rdefs_mind.

  Definition br_rel (br br' : list name × term) := br.1 = br'.1 /\ R br.2 br'.2.
  Definition def_rel (d d' : def term) :=
    dname d = dname d' /\ rarg d = rarg d' /\ R (dbody d) (dbody d').

  Lemma Rs_Forall2 l l' : Rs l l' <-> Forall2 R l l'.
  Proof. split; induction 1; constructor; auto. Qed.

  Lemma Rbrs_Forall2 l l' : Rbrs l l' <-> Forall2 br_rel l l'.
  Proof.
    split; induction 1; try constructor; auto.
    - split; auto.
    - destruct x, y, H; cbn in *; subst. now constructor.
  Qed.

  Lemma Rdefs_Forall2 l l' : Rdefs l l' <-> Forall2 def_rel l l'.
  Proof.
    split; induction 1; try constructor; auto.
    - repeat split; auto.
    - destruct x, y, H as (? & ? & ?); cbn in *; subst. now constructor.
  Qed.

  Lemma Rs_length l l' : Rs l l' -> #|l| = #|l'|.
  Proof. intros H%Rs_Forall2. exact (Forall2_length H). Qed.
  Lemma Rbrs_length l l' : Rbrs l l' -> #|l| = #|l'|.
  Proof. intros H%Rbrs_Forall2. exact (Forall2_length H). Qed.
  Lemma Rdefs_length l l' : Rdefs l l' -> #|l| = #|l'|.
  Proof. intros H%Rdefs_Forall2. exact (Forall2_length H). Qed.

  Lemma R_refl t : R t t.
  Proof.
    induction t using term_forall_list_ind; apply R_head; try (constructor; auto; fail).
    all: try (constructor; auto;
              first [apply Rs_Forall2 | apply Rbrs_Forall2 | apply Rdefs_Forall2];
              induction X; constructor; auto; repeat split; auto; fail).
    destruct p as [? []]; try constructor. depelim X. destruct p as [Hd Hv].
    destruct a; cbn in *. constructor; auto.
    apply Rs_Forall2. induction Hv; constructor; auto.
  Qed.

  Lemma Rs_refl l : Rs l l.
  Proof. induction l; constructor; auto using R_refl. Qed.

  Lemma R_mkApps f f' args args' :
    R f f' -> Rs args args' -> R (mkApps f args) (mkApps f' args').
  Proof.
    intros Hf H. induction H in f, f', Hf |- *; cbn; auto.
    apply IHRs. now apply R_head, Rh_app.
  Qed.

  (** *** Closedness *)

  Lemma R_closed_mut :
    (forall t t', R t t' -> forall k, closedn k t -> closedn k t') /\
    (forall t t', Rh t t' -> forall k, closedn k t -> closedn k t') /\
    (forall l l', Rs l l' -> forall k, forallb (closedn k) l -> forallb (closedn k) l') /\
    (forall l l', Rbrs l l' -> forall k,
      forallb (fun br => closedn (#|br.1| + k) br.2) l ->
      forallb (fun br => closedn (#|br.1| + k) br.2) l') /\
    (forall l l', Rdefs l l' -> forall k,
      forallb (test_def (closedn k)) l -> forallb (test_def (closedn k)) l').
  Proof.
    apply R_mutind; intros; cbn in *; auto.
    all: try (rtoProp; intuition eauto; fail).
    - eapply closed_upwards; tea. lia.
    - rewrite -(Rdefs_length _ _ H). auto.
    - rewrite -(Rdefs_length _ _ H). auto.
    - unfold test_array_model in *; cbn in *. rtoProp; intuition eauto.
  Qed.

  Lemma R_closed t t' k : R t t' -> closedn k t -> closedn k t'.
  Proof. intros H. exact (proj1 R_closed_mut _ _ H k). Qed.

  Lemma Rs_closed l l' k : Rs l l' -> forallb (closedn k) l -> forallb (closedn k) l'.
  Proof. intros H. exact (proj1 (proj2 (proj2 R_closed_mut)) _ _ H k). Qed.

  (** *** Substitution *)

  Lemma R_csubst_mut a a' : R a a' -> closed a' ->
    (forall t t', R t t' -> forall k, R (csubst a k t) (csubst a' k t')) /\
    (forall t t', Rh t t' -> forall k, R (csubst a k t) (csubst a' k t')) /\
    (forall l l', Rs l l' -> forall k, Rs (map (csubst a k) l) (map (csubst a' k) l')) /\
    (forall l l', Rbrs l l' -> forall k,
      Rbrs (map (fun br => (br.1, csubst a (#|br.1| + k) br.2)) l)
           (map (fun br => (br.1, csubst a' (#|br.1| + k) br.2)) l')) /\
    (forall l l', Rdefs l l' -> forall k,
      Rdefs (map (map_def (csubst a k)) l) (map (map_def (csubst a' k)) l')).
  Proof.
    intros Ha cla. apply R_mutind; intros; cbn; auto.
    all: try (constructor; eauto; fail).
    all: try (apply R_head; constructor; eauto; fail).
    - (* cofix expansion *)
      rewrite (csubst_closed a' k (mkApps _ _)); [eapply closed_upwards; tea; lia|].
      specialize (H0 k). rewrite (csubst_closed a' k v0) in H0; [eapply closed_upwards; tea; lia|].
      cbn in H0. eapply R_cofix; eauto.
    - destruct (Nat.compare k n); auto; apply R_head; constructor.
    - apply R_head. rewrite -(Rdefs_length _ _ H). constructor. auto.
    - apply R_head. rewrite -(Rdefs_length _ _ H). constructor. auto.
    - erewrite all_rebuild_csubst; tea. apply R_head. constructor; auto.
  Qed.

  Lemma R_csubst a a' t t' k :
    R a a' -> closed a' -> R t t' -> R (csubst a k t) (csubst a' k t').
  Proof. intros Ha cla H. exact (proj1 (R_csubst_mut a a' Ha cla) _ _ H k). Qed.

  Lemma R_substl s s' t t' :
    Rs s s' -> forallb (closedn 0) s' -> R t t' -> R (substl s t) (substl s' t').
  Proof.
    unfold substl. intros H. induction H in t, t' |- *; cbn; auto.
    move/andP => [cl cls] Ht. apply IHRs; auto. now apply R_csubst.
  Qed.

  Lemma Rs_rev l l' : Rs l l' -> Rs (List.rev l) (List.rev l').
  Proof.
    rewrite !Rs_Forall2. induction 1; cbn; [constructor|]. apply Forall2_app; auto.
  Qed.

  Lemma Rs_skipn n l l' : Rs l l' -> Rs (skipn n l) (skipn n l').
  Proof. rewrite !Rs_Forall2. apply Forall2_skipn. Qed.

  Lemma Rs_nth_error l l' n x :
    Rs l l' -> nth_error l n = Some x -> exists x', nth_error l' n = Some x' /\ R x x'.
  Proof.
    intros H. induction H in n |- *; destruct n; cbn; try discriminate; eauto.
    intros [= <-]. eauto.
  Qed.

  Lemma Rbrs_nth_error l l' n br :
    Rbrs l l' -> nth_error l n = Some br ->
    exists br', nth_error l' n = Some br' /\ br.1 = br'.1 /\ R br.2 br'.2.
  Proof.
    intros H. induction H in n |- *; destruct n; cbn; try discriminate; eauto.
    intros [= <-]. eexists; split; [reflexivity|]. cbn. auto.
  Qed.

  Lemma Rdefs_nth_error l l' n d :
    Rdefs l l' -> nth_error l n = Some d ->
    exists d', nth_error l' n = Some d' /\ rarg d = rarg d' /\ R (dbody d) (dbody d').
  Proof.
    intros H. induction H in n |- *; destruct n; cbn; try discriminate; eauto.
    intros [= <-]. eexists; split; [reflexivity|]. cbn. auto.
  Qed.

  Lemma R_fix_subst mf mf' : Rdefs mf mf' -> Rs (fix_subst mf) (fix_subst mf').
  Proof.
    intros H. unfold fix_subst. rewrite (Rdefs_length _ _ H).
    induction #|mf'|; constructor; auto. now apply R_head, Rh_fix.
  Qed.

  Lemma R_cofix_subst mf mf' : Rdefs mf mf' -> Rs (cofix_subst mf) (cofix_subst mf').
  Proof.
    intros H. unfold cofix_subst. rewrite (Rdefs_length _ _ H).
    induction #|mf'|; constructor; auto. now apply R_head, Rh_cofix.
  Qed.

  Lemma closed_fix_subst' mf idx : closed (tFix mf idx) -> forallb (closedn 0) (fix_subst mf).
  Proof.
    intros H. unfold fix_subst. induction #|mf|; cbn; auto; try (apply/andP; split; auto).
  Qed.

  Lemma closed_cofix_subst' mf idx : closed (tCoFix mf idx) -> forallb (closedn 0) (cofix_subst mf).
  Proof.
    intros H. unfold cofix_subst. induction #|mf|; cbn; auto; try (apply/andP; split; auto).
  Qed.

  Lemma R_cunfold_fix mf mf' idx narg fn :
    Rdefs mf mf' -> closed (tFix mf' idx) -> cunfold_fix mf idx = Some (narg, fn) ->
    exists fn', cunfold_fix mf' idx = Some (narg, fn') /\ R fn fn'.
  Proof.
    intros H cl. unfold cunfold_fix. destruct nth_error eqn:E; [|discriminate].
    intros [= <- <-].
    destruct (Rdefs_nth_error _ _ _ _ H E) as (d' & -> & Hr & Hb).
    eexists; split; [now rewrite Hr|]. apply R_substl; auto.
    - now apply R_fix_subst.
    - eapply closed_fix_subst'; tea.
  Qed.

  Lemma R_cunfold_cofix mf mf' idx narg fn :
    Rdefs mf mf' -> closed (tCoFix mf' idx) -> cunfold_cofix mf idx = Some (narg, fn) ->
    exists fn', cunfold_cofix mf' idx = Some (narg, fn') /\ R fn fn'.
  Proof.
    intros H cl. unfold cunfold_cofix. destruct nth_error eqn:E; [|discriminate].
    intros [= <- <-].
    destruct (Rdefs_nth_error _ _ _ _ H E) as (d' & -> & Hr & Hb).
    eexists; split; [now rewrite Hr|]. apply R_substl; auto.
    - now apply R_cofix_subst.
    - eapply closed_cofix_subst'; tea.
  Qed.

  Lemma R_iota_red pars args args' br br' :
    Rs args args' -> forallb (closedn 0) args' -> R br.2 br'.2 ->
    R (iota_red pars args br) (iota_red pars args' br').
  Proof.
    intros Ha cl Hb. unfold iota_red. apply R_substl; auto.
    - now apply Rs_rev, Rs_skipn.
    - rewrite forallb_rev. now apply forallb_skipn.
  Qed.

End Rel.
