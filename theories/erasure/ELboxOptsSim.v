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
From Peregrine Require Import ELboxOpts ELboxOptsSimDB.
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

  (** Head reduction steps of the target whose principal part is closed
      and evaluates. *)
  Inductive tred : term -> term -> Prop :=
  | tred_iota ind pars cdecl d c args brs br :
      ∥ eval Σ' d (tConstruct ind c args) ∥ -> closed d -> forallb (closedn 0) args ->
      constructor_isprop_pars_decl Σ' ind c = Some (false, pars, cdecl) ->
      nth_error brs c = Some br ->
      #|args| = pars + cstr_nargs cdecl -> #|skipn pars args| = #|br.1| ->
      tred (tCase (ind, pars) d brs) (iota_red pars args br)
  | tred_cofix ip d mfix idx args narg fn brs :
      ∥ eval Σ' d (mkApps (tCoFix mfix idx) args) ∥ -> closed d ->
      cunfold_cofix mfix idx = Some (narg, fn) -> closed (mkApps fn args) ->
      tred (tCase ip d brs) (tCase ip (mkApps fn args) brs)
  | tred_scrut ip d v brs :
      ∥ eval Σ' d v ∥ -> closed d -> closed v -> tred (tCase ip d brs) (tCase ip v brs).

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
  (** the target is any closed term evaluating to something related *)
  | R_eval t v0 t' :
      R t v0 -> ∥ eval Σ' t' v0 ∥ -> closed t' -> closed v0 -> R t t'
  (** the target, under some lambdas, head-reduces to something related *)
  | R_exp ys s u t' :
      R s (mk_lambdas ys u) -> tred t' u ->
      closed (mk_lambdas ys u) -> closed (mk_lambdas ys t') ->
      R s (mk_lambdas ys t')
  with Rh : term -> term -> Prop :=
  | Rh_box : Rh tBox tBox
  | Rh_rel n : Rh (tRel n) (tRel n)
  | Rh_var na : Rh (tVar na) (tVar na)
  | Rh_const kn : Rh (tConst kn) (tConst kn)
  | Rh_evar n ts ts' : Rs ts ts' -> Rh (tEvar n ts) (tEvar n ts')
  | Rh_lambda na na' b b' : R b b' -> Rh (tLambda na b) (tLambda na' b')
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
  (** [beta_let]: beta-reduction, and pushing an argument into a let or
      into the branches of a case *)
  | Rh_beta na b b' a a' :
      R b b' -> R a a' -> Rh (tApp (tLambda na b) a) (subst1 a' 0 b')
  | Rh_app_let z v v' b b' a a' :
      R v v' -> R b b' -> R a a' ->
      Rh (tApp (tLetIn z v b) a) (tLetIn z v' (tApp b' (lift0 1 a')))
  | Rh_app_case ci d d' brs brs' a a' :
      R d d' -> Rbrs brs brs' -> R a a' ->
      Rh (tApp (tCase ci d brs) a)
         (tCase ci d' (map (fun br => (br.1, tApp br.2 (lift0 #|br.1| a'))) brs'))
  (** [let_inline] (for any let-bound term: the source evaluates it to a
      value before substituting it, and the target substitutes the term) *)
  | Rh_let_inline z v v' b b' :
      R v v' -> R b b' -> Rh (tLetIn z v b) (subst1 v' 0 b')
  (** [case_fun] *)
  | Rh_case_fun ci d d' brs brs1 ys :
      R d d' -> forallb (fun br => has_lambdas #|ys| br.2) brs ->
      Rbrs (map (fun br => (br.1, strip_lambdas #|ys| br.2)) brs) brs1 ->
      Rh (tCase ci d brs)
         (mk_lambdas ys (tCase ci (lift0 #|ys| d')
            (map (fun br => (br.1, exchange #|ys| #|br.1| 0 br.2)) brs1)))
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

  Lemma csubst_subst1 a k x b :
    closed a -> csubst a k (subst1 x 0 b) = subst1 (csubst a k x) 0 (csubst a (S k) b).
  Proof.
    intros cl. rewrite !closed_subst //. unfold subst1. now rewrite distr_subst.
  Qed.

  Lemma csubst_lift0 a n k x :
    closed a -> csubst a (n + k) (lift0 n x) = lift0 n (csubst a k x).
  Proof.
    intros cl. rewrite !closed_subst //.
    rewrite (commut_lift_subst_rec x [a] n k 0); [lia|]. now rewrite Nat.add_comm.
  Qed.

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
    - eapply closed_upwards; tea. lia.
    - eapply closed_upwards; tea. lia.
    - rewrite -(Rdefs_length _ _ H). auto.
    - rewrite -(Rdefs_length _ _ H). auto.
    - unfold test_array_model in *; cbn in *. rtoProp; intuition eauto.
    - (* beta *)
      move/andP: H3 => [cb ca]. apply closedn_subst; cbn; rewrite ?H2 //. apply H0. exact cb.
    - (* app let *)
      rtoProp. intuition eauto. rewrite -Nat.add_1_r. apply closedn_lift. eauto.
    - (* app case *)
      rtoProp. intuition eauto. rewrite forallb_map. cbn.
      specialize (H2 k ltac:(assumption)). specialize (H4 k ltac:(assumption)).
      solve_all. rtoProp. split; auto. rewrite Nat.add_comm. now apply closedn_lift.
    - (* let_inline *)
      move/andP: H3 => [cv cb]. apply closedn_subst; cbn; rewrite ?H0 //. apply H2. exact cb.
    - (* case_fun *)
      move/andP: H4 => [cd cb]. rewrite closedn_mk_lambdas. cbn. apply/andP; split.
      + rewrite Nat.add_comm. apply closedn_lift. auto.
      + specialize (H3 (#|ys| + k)). rewrite forallb_map in H3. cbn in H3.
        rewrite forallb_map. cbn.
        forward H3.
        { solve_all. replace (#|x.1| + (#|ys| + k)) with (#|ys| + (#|x.1| + k)) by lia.
          now apply closedn_strip_lambdas. }
        solve_all. apply closedn_exchange; [lia|auto].
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
    - (* evaluation *)
      rewrite (csubst_closed a' k t'); [eapply closed_upwards; tea; lia|].
      specialize (H0 k). rewrite (csubst_closed a' k v0) in H0; [eapply closed_upwards; tea; lia|].
      eapply R_eval; eauto.
    - (* head expansion *)
      rewrite (csubst_closed a' k (mk_lambdas ys t')); [eapply closed_upwards; tea; lia|].
      specialize (H0 k).
      rewrite (csubst_closed a' k (mk_lambdas ys u)) in H0; [eapply closed_upwards; tea; lia|].
      eapply R_exp; eauto.
    - destruct (Nat.compare k n); auto; apply R_head; constructor.
    - apply R_head. rewrite -(Rdefs_length _ _ H). constructor. auto.
    - apply R_head. rewrite -(Rdefs_length _ _ H). constructor. auto.
    - erewrite all_rebuild_csubst; tea. apply R_head. constructor; auto.
    - rewrite csubst_subst1 //. apply R_head, Rh_beta; auto.
    - rewrite (csubst_lift0 a' 1 k) //. apply R_head, Rh_app_let; auto.
    - assert (E : forall L x,
        map (fun br : list name × term => (br.1, csubst a' (#|br.1| + k) br.2))
          (map (fun br : list name × term => (br.1, tApp br.2 (lift0 #|br.1| x))) L) =
        map (fun br : list name × term => (br.1, tApp br.2 (lift0 #|br.1| (csubst a' k x))))
          (map (fun br : list name × term => (br.1, csubst a' (#|br.1| + k) br.2)) L)).
      { intros L x. rewrite !map_map. apply map_ext. intros [n b0]. cbn. now rewrite csubst_lift0. }
      rewrite E.
      apply R_head, Rh_app_case; auto.
    - (* let_inline *)
      rewrite csubst_subst1 //. apply R_head, Rh_let_inline; auto.
    - (* case_fun *)
      rewrite csubst_mk_lambdas. cbn.
      rewrite (csubst_lift0 a' #|ys| k) //.
      match goal with |- R _ (mk_lambdas ys (tCase ci _ ?B)) =>
        replace B with
          (map (fun br : list name × term => (br.1, exchange #|ys| #|br.1| 0 br.2))
             (map (fun br : list name × term => (br.1, csubst a' (#|br.1| + (#|ys| + k)) br.2)) brs1))
      end.
      2:{ rewrite !map_map. apply map_ext. intros [n b0]. cbn. rewrite csubst_exchange //; lia. }
      apply R_head, Rh_case_fun; auto.
      + rewrite forallb_map. cbn. solve_all. now apply has_lambdas_csubst.
      + specialize (H3 (#|ys| + k)).
        match type of H3 with Rbrs ?X _ =>
          match goal with |- Rbrs ?Y _ => replace Y with X end end; [exact H3|].
        rewrite !map_map. apply map_ext_in. intros x Hin. cbn. f_equal.
        rewrite strip_lambdas_csubst; [exact (proj1 (forallb_forall _ _) H1 x Hin)|].
        f_equal. lia.
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

(** ** Evaluation at the flags of the pipeline stage *)

Lemma map_seq_nth {A} (g : nat -> A) l s :
  (forall p a, nth_error l p = Some a -> g (s + p) = a) -> map g (seq s #|l|) = l.
Proof.
  induction l in s |- *; cbn; intros H; f_equal.
  - rewrite -(H 0 a eq_refl). now rewrite Nat.add_0_r.
  - apply IHl. intros p x Hp. rewrite Nat.add_succ_comm. now apply (H (S p)).
Qed.

Lemma rebuild_iota ind c br args :
  rebuilds ind c br -> #|args| = #|br.1| -> forallb (closedn 0) args ->
  exists args0 args1,
    iota_red 0 args br = mkApps (tConstruct ind c args0) args1 /\ args0 ++ args1 = args.
Proof.
  intros (l0 & l1 & E & El)%rebuilds_spec Hn cl.
  unfold iota_red. rewrite skipn_0 E substl_subst; [now rewrite forallb_rev|].
  rewrite subst_mkApps. cbn.
  eexists _, _. split; [reflexivity|].
  rewrite -map_app El map_map -Hn. apply map_seq_nth.
  intros p a Hp. cbn. rewrite Nat.sub_0_r.
  replace (#|args| - 1 - p) with (#|args| - S p) by lia.
  rewrite -nth_error_rev; [apply nth_error_Some_length in Hp; lia|].
  rewrite Hp. apply lift0_id.
Qed.

Section Flags.
  Context {wfl : WcbvFlags}.
  Hypothesis Hblock : with_constructor_as_block = true.
  Hypothesis Hguard : with_guarded_fix = false.
  Hypothesis Hprop : with_prop_case = false.
  Variable Σ : global_declarations.

  Lemma value_cofix_app mfix idx args :
    All (value Σ) args -> value Σ (mkApps (tCoFix mfix idx) args).
  Proof.
    intros H. destruct args.
    - cbn. now do 2 constructor.
    - eapply value_app_nonnil; auto; [constructor|discriminate].
  Qed.

  Lemma value_tApp_inv f a :
    value Σ (tApp f a) ->
    ∑ mfix idx args, f = mkApps (tCoFix mfix idx) args × All (value Σ) (args ++ [a]).
  Proof.
    intros H. remember (tApp f a) as t eqn:E.
    destruct H as [? X|? ? ? ? ? ? ? ? ? ?|f0 args vh nn al].
    - exfalso. destruct X as [? i|?]; subst; [cbn in i|]; discriminate.
    - discriminate.
    - destruct (exists_last nn) as (l & x & ->). rewrite mkApps_app in E. cbn in E.
      injection E as <- <-.
      destruct vh.
      + congruence.
      + eexists _, _, _. split; [reflexivity|auto].
      + rewrite Hguard in y. destruct y.
  Qed.

  Lemma eval_case_scrut ip d v0 brs r :
    eval Σ d v0 -> eval Σ (tCase ip v0 brs) r -> eval Σ (tCase ip d brs) r.
  Proof.
    intros ev H. depelim H.
    all: try solve [econstructor; tea; eapply eval_trans; tea].
    cbn in i. discriminate.
  Qed.

  Lemma eval_proj_scrut p d v0 r :
    eval Σ d v0 -> eval Σ (tProj p v0) r -> eval Σ (tProj p d) r.
  Proof.
    intros ev H. depelim H.
    all: try solve [econstructor; tea; eapply eval_trans; tea].
    cbn in i. discriminate.
  Qed.

  (** [unfolds w v]: the value [w] becomes [v] by unfolding cofixpoints at
      the head and evaluating. *)
  Inductive unfolds : term -> term -> Prop :=
  | unfolds_refl v : unfolds v v
  | unfolds_step mfix idx args narg fn v0 v :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      ∥ value Σ (mkApps (tCoFix mfix idx) args) ∥ ->
      ∥ eval Σ (mkApps fn args) v0 ∥ -> unfolds v0 v ->
      unfolds (mkApps (tCoFix mfix idx) args) v.

  Lemma unfolds_case w v ip brs r :
    unfolds w v -> eval Σ (tCase ip v brs) r -> ∥ eval Σ (tCase ip w brs) r ∥.
  Proof.
    induction 1; intros ev; [now sq|].
    destruct (IHunfolds ev) as [ev']. destruct H0 as [vv], H1 as [e1]. sq.
    eapply eval_cofix_case; tea; first [now apply value_final | eapply eval_case_scrut; tea].
  Qed.

  Lemma unfolds_proj w v p r :
    unfolds w v -> eval Σ (tProj p v) r -> ∥ eval Σ (tProj p w) r ∥.
  Proof.
    induction 1; intros ev; [now sq|].
    destruct (IHunfolds ev) as [ev']. destruct H0 as [vv], H1 as [e1]. sq.
    eapply eval_cofix_proj; tea; first [now apply value_final | eapply eval_proj_scrut; tea].
  Qed.

  (** *** Identity cases evaluate to their scrutinee *)

  Hypothesis HclΣ : closed_env Σ.
  Hypothesis Hpars : forall ind c b pars cdecl,
    constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) -> pars = 0.

  Lemma case_id_iota ind c br args res :
    rebuilds ind c br -> #|args| = #|br.1| -> forallb (closedn 0) args ->
    value Σ (tConstruct ind c args) ->
    eval Σ (iota_red 0 args br) res -> res = tConstruct ind c args.
  Proof.
    intros Hr Hn cl V.
    destruct (rebuild_iota _ _ _ _ Hr Hn cl) as (args0 & args1 & -> & E). intros ev.
    destruct (eval_mkApps_Construct_block_inv _ _ _ _ _ _ Hblock ev) as (args' & -> & _ & _).
    cbn in ev. rewrite app_nil_r in E. subst. symmetry. eapply eval_value; tea.
  Qed.

  Lemma case_id_result t v :
    eval Σ t v -> forall ind p d brs, t = tCase (ind, p) d brs -> closed d ->
    all_rebuild ind brs -> exists c args, v = tConstruct ind c args.
  Proof.
    induction 1; intros ind0 p0 d0 brs0 E cl Hb; try discriminate.
    all: try (exfalso; unfold is_true in *; congruence).
    - injection E; intros; subst.
      match goal with H : constructor_isprop_pars_decl _ _ _ = Some (_, ?q, _) |- _ =>
        pose proof (Hpars _ _ _ _ _ H) as Hq; rewrite Hq in H; try subst q end.
      match goal with H : eval Σ ?d (tConstruct _ _ _) |- _ =>
        have clv := eval_closed Σ HclΣ _ _ cl H; have vv := eval_to_value _ _ H end.
      cbn in clv.
      match goal with H : #|skipn 0 _| = _ |- _ => rewrite skipn_0 in H end.
      do 2 eexists. eapply case_id_iota; tea.
      eapply all_rebuild_nth; tea.
    - injection E; intros; subst.
      eapply IHeval2; [reflexivity| |tea].
      have clv := eval_closed Σ HclΣ _ _ cl H. rewrite closedn_mkApps in clv.
      move/andP: clv => [clf cla]. rewrite closedn_mkApps. apply/andP; split; auto.
      eapply closed_cunfold_cofix; tea.
    - subst. cbn in i. discriminate.
  Qed.

  (** *** Applications: pushing an argument into a let or a case *)

  Lemma eval_lambda_inv na b v : eval Σ (tLambda na b) v -> v = tLambda na b.
  Proof. intros ev. exact (eval_deterministic ev (eval_atom Σ (tLambda na b) eq_refl)). Qed.

  Lemma value_app_head f a : value Σ (tApp f a) -> value Σ f.
  Proof.
    intros H. destruct (value_tApp_inv _ _ H) as (mfix & idx & args & -> & Hall).
    apply value_cofix_app. eapply All_app in Hall as [? _]. assumption.
  Qed.

  Lemma mkApps_cofix_head mf idx args :
    match mkApps (tCoFix mf idx) args with
    | tLambda _ _ | tLetIn _ _ _ | tCase _ _ _ => False
    | _ => True
    end.
  Proof. destruct args using rev_case; rewrite ?mkApps_app; cbn; auto. Qed.

  Ltac flag_contra :=
    solve [ exfalso; unfold is_true in *; congruence
          | match goal with H : atom _ _ |- _ => cbn in H; discriminate end
          | match goal with H : is_true (atom _ _) |- _ => cbn in H; discriminate end ].

  Lemma eval_app_inv f a r :
    eval Σ (tApp f a) r -> ∑ fv, eval Σ f fv × eval Σ (tApp fv a) r.
  Proof.
    intros ev. depelim ev; try flag_contra.
    all: eexists; split; [eassumption|].
    all: let fin := try eassumption; try (eapply value_final, eval_to_value; eassumption) in
      first [ solve [eapply eval_box; fin] | solve [eapply eval_beta; fin]
            | solve [eapply eval_fix'; fin] | solve [eapply eval_app_cong; fin] ].
  Qed.

  Lemma eval_app_value x fv a r :
    eval Σ x fv -> eval Σ (tApp fv a) r -> eval Σ (tApp x a) r.
  Proof.
    intros ex ev. have vf := eval_to_value _ _ ex.
    depelim ev; try flag_contra.
    all: match goal with vf : value _ ?F, H : eval Σ ?F ?y |- _ =>
           eapply eval_value in H; [|exact vf]; subst end.
    all: first [ solve [eapply eval_box; eassumption] | solve [eapply eval_beta; eassumption]
               | solve [eapply eval_fix'; eassumption] | solve [eapply eval_app_cong; eassumption] ].
  Qed.

  Lemma substl_tApp s x y : substl s (tApp x y) = tApp (substl s x) (substl s y).
  Proof. induction s in x, y |- *; cbn; auto. Qed.

  Lemma substl_closed s x : closed x -> substl s x = x.
  Proof. intros cl. induction s; cbn; auto. now rewrite csubst_closed. Qed.

  Lemma eval_app_let z v b a r :
    closed a ->
    eval Σ (tApp (tLetIn z v b) a) r -> eval Σ (tLetIn z v (tApp b (lift0 1 a))) r.
  Proof.
    intros cl ev. apply eval_app_inv in ev as (fv & ef & ev).
    depelim ef; try flag_contra.
    eapply eval_zeta; [eassumption|]. cbn.
    rewrite (lift_closed 1 0 a) // (csubst_closed _ 0 a) //.
    eapply eval_app_value; eassumption.
  Qed.

  Definition push_arg (a : term) (brs : list (list name × term)) :=
    map (fun br => (br.1, tApp br.2 (lift0 #|br.1| a))) brs.

  Lemma eval_case_app a r t fv :
    closed a -> eval Σ t fv -> forall ci d brs, t = tCase ci d brs ->
    eval Σ (tApp fv a) r -> eval Σ (tCase ci d (push_arg a brs)) r.
  Proof.
    intros cl ev. induction ev; intros ci0 d0 brs0 E ea; try discriminate; try flag_contra;
      try (subst; flag_contra).
    - injection E as <- <- <-.
      eapply eval_iota_block with (br := (br.1, tApp br.2 (lift0 #|br.1| a))); tea.
      + unfold push_arg. rewrite nth_error_map.
        match goal with H : nth_error _ _ = Some _ |- _ => now rewrite H end.
      + unfold iota_red. cbn. rewrite substl_tApp.
        rewrite (lift_closed _ 0 a) // (substl_closed _ a) //.
        eapply eval_app_value; eassumption.
    - injection E as <- <- <-.
      eapply eval_cofix_case; tea. eapply IHev2; auto.
  Qed.

  Lemma eval_app_case ci d brs a r :
    closed a ->
    eval Σ (tApp (tCase ci d brs) a) r -> eval Σ (tCase ci d (push_arg a brs)) r.
  Proof.
    intros cl ev. apply eval_app_inv in ev as (fv & ef & ev).
    exact (eval_case_app a r _ fv cl ef ci d brs eq_refl ev).
  Qed.

End Flags.
