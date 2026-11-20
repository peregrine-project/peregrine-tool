(** * Eta-expansion preserves evaluation

    The simulation relation [R Γ t t'] relates a λ□ term to an eta-expansion
    of it: [t'] is [t] where under-applied fixpoints, constructors and
    fixpoint-bound variables may have been replaced by [eta_wrap n h]
    ([Rs_fix_eta], [Rs_construct_eta], [Rs_rel_eta]).  As in
    [EEtaExpandedFix.expanded], [Γ] records for every variable the number of
    arguments it expects ([S rarg] for variables bound by a fixpoint).

    Evaluating an expanded head applied to some but not all of its arguments
    gives an abstraction, while the source value is a stuck application; the
    rules [R_fix_part] and [R_constr_part] relate the two.

    The main result is [eta_simulation]: if [t] evaluates to [v] and
    [R [] t t'], then [t'] evaluates to some [v'] with [R [] v v']
    (weak call-by-value evaluation with guarded fixpoints, constructors not
    as blocks). *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst ECSubst
  EGlobalEnv EWcbvEval EWellformed EProgram.
From Peregrine Require Import ELiftConstants EEtaExpand.
From Equations Require Import Equations.

Import ListNotations.

Local Existing Instance default_wcbv_flags.

(** [fun x1 .. xj => f vs x1 .. xj], for closed [f] and [vs] *)
Definition pwrap (j : nat) (f : term) (vs : list term) : term :=
  mk_lams j (mkApps f (vs ++ rels_down j)).

#[local] Arguments eta_wrap : simpl never.
#[local] Arguments pwrap : simpl never.

Definition fix_ctx (mfix : mfixpoint term) : list nat :=
  rev_map (fun d => S (rarg d)) mfix.

Section Rel.
  Variables Σ Σ' : global_declarations.

  Inductive Rs : list nat -> term -> term -> Prop :=
  | Rs_box Γ : Rs Γ tBox tBox
  | Rs_rel Γ i : Rs Γ (tRel i) (tRel i)
  | Rs_rel_eta Γ i m : nth_error Γ i = Some m -> Rs Γ (tRel i) (eta_wrap m (tRel i))
  | Rs_var Γ na : Rs Γ (tVar na) (tVar na)
  | Rs_const Γ kn : Rs Γ (tConst kn) (tConst kn)
  | Rs_evar Γ n ts ts' : Rl Γ ts ts' -> Rs Γ (tEvar n ts) (tEvar n ts')
  | Rs_lambda Γ na b b' : R (0 :: Γ) b b' -> Rs Γ (tLambda na b) (tLambda na b')
  | Rs_letin Γ na v v' b b' : R Γ v v' -> R (0 :: Γ) b b' -> Rs Γ (tLetIn na v b) (tLetIn na v' b')
  | Rs_app Γ f f' a a' : R Γ f f' -> R Γ a a' -> Rs Γ (tApp f a) (tApp f' a')
  | Rs_case Γ ci d d' brs brs' : R Γ d d' -> Rbrs Γ brs brs' -> Rs Γ (tCase ci d brs) (tCase ci d' brs')
  | Rs_proj Γ p u u' : R Γ u u' -> Rs Γ (tProj p u) (tProj p u')
  | Rs_fix Γ mfix mfix' idx :
      Rdefs (fix_ctx mfix ++ Γ) mfix mfix' -> Rs Γ (tFix mfix idx) (tFix mfix' idx)
  | Rs_fix_eta Γ mfix mfix' idx d :
      Rdefs (fix_ctx mfix ++ Γ) mfix mfix' -> nth_error mfix idx = Some d ->
      Rs Γ (tFix mfix idx) (eta_wrap (S (rarg d)) (tFix mfix' idx))
  | Rs_cofix Γ mfix mfix' idx :
      Rdefs (repeat 0 #|mfix| ++ Γ) mfix mfix' -> Rs Γ (tCoFix mfix idx) (tCoFix mfix' idx)
  | Rs_construct Γ ind c args args' : Rl Γ args args' -> Rs Γ (tConstruct ind c args) (tConstruct ind c args')
  | Rs_construct_eta Γ ind c p a :
      lookup_constructor_pars_args Σ ind c = Some (p, a) ->
      Rs Γ (tConstruct ind c []) (eta_wrap (p + a) (tConstruct ind c []))
  | Rs_prim_int Γ i : Rs Γ (tPrim (prim_int i)) (tPrim (prim_int i))
  | Rs_prim_float Γ f : Rs Γ (tPrim (prim_float f)) (tPrim (prim_float f))
  | Rs_prim_string Γ s : Rs Γ (tPrim (prim_string s)) (tPrim (prim_string s))
  | Rs_prim_array Γ d d' v v' :
      R Γ d d' -> Rl Γ v v' ->
      Rs Γ (tPrim (prim_array {| array_default := d; array_value := v |}))
           (tPrim (prim_array {| array_default := d'; array_value := v' |}))
  | Rs_lazy Γ u u' : R Γ u u' -> Rs Γ (tLazy u) (tLazy u')
  | Rs_force Γ u u' : R Γ u u' -> Rs Γ (tForce u) (tForce u')

  with R : list nat -> term -> term -> Prop :=
  | R_s Γ t t' : Rs Γ t t' -> R Γ t t'
  (* a stuck fixpoint application against the partially applied expansion *)
  | R_fix_part Γ mfix mfix' idx d vs vs' j :
      Rdefs (fix_ctx mfix ++ []) mfix mfix' -> nth_error mfix idx = Some d ->
      Rl [] vs vs' -> 0 < j -> #|vs| + j = S (rarg d) ->
      closedn 0 (mkApps (tFix mfix idx) vs) ->
      ∥ eval Σ (mkApps (tFix mfix idx) vs) (mkApps (tFix mfix idx) vs) ∥ ->
      Forall (fun v => ∥ eval Σ' v v ∥) vs' ->
      R Γ (mkApps (tFix mfix idx) vs) (pwrap j (tFix mfix' idx) vs')
  (* a partial constructor application against the partially applied expansion *)
  | R_constr_part Γ ind c p a vs vs' j :
      lookup_constructor_pars_args Σ ind c = Some (p, a) ->
      Rl [] vs vs' -> 0 < j -> #|vs| + j = p + a ->
      closedn 0 (mkApps (tConstruct ind c []) vs) ->
      ∥ eval Σ (mkApps (tConstruct ind c []) vs) (mkApps (tConstruct ind c []) vs) ∥ ->
      Forall (fun v => ∥ eval Σ' v v ∥) vs' ->
      R Γ (mkApps (tConstruct ind c []) vs) (pwrap j (tConstruct ind c []) vs')
  (* closed related terms are related in any context *)
  | R_weak Γ m t t' : closedn 0 t -> R [] t t' -> R (m :: Γ) t t'

  with Rl : list nat -> list term -> list term -> Prop :=
  | Rl_nil Γ : Rl Γ [] []
  | Rl_cons Γ t t' l l' : R Γ t t' -> Rl Γ l l' -> Rl Γ (t :: l) (t' :: l')

  with Rbrs : list nat -> list (list name × term) -> list (list name × term) -> Prop :=
  | Rbrs_nil Γ : Rbrs Γ [] []
  | Rbrs_cons Γ br br' brs brs' :
      br.1 = br'.1 -> R (repeat 0 #|br.1| ++ Γ) br.2 br'.2 -> Rbrs Γ brs brs' ->
      Rbrs Γ (br :: brs) (br' :: brs')

  with Rdefs : list nat -> mfixpoint term -> mfixpoint term -> Prop :=
  | Rdefs_nil Γ : Rdefs Γ [] []
  | Rdefs_cons Γ d d' m m' :
      dname d = dname d' -> rarg d = rarg d' -> R Γ (dbody d) (dbody d') -> Rdefs Γ m m' ->
      Rdefs Γ (d :: m) (d' :: m').

  Scheme Rs_mind := Minimality for Rs Sort Prop
  with R_mind := Minimality for R Sort Prop
  with Rl_mind := Minimality for Rl Sort Prop
  with Rbrs_mind := Minimality for Rbrs Sort Prop
  with Rdefs_mind := Minimality for Rdefs Sort Prop.
  Combined Scheme R_mutind from Rs_mind, R_mind, Rl_mind, Rbrs_mind, Rdefs_mind.

  Lemma Rl_Forall2 Γ l l' : Rl Γ l l' <-> Forall2 (R Γ) l l'.
  Proof. split; induction 1; constructor; auto. Qed.

  Lemma Rl_length Γ l l' : Rl Γ l l' -> #|l| = #|l'|.
  Proof. induction 1; cbn; congruence. Qed.

  Lemma Rl_app Γ l1 l1' l2 l2' : Rl Γ l1 l1' -> Rl Γ l2 l2' -> Rl Γ (l1 ++ l2) (l1' ++ l2').
  Proof. induction 1; cbn; auto. intros. constructor; auto. Qed.

  Definition br_rel Γ (br br' : list name × term) :=
    br.1 = br'.1 /\ R (repeat 0 #|br.1| ++ Γ) br.2 br'.2.
  Definition def_rel Γ (d d' : def term) :=
    dname d = dname d' /\ rarg d = rarg d' /\ R Γ (dbody d) (dbody d').

  Lemma Rbrs_Forall2 Γ l l' : Rbrs Γ l l' <-> Forall2 (br_rel Γ) l l'.
  Proof.
    split; induction 1; constructor; auto; try (split; auto; fail).
    all: destruct H; auto.
  Qed.

  Lemma Rdefs_Forall2 Γ l l' : Rdefs Γ l l' <-> Forall2 (def_rel Γ) l l'.
  Proof.
    split; induction 1; constructor; auto; try (repeat split; auto; fail).
    all: destruct H as (? & ? & ?); auto.
  Qed.

  Lemma Rdefs_length Γ m m' : Rdefs Γ m m' -> #|m| = #|m'|.
  Proof. induction 1; cbn; congruence. Qed.

  Lemma Rdefs_fix_ctx Γ m m' : Rdefs Γ m m' -> fix_ctx m' = fix_ctx m.
  Proof.
    intros H. rewrite /fix_ctx !rev_map_spec. f_equal.
    induction H; cbn; congruence.
  Qed.

  Lemma Rdefs_nth_error Γ m m' idx d :
    Rdefs Γ m m' -> nth_error m idx = Some d ->
    exists d', nth_error m' idx = Some d' /\ rarg d = rarg d' /\ R Γ (dbody d) (dbody d').
  Proof.
    intros H. induction H in idx |- *; destruct idx; cbn; try discriminate.
    - intros [= <-]. eauto.
    - auto.
  Qed.

  Lemma R_mkApps Γ f f' l l' : R Γ f f' -> Rl Γ l l' -> R Γ (mkApps f l) (mkApps f' l').
  Proof.
    intros Hf H. induction H in f, f', Hf |- *; cbn; auto.
    apply IHRl. now apply R_s, Rs_app.
  Qed.

  Lemma R_weaken Γ t t' : closedn 0 t -> R [] t t' -> R Γ t t'.
  Proof. destruct Γ; auto. intros. now apply R_weak. Qed.

  (** ** Closedness *)

  Lemma closedn_mk_lams n k t : closedn k (mk_lams n t) = closedn (n + k) t.
  Proof.
    induction n in k |- *; cbn; auto. now rewrite IHn Nat.add_succ_r.
  Qed.

  Lemma closedn_rels_down n k : n <= k -> forallb (closedn k) (rels_down n).
  Proof.
    induction n; cbn; auto. intros H. rewrite IHn; [lia|].
    rewrite andb_true_r. apply Nat.ltb_lt. lia.
  Qed.

  Lemma closedn_eta_wrap n k t : closedn k t -> closedn k (eta_wrap n t).
  Proof.
    intros H. rewrite /eta_wrap closedn_mk_lams closedn_mkApps closedn_rels_down; [lia|].
    rewrite andb_true_r Nat.add_comm. now apply closedn_lift.
  Qed.

  Lemma closedn_pwrap j k f vs :
    closedn 0 f -> forallb (closedn 0) vs -> closedn k (pwrap j f vs).
  Proof.
    intros Hf Hvs. rewrite /pwrap closedn_mk_lams closedn_mkApps forallb_app.
    rewrite closedn_rels_down; [lia|]. rewrite andb_true_r.
    apply/andP; split; [eapply closed_upwards; tea; lia|].
    solve_all. eapply closed_upwards; tea; lia.
  Qed.

  Lemma eta_wrap_pwrap n f : closedn 0 f -> eta_wrap n f = pwrap n f [].
  Proof. intros H. now rewrite /eta_wrap /pwrap lift_closed. Qed.

  Lemma R_closed_mut :
    (forall Γ t t', Rs Γ t t' -> forall k, closedn k t -> closedn k t') /\
    (forall Γ t t', R Γ t t' -> forall k, closedn k t -> closedn k t') /\
    (forall Γ l l', Rl Γ l l' -> forall k, forallb (closedn k) l -> forallb (closedn k) l') /\
    (forall Γ l l', Rbrs Γ l l' -> forall k,
        forallb (fun br => closedn (#|br.1| + k) br.2) l -> forallb (fun br => closedn (#|br.1| + k) br.2) l') /\
    (forall Γ l l', Rdefs Γ l l' -> forall k,
        forallb (test_def (closedn k)) l -> forallb (test_def (closedn k)) l').
  Proof.
    apply R_mutind; intros; cbn in *; rtoProp; auto.
    all: try (repeat split; eauto; fail).
    - now apply (closedn_eta_wrap m k (tRel i)).
    - erewrite <- Rdefs_length; tea. eauto.
    - apply (closedn_eta_wrap _ k (tFix mfix' idx)). cbn.
      erewrite <- Rdefs_length; tea. eauto.
    - erewrite <- Rdefs_length; tea. eauto.
    - now apply (closedn_eta_wrap _ k (tConstruct ind c [])).
    - move: H3; rewrite /test_array_model /= => /andP [? ?]. apply/andP; split; eauto.
    - match goal with H : is_true (closedn 0 (mkApps _ _)) |- _ => move: H end.
      rewrite closedn_mkApps => /andP [Hf Hvs]. cbn in Hf.
      apply closedn_pwrap; cbn; [rewrite Nat.add_0_r in Hf|]; eauto.
      erewrite <- Rdefs_length; tea. rewrite Nat.add_0_r. eauto.
    - match goal with H : is_true (closedn 0 (mkApps _ _)) |- _ => move: H end.
      rewrite closedn_mkApps => /andP [Hf Hvs].
      apply closedn_pwrap; cbn; eauto.
    - rewrite -H. split; eauto.
  Qed.

  Lemma R_closed Γ t t' k : R Γ t t' -> closedn k t -> closedn k t'.
  Proof. intros H. exact (proj1 (proj2 R_closed_mut) _ _ _ H k). Qed.

  Lemma Rl_closed Γ l l' k : Rl Γ l l' -> forallb (closedn k) l -> forallb (closedn k) l'.
  Proof. intros H. exact (proj1 (proj2 (proj2 R_closed_mut)) _ _ _ H k). Qed.

  Lemma Rdefs_closed Γ l l' k :
    Rdefs Γ l l' -> forallb (test_def (closedn k)) l -> forallb (test_def (closedn k)) l'.
  Proof. intros H. exact (proj2 (proj2 (proj2 (proj2 R_closed_mut))) _ _ _ H k). Qed.

  (** ** Substitution *)

  Lemma csubst_lift0 a n k x :
    closed a -> csubst a (n + k) (lift0 n x) = lift0 n (csubst a k x).
  Proof.
    intros Ha. rewrite !closed_subst //.
    rewrite (commut_lift_subst_rec x [a] n k 0); [lia|].
    now rewrite Nat.add_comm.
  Qed.

  Lemma csubst_mk_lams a k n t : csubst a k (mk_lams n t) = mk_lams n (csubst a (n + k) t).
  Proof.
    induction n in k |- *; cbn; auto. now rewrite IHn Nat.add_succ_r.
  Qed.

  Lemma csubst_rels_down a k n m : n <= m -> map (csubst a (m + k)) (rels_down n) = rels_down n.
  Proof.
    induction n; cbn; auto. intros H. rewrite IHn; [lia|]. f_equal.
    destruct (Nat.compare_spec (m + k) n); try lia. reflexivity.
  Qed.

  Lemma csubst_eta_wrap a k n t :
    closed a -> csubst a k (eta_wrap n t) = eta_wrap n (csubst a k t).
  Proof.
    intros Ha. rewrite /eta_wrap csubst_mk_lams csubst_mkApps csubst_rels_down //.
    now rewrite csubst_lift0.
  Qed.

  Definition compat (m : nat) (a a' : term) : Prop :=
    closedn 0 a /\ closedn 0 a' /\ R [] a a' /\ R [] a (eta_wrap m a').

  Lemma fix_ctx_length mfix : #|fix_ctx mfix| = #|mfix|.
  Proof. now rewrite /fix_ctx rev_map_spec List.length_rev length_map. Qed.

  Lemma fix_ctx_map f mfix : fix_ctx (map (map_def f) mfix) = fix_ctx mfix.
  Proof.
    rewrite /fix_ctx !rev_map_spec map_map. reflexivity.
  Qed.

  Lemma R_csubst_closed Γ Γ' t t' a a' k :
    R Γ t t' -> closedn 0 t -> (forall Δ, R Δ t t') ->
    R Γ' (csubst a k t) (csubst a' k t').
  Proof.
    intros H Hc Hall.
    rewrite !csubst_closed; auto.
    - eapply closed_upwards; tea; lia.
    - eapply closed_upwards; [eapply R_closed; tea|lia].
  Qed.

  Lemma R_csubst_mut :
    (forall Γ t t', Rs Γ t t' -> forall Γ1 m Γ2 a a', Γ = Γ1 ++ m :: Γ2 -> compat m a a' ->
        R (Γ1 ++ Γ2) (csubst a #|Γ1| t) (csubst a' #|Γ1| t')) /\
    (forall Γ t t', R Γ t t' -> forall Γ1 m Γ2 a a', Γ = Γ1 ++ m :: Γ2 -> compat m a a' ->
        R (Γ1 ++ Γ2) (csubst a #|Γ1| t) (csubst a' #|Γ1| t')) /\
    (forall Γ l l', Rl Γ l l' -> forall Γ1 m Γ2 a a', Γ = Γ1 ++ m :: Γ2 -> compat m a a' ->
        Rl (Γ1 ++ Γ2) (map (csubst a #|Γ1|) l) (map (csubst a' #|Γ1|) l')) /\
    (forall Γ l l', Rbrs Γ l l' -> forall Γ1 m Γ2 a a', Γ = Γ1 ++ m :: Γ2 -> compat m a a' ->
        Rbrs (Γ1 ++ Γ2) (map (fun br => (br.1, csubst a (#|br.1| + #|Γ1|) br.2)) l)
                        (map (fun br => (br.1, csubst a' (#|br.1| + #|Γ1|) br.2)) l')) /\
    (forall Γ l l', Rdefs Γ l l' -> forall Γ1 m Γ2 a a', Γ = Γ1 ++ m :: Γ2 -> compat m a a' ->
        Rdefs (Γ1 ++ Γ2) (map (map_def (csubst a #|Γ1|)) l) (map (map_def (csubst a' #|Γ1|)) l')).
  Proof.
    apply R_mutind; intros; subst; cbn -[eta_wrap pwrap].
    all: try (apply R_s; constructor; eauto; fail).
    - (* rel *)
      destruct (Nat.compare_spec #|Γ1| i).
      + destruct H0 as (? & ? & ? & ?). now apply R_weaken.
      + apply R_s; constructor.
      + apply R_s; constructor.
    - (* rel eta *)
      destruct H1 as (Ha & Ha' & Haa & Hw).
      rewrite csubst_eta_wrap //. cbn.
      destruct (Nat.compare_spec #|Γ1| i).
      + subst i. rewrite nth_error_app_ge // Nat.sub_diag /= in H. noconf H.
        now apply R_weaken.
      + apply R_s, Rs_rel_eta.
        rewrite nth_error_app_ge in H; [lia|].
        rewrite nth_error_app_ge; [lia|].
        destruct i; [lia|]. cbn. replace (S i - #|Γ1|) with (S (i - #|Γ1|)) in H by lia.
        exact H.
      + apply R_s, Rs_rel_eta.
        rewrite nth_error_app_lt in H; [lia|]. now rewrite nth_error_app_lt.
    - (* lambda *)
      apply R_s; constructor. now apply (H0 (0 :: Γ1) m Γ2).
    - (* let *)
      apply R_s; constructor; eauto. now apply (H2 (0 :: Γ1) m Γ2).
    - (* fix *)
      apply R_s, Rs_fix. rewrite fix_ctx_map.
      specialize (H0 (fix_ctx mfix ++ Γ1) m Γ2 a a').
      rewrite length_app fix_ctx_length -!app_assoc in H0.
      rewrite -(Rdefs_length _ _ _ H). now apply H0.
    - (* fix eta *)
      destruct H3 as (Ha & Ha' & Haa & Hw).
      rewrite csubst_eta_wrap //. cbn.
      apply R_s. eapply (Rs_fix_eta _ _ _ _ (map_def (csubst a (#|mfix| + #|Γ1|)) d)).
      + rewrite fix_ctx_map.
        specialize (H0 (fix_ctx mfix ++ Γ1) m Γ2 a a').
        rewrite length_app fix_ctx_length -!app_assoc in H0.
        rewrite -(Rdefs_length _ _ _ H). apply H0; auto. repeat split; auto.
      + now rewrite nth_error_map H1.
    - (* cofix *)
      apply R_s, Rs_cofix. rewrite length_map.
      specialize (H0 (repeat 0 #|mfix| ++ Γ1) m Γ2 a a').
      rewrite length_app repeat_length -!app_assoc in H0.
      rewrite -(Rdefs_length _ _ _ H). now apply H0.
    - (* construct eta *)
      destruct H1 as (Ha & Ha' & Haa & Hw).
      rewrite csubst_eta_wrap //. cbn. now apply R_s, Rs_construct_eta.
    - eapply H0; eauto.
    - (* fix part *)
      apply R_csubst_closed with (Γ := []); auto; intros; eapply R_fix_part; eauto.
    - (* constr part *)
      apply R_csubst_closed with (Γ := []); auto; intros; eapply R_constr_part; eauto.
    - (* weak *)
      destruct Γ1; noconf H2; cbn.
      + apply R_csubst_closed with (Γ := []); auto. intros. now apply R_weaken.
      + apply R_csubst_closed with (Γ := []); auto. intros. now apply R_weaken.
    - constructor.
    - constructor; eauto.
    - constructor.
    - constructor; cbn; eauto.
      specialize (H1 (repeat 0 #|br.1| ++ Γ1) m Γ2 a a').
      rewrite length_app repeat_length -!app_assoc in H1. rewrite -H. now apply H1.
    - constructor.
    - constructor; cbn; eauto.
  Qed.

  Lemma R_csubst Γ1 m Γ2 t t' a a' :
    R (Γ1 ++ m :: Γ2) t t' -> compat m a a' ->
    R (Γ1 ++ Γ2) (csubst a #|Γ1| t) (csubst a' #|Γ1| t').
  Proof. intros H Hc. exact (proj1 (proj2 R_csubst_mut) _ _ _ H _ _ _ _ _ eq_refl Hc). Qed.

  Inductive compats : list nat -> list term -> list term -> Prop :=
  | compats_nil : compats [] [] []
  | compats_cons m ms a a' s s' : compat m a a' -> compats ms s s' -> compats (m :: ms) (a :: s) (a' :: s').

  Lemma R_substl ms s s' Γ t t' :
    compats ms s s' -> R (ms ++ Γ) t t' -> R Γ (substl s t) (substl s' t').
  Proof.
    unfold substl. induction 1 in t, t' |- *; cbn; auto.
    intros Ht. apply IHcompats. now apply (R_csubst [] m (ms ++ Γ)).
  Qed.

  Lemma compat_0 a a' : closedn 0 a -> R [] a a' -> compat 0 a a'.
  Proof.
    intros Ha Hr. repeat split; auto.
    - eapply R_closed; tea.
    - now rewrite eta_wrap_0.
  Qed.

  Lemma compats_repeat l l' :
    forallb (closedn 0) l -> Rl [] l l' -> compats (repeat 0 #|l|) l l'.
  Proof.
    intros Hc H. apply Rl_Forall2 in H.
    induction H; cbn in *; rtoProp; constructor; auto.
    now apply compat_0.
  Qed.
End Rel.

Fixpoint fix_subst_aux (mfix : mfixpoint term) (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => tFix mfix n :: fix_subst_aux mfix n
  end.

Lemma fix_subst_aux_eq mfix : fix_subst mfix = fix_subst_aux mfix #|mfix|.
Proof.
  unfold fix_subst. generalize #|mfix|. induction n; cbn; f_equal; auto.
Qed.

Fixpoint cofix_subst_aux (mfix : mfixpoint term) (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => tCoFix mfix n :: cofix_subst_aux mfix n
  end.

Lemma cofix_subst_aux_eq mfix : cofix_subst mfix = cofix_subst_aux mfix #|mfix|.
Proof.
  unfold cofix_subst. generalize #|mfix|. induction n; cbn; f_equal; auto.
Qed.

Lemma csubst_pwrap a j f vs :
  closedn 0 f -> forallb (closedn 0) vs ->
  csubst a 0 (mk_lams j (mkApps f (vs ++ rels_down (S j)))) = pwrap j f (vs ++ [a]).
Proof.
  intros Hf Hvs. rewrite /pwrap csubst_mk_lams csubst_mkApps map_app. cbn.
  rewrite (csubst_rels_down a 0 j j) // Nat.add_0_r Nat.compare_refl -app_assoc /=.
  rewrite csubst_closed; [eapply closed_upwards; tea; lia|].
  f_equal. f_equal. f_equal.
  solve_all. apply csubst_closed. eapply closed_upwards; tea; lia.
Qed.

Section Sim.
  Variables Σ Σ' : global_declarations.
  Hypothesis clΣ : closed_env Σ.
  Hypothesis Hind : forall kn, lookup_minductive Σ kn = lookup_minductive Σ' kn.
  Hypothesis Hcst : forall c decl b,
    declared_constant Σ c decl -> cst_body decl = Some b ->
    exists decl' b', declared_constant Σ' c decl' /\ cst_body decl' = Some b' /\ R Σ Σ' [] b b'.

  Notation R := (R Σ Σ').
  Notation Rs := (Rs Σ Σ').
  Notation Rl := (Rl Σ Σ').
  Notation Rdefs := (Rdefs Σ Σ').
  Notation Rbrs := (Rbrs Σ Σ').
  Notation compat := (compat Σ Σ').
  Notation compats := (compats Σ Σ').

  Definition selfeval' (v : term) := ∥ eval Σ' v v ∥.

  (** *** Substitutions for fixpoint unfolding *)

  Lemma compats_fix_subst mfix mfix' :
    Rdefs (fix_ctx mfix ++ []) mfix mfix' ->
    forallb (test_def (closedn (#|mfix| + 0))) mfix ->
    compats (fix_ctx mfix) (fix_subst mfix) (fix_subst mfix').
  Proof.
    intros Hd Hc.
    rewrite !fix_subst_aux_eq -(Rdefs_length _ _ _ _ _ Hd) /fix_ctx rev_map_spec.
    assert (H : forall l1 l2, map (fun d => S (rarg d)) mfix = l1 ++ l2 ->
              compats (List.rev l1) (fix_subst_aux mfix #|l1|) (fix_subst_aux mfix' #|l1|)).
    { induction l1 using rev_ind; intros l2 E.
      - constructor.
      - rewrite rev_unit length_app /= Nat.add_1_r /=.
        rewrite -app_assoc /= in E.
        constructor; [|now apply (IHl1 (x :: l2))].
        assert (Hn : nth_error (map (fun d => S (rarg d)) mfix) #|l1| = Some x).
        { rewrite E nth_error_app_ge // Nat.sub_diag //. }
        rewrite nth_error_map in Hn. destruct (nth_error mfix #|l1|) as [d|] eqn:Hnth; noconf Hn.
        assert (Hcl : closedn 0 (tFix mfix #|l1|)) by exact Hc.
        repeat split; auto.
        + eapply R_closed; [apply R_s, Rs_fix; exact Hd|exact Hcl].
        + apply R_s, Rs_fix; exact Hd.
        + apply R_s. eapply Rs_fix_eta; tea. }
    specialize (H (map (fun d => S (rarg d)) mfix) []). rewrite app_nil_r length_map in H.
    now apply H.
  Qed.

  Lemma compats_cofix_subst mfix mfix' :
    Rdefs (repeat 0 #|mfix| ++ []) mfix mfix' ->
    forallb (test_def (closedn (#|mfix| + 0))) mfix ->
    compats (repeat 0 #|mfix|) (cofix_subst mfix) (cofix_subst mfix').
  Proof.
    intros Hd Hc.
    rewrite !cofix_subst_aux_eq -(Rdefs_length _ _ _ _ _ Hd).
    generalize #|mfix| at 1 2 3. induction n; cbn; constructor; auto.
    apply compat_0; [exact Hc|]. apply R_s, Rs_cofix; exact Hd.
  Qed.

  Lemma cunfold_fix_rel mfix mfix' idx n fn :
    Rdefs (fix_ctx mfix ++ []) mfix mfix' -> closedn 0 (tFix mfix idx) ->
    cunfold_fix mfix idx = Some (n, fn) ->
    exists fn', cunfold_fix mfix' idx = Some (n, fn') /\ R [] fn fn'.
  Proof.
    intros Hd Hc. unfold cunfold_fix.
    destruct (nth_error mfix idx) as [d|] eqn:E; [|discriminate]. intros [= <- <-].
    destruct (Rdefs_nth_error _ _ _ _ _ _ _ Hd E) as (d' & -> & <- & Hb).
    eexists; split; [reflexivity|].
    eapply R_substl; [|exact Hb]. now apply compats_fix_subst.
  Qed.

  Lemma cunfold_cofix_rel mfix mfix' idx n fn :
    Rdefs (repeat 0 #|mfix| ++ []) mfix mfix' -> closedn 0 (tCoFix mfix idx) ->
    cunfold_cofix mfix idx = Some (n, fn) ->
    exists fn', cunfold_cofix mfix' idx = Some (n, fn') /\ R [] fn fn'.
  Proof.
    intros Hd Hc. unfold cunfold_cofix.
    destruct (nth_error mfix idx) as [d|] eqn:E; [|discriminate]. intros [= <- <-].
    destruct (Rdefs_nth_error _ _ _ _ _ _ _ Hd E) as (d' & -> & <- & Hb).
    eexists; split; [reflexivity|].
    eapply R_substl; [|exact Hb]. now apply compats_cofix_subst.
  Qed.

  (** *** Inversion of the relation on values *)

  Lemma R_inv_s t w : R [] t w -> ~~ isFixApp t -> ~~ isConstructApp t -> Rs [] t w.
  Proof.
    inversion 1; subst; auto.
    - now rewrite isFixApp_mkApps.
    - now rewrite isConstructApp_mkApps.
  Qed.

  Lemma head_rel t : forall w, R [] t w -> ~~ isFixApp t -> ~~ isConstructApp t ->
    [/\ isLambda w = isLambda t, isFixApp w = false, isBox w = isBox t,
        isConstructApp w = false, isPrimApp w = isPrimApp t & isLazyApp w = isLazyApp t].
  Proof.
    induction t; intros w H Hf Hc; apply R_inv_s in H; auto; inversion H; subst.
    all: try (split; reflexivity).
    all: try discriminate.
    - destruct n; discriminate.
    - unfold isFixApp, isConstructApp, isPrimApp, isLazyApp in *.
      rewrite !head_tApp in Hf, Hc |- *.
      match goal with HR : R [] t1 _ |- _ => destruct (IHt1 _ HR Hf Hc) end.
      split; auto.
  Qed.

  Lemma value_tApp_inv f a : value Σ' (tApp f a) -> value Σ' f × ~~ isLambda f.
  Proof.
    intros H. rewrite -(mkApps_head_spine f) in H |- *.
    change (tApp ?g a) with (mkApps g [a]) in H. rewrite -mkApps_app in H.
    apply value_mkApps_inv in H as [[[E _]|[E _]]|[Hne Hh Hall]]; [| | |apply head_nApp].
    1-2: destruct (spine f); discriminate.
    apply All_app in Hall as [Hall _].
    assert (Hh' : value_head Σ' #|spine f| (head f)).
    { rewrite length_app /= in Hh. destruct Hh; econstructor; eauto; cbn in *; lia. }
    split; [now apply value_app|].
    destruct (spine f) using rev_case; [destruct Hh'; reflexivity|].
    rewrite mkApps_app. reflexivity.
  Qed.

  Definition fix_partial mfix idx vs w :=
    exists mfix' d vs' j,
      [/\ w = pwrap j (tFix mfix' idx) vs', Rdefs (fix_ctx mfix ++ []) mfix mfix',
          nth_error mfix idx = Some d, Rl [] vs vs' & 0 < j /\ #|vs| + j = S (rarg d) /\ Forall selfeval' vs'].

  Lemma R_fix_cases mfix idx vs w :
    R [] (mkApps (tFix mfix idx) vs) w ->
    Rs [] (mkApps (tFix mfix idx) vs) w \/ fix_partial mfix idx vs w.
  Proof.
    inversion 1; subst; auto.
    - match goal with E : mkApps _ _ = mkApps _ _ |- _ =>
        apply mkApps_eq_inj in E as [[= -> ->] ->]; auto end.
      right. repeat eexists; eauto.
    - match goal with E : mkApps _ _ = mkApps _ _ |- _ =>
        apply mkApps_eq_inj in E as [[=] _]; auto end.
  Qed.

  Lemma fix_spine_inv mfix idx vs : forall w,
    closedn 0 (tFix mfix idx) ->
    R [] (mkApps (tFix mfix idx) vs) w -> value Σ' w ->
    (exists mfix' vs', [/\ w = mkApps (tFix mfix' idx) vs', Rdefs (fix_ctx mfix ++ []) mfix mfix' & Rl [] vs vs']) \/
    fix_partial mfix idx vs w.
  Proof.
    induction vs using rev_ind; intros w Hc H Hv.
    - destruct (R_fix_cases _ _ _ _ H) as [Hs|]; auto. cbn in Hs. inversion Hs; subst.
      + left. exists mfix', []. split; auto. constructor.
      + right. exists mfix', d, [], (S (rarg d)).
        split; auto; [|constructor|repeat split; auto; lia].
        apply eta_wrap_pwrap. eapply R_closed; [apply R_s, Rs_fix; eassumption|exact Hc].
    - destruct (R_fix_cases _ _ _ _ H) as [Hs|]; auto.
      rewrite mkApps_app /= in Hs. inversion Hs; subst.
      apply value_tApp_inv in Hv as [Hv Hl].
      match goal with HR : R [] (mkApps _ vs) _ |- _ =>
        destruct (IHvs _ Hc HR Hv) as [(mfix' & vs' & [-> Hd Hvs])|(mfix' & d & vs' & j & [-> _ _ _ [Hj _]])] end.
      + left. exists mfix', (vs' ++ [a']). rewrite mkApps_app. split; auto.
        apply Rl_app; auto. constructor; auto. constructor.
      + destruct j; [lia|]. discriminate Hl.
  Qed.

  Definition constr_partial ind c vs w :=
    exists p a vs' j,
      [/\ w = pwrap j (tConstruct ind c []) vs', lookup_constructor_pars_args Σ ind c = Some (p, a),
          Rl [] vs vs', 0 < j & #|vs| + j = p + a /\ Forall selfeval' vs'].

  Lemma R_constr_cases ind c vs w :
    R [] (mkApps (tConstruct ind c []) vs) w ->
    Rs [] (mkApps (tConstruct ind c []) vs) w \/ constr_partial ind c vs w.
  Proof.
    inversion 1; subst; auto.
    - match goal with E : mkApps _ _ = mkApps _ _ |- _ =>
        apply mkApps_eq_inj in E as [[=] _]; auto end.
    - match goal with E : mkApps _ _ = mkApps _ _ |- _ =>
        apply mkApps_eq_inj in E as [[= -> ->] ->]; auto end.
      right. exists p, a, vs', j. split; auto.
  Qed.

  Lemma constr_spine_inv ind c vs : forall w,
    R [] (mkApps (tConstruct ind c []) vs) w -> value Σ' w ->
    (exists vs', w = mkApps (tConstruct ind c []) vs' /\ Rl [] vs vs') \/
    constr_partial ind c vs w.
  Proof.
    induction vs using rev_ind; intros w H Hv.
    - destruct (R_constr_cases _ _ _ _ H) as [Hs|]; auto. cbn in Hs. inversion Hs; subst.
      + left. exists []. split; [|constructor].
        match goal with HR : Rl [] [] _ |- _ => inversion HR; subst end. reflexivity.
      + destruct (p + a) as [|n] eqn:E.
        * left. exists []. rewrite eta_wrap_0. split; [reflexivity|constructor].
        * right. exists p, a, [], (S n).
          split; [now apply eta_wrap_pwrap|assumption|constructor|lia|split; [cbn; lia|constructor]].
    - destruct (R_constr_cases _ _ _ _ H) as [Hs|]; auto.
      rewrite mkApps_app /= in Hs. inversion Hs; subst.
      apply value_tApp_inv in Hv as [Hv Hl].
      match goal with HR : R [] (mkApps _ vs) _ |- _ =>
        destruct (IHvs _ HR Hv) as [(vs' & -> & Hvs)|(p & a & vs' & j & [-> _ _ Hj _])] end.
      + left. exists (vs' ++ [a']). rewrite mkApps_app. split; auto.
        apply Rl_app; auto. constructor; auto. constructor.
      + destruct j; [lia|]. discriminate Hl.
  Qed.

  Lemma cofix_spine_inv mfix idx vs : forall w,
    R [] (mkApps (tCoFix mfix idx) vs) w ->
    exists mfix' vs', [/\ w = mkApps (tCoFix mfix' idx) vs', Rdefs (repeat 0 #|mfix| ++ []) mfix mfix' & Rl [] vs vs'].
  Proof.
    induction vs using rev_ind; intros w H.
    - apply R_inv_s in H; [|reflexivity..]. cbn in H. inversion H; subst.
      exists mfix', []. split; auto. constructor.
    - apply R_inv_s in H; [|rewrite ?isFixApp_mkApps ?isConstructApp_mkApps //..].
      rewrite mkApps_app /= in H. inversion H; subst.
      match goal with HR : R [] (mkApps _ vs) _ |- _ =>
        destruct (IHvs _ HR) as (mfix' & vs' & [-> Hd Hvs]) end.
      exists mfix', (vs' ++ [a']). rewrite mkApps_app. split; auto.
      apply Rl_app; auto. constructor; auto. constructor.
  Qed.

  (** ** The simulation *)

  Definition simQ (v u : term) := exists v', ∥ eval Σ' u v' ∥ /\ R [] v v'.
  Definition sim_s (t v : term) := closedn 0 t -> forall u, Rs [] t u -> simQ v u.
  Definition sim_g (t v : term) := closedn 0 t -> forall u, R [] t u -> simQ v u.

  Lemma sim_lift t v : eval Σ t v -> sim_s t v -> sim_g t v.
  Proof.
    intros ev Hs Hc u H. inversion H; subst.
    - now apply Hs.
    - match goal with He : ∥ eval Σ _ _ ∥ |- _ => destruct He as [ev1] end.
      have e := eval_deterministic ev ev1. subst v.
      eexists; split; [|exact H]. destruct j; [lia|]. sq. now apply eval_atom.
    - match goal with He : ∥ eval Σ _ _ ∥ |- _ => destruct He as [ev1] end.
      have e := eval_deterministic ev ev1. subst v.
      eexists; split; [|exact H]. destruct j; [lia|]. sq. now apply eval_atom.
  Qed.

  Lemma sim_args args args' (a : All2_Set (eval Σ) args args') :
    All2_over a (fun x y _ => sim_s x y) -> forallb (closedn 0) args ->
    forall args0, Rl [] args args0 ->
    exists args1, ∥ All2_Set (eval Σ') args0 args1 ∥ /\ Rl [] args' args1.
  Proof.
    induction a; cbn; intros iha Hc args0 H.
    - inversion H; subst. exists []. split; [sq; constructor | constructor].
    - destruct iha as [hx hl]. move/andP: Hc => [Hc1 Hc2]. inversion H; subst.
      match goal with ev : eval Σ ?x ?y, HG : R [] ?x _ |- _ =>
        destruct (sim_lift _ _ ev hx Hc1 _ HG) as (y' & [evy] & Hy) end.
      match goal with HG : Rl [] _ _ |- _ =>
        destruct (IHa hl Hc2 _ HG) as (lr & [evl] & Hl) end.
      exists (y' :: lr). split; [sq; now constructor | now constructor].
  Qed.

  Lemma evcl t v : closedn 0 t -> eval Σ t v -> closedn 0 v.
  Proof. now apply eval_closed. Qed.

  Lemma selfeval_All2 l : Forall selfeval' l -> ∥ All2 (eval Σ') l l ∥.
  Proof.
    induction 1; [sq; constructor|]. destruct H as [e], IHForall as [a]. sq. now constructor.
  Qed.

  Lemma eval_stuck_fix_self mfix idx vs n fn :
    cunfold_fix mfix idx = Some (n, fn) -> #|vs| <= n -> Forall selfeval' vs ->
    ∥ eval Σ' (mkApps (tFix mfix idx) vs) (mkApps (tFix mfix idx) vs) ∥.
  Proof.
    intros Hu Hn Hs. destruct (selfeval_All2 _ Hs) as [Ha]. sq.
    apply eval_stuck_Fix; auto; try (now apply eval_atom).
    cbn. rewrite Hu. now apply Nat.leb_le.
  Qed.

  Lemma eval_constr_self ind c vs mdecl idecl cdecl :
    lookup_constructor Σ' ind c = Some (mdecl, idecl, cdecl) ->
    #|vs| <= cstr_arity mdecl cdecl -> Forall selfeval' vs ->
    ∥ eval Σ' (mkApps (tConstruct ind c []) vs) (mkApps (tConstruct ind c []) vs) ∥.
  Proof.
    intros Hl Hn Hs. destruct (selfeval_All2 _ Hs) as [Ha]. sq.
    eapply eval_mkApps_Construct; tea; auto.
    apply eval_atom. cbn -[lookup_constructor]. now rewrite Hl.
  Qed.

  Lemma pars_args_isprop ind c b pars cdecl p a :
    constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) ->
    lookup_constructor_pars_args Σ ind c = Some (p, a) ->
    p = pars /\ a = cstr_nargs cdecl.
  Proof.
    unfold constructor_isprop_pars_decl, lookup_constructor_pars_args.
    destruct (lookup_constructor Σ ind c) as [[[? ?] ?]|]; cbn; [|discriminate].
    intros [= <- <- <-] [= <- <-]. auto.
  Qed.

  Lemma pars_args_lookup ind c mdecl idecl cdecl p a :
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    lookup_constructor_pars_args Σ ind c = Some (p, a) ->
    p + a = cstr_arity mdecl cdecl.
  Proof.
    unfold lookup_constructor_pars_args. intros ->. cbn. intros [= <- <-]. reflexivity.
  Qed.

  Ltac lft := repeat match goal with
    | ev : eval Σ ?t ?v, IH : sim_s ?t ?v, Hc : is_true (closedn 0 ?t), HG : EEtaExpandSim.R Σ Σ' [] ?t ?u |- _ =>
      let w := fresh "w" in let evw := fresh "evw" in let Hw := fresh "Hw" in
      destruct (sim_lift _ _ ev IH Hc _ HG) as (w & [evw] & Hw); clear IH end.

  Ltac cls := repeat match goal with
    | ev : eval Σ ?t ?v, Hc : is_true (closedn 0 ?t) |- _ =>
      lazymatch goal with
      | H : is_true (closedn 0 v) |- _ => fail
      | _ => let Hcv := fresh "Hcv" in have Hcv := evcl _ _ Hc ev
      end end.

  Ltac inv_s H := apply R_inv_s in H; [|reflexivity..]; inversion H; subst.

  Lemma eta_simulation_s t v (ev : eval Σ t v) : sim_s t v.
  Proof.
    induction ev using eval_rect; intros Hc u Hs.
    all: try (match goal with
              | H : context [with_guarded_fix] |- _ => cbv in H; discriminate H
              | H : context [with_constructor_as_block] |- _ => cbv in H; discriminate H end).
    all: cbn in Hc; rtoProp; inversion Hs; subst; lft.
    all: try (match goal with i : is_true (atom _ _) |- _ => cbn in i; discriminate i end).
    (* box *)
    - match goal with Hb : R [] tBox ?w |- _ => inv_s Hb end.
      exists tBox. split; [|apply R_s; constructor]. sq. eapply eval_box; tea.
    (* beta *)
    - match goal with Hl : R [] (tLambda _ _) ?w |- _ => inv_s Hl end.
      cls.
      match goal with Hb : R [0] b ?b', Ha : R [] a' ?w |- _ =>
        have HG3 : R [] (csubst a' 0 b) (csubst w 0 b')
          by (apply (R_csubst _ _ [] 0 []); [exact Hb|apply compat_0; auto]) end.
      have Hc3 : closedn 0 (csubst a' 0 b) by now apply closed_csubst.
      lft. eexists; split; [|eassumption]. sq. eapply eval_beta; tea.
    (* zeta *)
    - cls.
      match goal with Hb : R [0] b1 ?b', Ha : R [] b0' ?w |- _ =>
        have HG3 : R [] (csubst b0' 0 b1) (csubst w 0 b')
          by (apply (R_csubst _ _ [] 0 []); [exact Hb|apply compat_0; auto]) end.
      have Hc3 : closedn 0 (csubst b0' 0 b1) by now apply closed_csubst.
      lft. eexists; split; [|eassumption]. sq. eapply eval_zeta; tea.
    (* iota *)
    - cls.
      match goal with Hd : R [] (mkApps (tConstruct _ _ _) args) ?w, evw : eval Σ' _ ?w |- _ =>
        destruct (constr_spine_inv _ _ _ _ Hd (eval_to_value _ _ evw))
          as [(args' & -> & Hargs)|(p & a & vs' & j & [-> Hl _ Hj [Hlen _]])] end.
      2:{ exfalso.
          match goal with Hi : constructor_isprop_pars_decl Σ _ _ = Some _ |- _ =>
            destruct (pars_args_isprop _ _ _ _ _ _ _ Hi Hl) as [-> ->] end. lia. }
      match goal with Hb : Rbrs [] brs ?brs', Hn : nth_error brs c = Some br |- _ =>
        apply Rbrs_Forall2 in Hb;
        destruct (Forall2_nth_error_l _ _ _ _ _ Hb Hn) as (br' & Hn' & Hb1 & Hb2) end.
      apply Rl_Forall2 in Hargs. have Hlen := Forall2_length Hargs.
      match goal with Hc : is_true (closedn 0 (mkApps (tConstruct _ _ _) args)) |- _ =>
        rewrite closedn_mkApps /= in Hc end.
      have HG3 : R [] (iota_red pars args br) (iota_red pars args' br').
      { unfold iota_red.
        have Hcp := compats_repeat Σ Σ' (List.rev (skipn pars args)) (List.rev (skipn pars args')).
        rewrite List.length_rev in Hcp.
        match goal with E : #|skipn pars args| = #|br.1| |- _ => rewrite E in Hcp end.
        eapply R_substl; [apply Hcp|exact Hb2].
        - now rewrite forallb_rev forallb_skipn.
        - apply Rl_Forall2, Forall2_List_rev, Forall2_skipn. exact Hargs. }
      have Hc3 : closedn 0 (iota_red pars args br).
      { unfold iota_red. apply closed_substl; [now rewrite forallb_rev forallb_skipn|].
        rewrite List.length_rev.
        match goal with E : #|skipn pars args| = #|br.1| |- _ => rewrite E end.
        match goal with Hbr : is_true (forallb _ brs), Hn : nth_error brs c = Some br |- _ =>
          eapply (forallb_nth_error _ _ c) in Hbr; rewrite Hn in Hbr; exact Hbr end. }
      lft. eexists; split; [|eassumption]. sq.
      eapply eval_iota; tea.
      + rewrite -(same_constructor_isprop_pars_decl _ _ Hind). eassumption.
      + now rewrite -Hlen.
      + match goal with E : #|skipn pars args| = #|br.1| |- _ =>
          rewrite -Hb1 -E !length_skipn Hlen // end.
    (* iota sing *)
    - match goal with Hb : R [] tBox ?w |- _ => inv_s Hb end.
      match goal with ev : eval Σ (substl _ ?f0) _ |- _ => rename f0 into f end.
      match goal with Hb : Rbrs [] [_] _ |- _ =>
        inversion Hb as [|? ? br' ? ? Hb1 Hb2 Hb3]; subst; inversion Hb3; subst end.
      destruct br' as [n' f']; cbn in Hb1, Hb2; subst n'.
      have Hbx : forallb (closedn 0) (repeat tBox #|n|) by (clear; induction #|n|; cbn; auto).
      have HG3 : R [] (substl (repeat tBox #|n|) f) (substl (repeat tBox #|n|) f').
      { have Hcp := compats_repeat Σ Σ' (repeat tBox #|n|) (repeat tBox #|n|).
        rewrite repeat_length in Hcp. eapply R_substl; [apply Hcp|exact Hb2]; auto.
        clear; induction #|n|; cbn; constructor; auto. apply R_s; constructor. }
      have Hc3 : closedn 0 (substl (repeat tBox #|n|) f).
      { apply closed_substl; auto. rewrite repeat_length.
        match goal with Hbr : is_true (forallb _ [_]) |- _ =>
          cbn in Hbr; rewrite andb_true_r in Hbr; exact Hbr end. }
      lft. eexists; split; [|eassumption]. sq. eapply eval_iota_sing; tea; [|reflexivity].
      rewrite -(same_inductive_isprop_and_pars _ _ Hind). eassumption.
    (* fix *)
    - cls.
      match goal with Hc : is_true (closedn 0 (mkApps (tFix _ _) argsv)) |- _ =>
        rewrite closedn_mkApps in Hc; move/andP: Hc => [Hcf Hcargs] end.
      match goal with Hu : cunfold_fix mfix idx = Some _ |- _ =>
        have Hcfn := closed_cunfold_fix _ _ _ _ Hcf Hu; have Hu0 := Hu end.
      have Hc3 : closedn 0 (tApp (mkApps fn argsv) av)
        by (cbn; rewrite closedn_mkApps Hcfn Hcargs /=; assumption).
      match goal with Hd : R [] (mkApps (tFix _ _) argsv) ?w, evw : eval Σ' _ ?w |- _ =>
        destruct (fix_spine_inv _ _ _ _ Hcf Hd (eval_to_value _ _ evw))
          as [(mfix' & argsv' & [-> Hdefs Hargs])|(mfix' & d & vs' & j & [-> Hdefs Hnth Hargs [Hj [Hlen Hself]]])];
        rename evw into evf end.
      + destruct (cunfold_fix_rel _ _ _ _ _ Hdefs Hcf Hu0) as (fn' & Hu' & Hfn).
        have Hlen := Rl_length _ _ _ _ _ Hargs.
        match goal with Ha : R [] av ?w |- _ =>
          have HG3 : R [] (tApp (mkApps fn argsv) av) (tApp (mkApps fn' argsv') w)
            by (apply R_s, Rs_app; auto; apply R_mkApps; auto) end.
        lft. eexists; split; [|eassumption]. sq. eapply eval_fix; tea. now rewrite -Hlen.
      + destruct (cunfold_fix_rel _ _ _ _ _ Hdefs Hcf Hu0) as (fn' & Hu' & Hfn).
        have Hlen' := Rl_length _ _ _ _ _ Hargs.
        unfold cunfold_fix in Hu0. rewrite Hnth in Hu0. injection Hu0 as Hr _.
        assert (j = 1) by lia. subst j.
        have Hcf' : closedn 0 (tFix mfix' idx)
          by (eapply R_closed; [apply R_s, Rs_fix; exact Hdefs|exact Hcf]).
        have Hcvs' : forallb (closedn 0) vs' by (eapply Rl_closed; tea).
        match goal with Ha : R [] av ?w, eva : eval Σ' _ ?w |- _ =>
          have HG3 : R [] (tApp (mkApps fn argsv) av) (tApp (mkApps fn' vs') w)
            by (apply R_s, Rs_app; auto; apply R_mkApps; auto) end.
        match goal with Ha : R [] av ?w, eva : eval Σ' _ ?w |- _ => rename eva into eva0 end.
        lft. eexists; split; [|eassumption].
        have Hle : #|vs'| <= #|argsv| by lia.
        destruct (eval_stuck_fix_self _ _ _ _ _ Hu' Hle Hself) as [evst].
        change (pwrap 1 (tFix mfix' idx) vs')
          with (tLambda nAnon (mk_lams 0 (mkApps (tFix mfix' idx) (vs' ++ rels_down 1)))) in evf.
        sq. eapply eval_beta; [exact evf|exact eva0|].
        rewrite csubst_pwrap //. unfold pwrap. cbn [mk_lams rels_down].
        rewrite app_nil_r mkApps_app. cbn [mkApps].
        eapply eval_fix; tea.
        * apply value_final. eapply eval_to_value; exact eva0.
        * now rewrite -Hlen'.
    (* fix value *)
    - cls.
      match goal with Hc : is_true (closedn 0 (mkApps (tFix _ _) argsv)) |- _ =>
        rewrite closedn_mkApps in Hc; move/andP: Hc => [Hcf Hcargs] end.
      match goal with Hu : cunfold_fix mfix idx = Some _ |- _ => have Hu0 := Hu end.
      match goal with Hd : R [] (mkApps (tFix _ _) argsv) ?w, evw : eval Σ' _ ?w |- _ =>
        destruct (fix_spine_inv _ _ _ _ Hcf Hd (eval_to_value _ _ evw))
          as [(mfix' & argsv' & [-> Hdefs Hargs])|(mfix' & d & vs' & j & [-> Hdefs Hnth Hargs [Hj [Hlen Hself]]])];
        rename evw into evf end.
      + destruct (cunfold_fix_rel _ _ _ _ _ Hdefs Hcf Hu0) as (fn' & Hu' & Hfn).
        have Hlen := Rl_length _ _ _ _ _ Hargs.
        eexists (tApp (mkApps (tFix mfix' idx) argsv') _). split.
        * sq. eapply eval_fix_value; tea. now rewrite -Hlen.
        * apply R_s, Rs_app; auto.
      + have Hlen' := Rl_length _ _ _ _ _ Hargs.
        have Hu1 := Hu0. unfold cunfold_fix in Hu1. rewrite Hnth in Hu1. injection Hu1 as Hr _.
        destruct j as [|[|j]]; try lia.
        have Hcf' : closedn 0 (tFix mfix' idx)
          by (eapply R_closed; [apply R_s, Rs_fix; exact Hdefs|exact Hcf]).
        have Hcvs' : forallb (closedn 0) vs' by (eapply Rl_closed; tea).
        match goal with Ha : R [] av ?w, eva : eval Σ' _ ?w |- _ =>
          rename eva into eva0; rename Ha into Hav; rename w into aw end.
        have Hsw : selfeval' aw by (sq; apply value_final; eapply eval_to_value; exact eva0).
        change (pwrap (S (S j)) (tFix mfix' idx) vs')
          with (tLambda nAnon (mk_lams (S j) (mkApps (tFix mfix' idx) (vs' ++ rels_down (S (S j)))))) in evf.
        exists (pwrap (S j) (tFix mfix' idx) (vs' ++ [aw])). split.
        * sq. eapply eval_beta; [exact evf|exact eva0|].
          rewrite csubst_pwrap //. now apply eval_atom.
        * change (tApp ?f ?x) with (mkApps f [x]). rewrite -mkApps_app.
          apply (R_fix_part Σ Σ' [] mfix mfix' idx d (argsv ++ [av]) (vs' ++ [aw]) (S j)); auto.
          -- apply Rl_app; auto. constructor; auto. constructor.
          -- lia.
          -- rewrite length_app /=. lia.
          -- rewrite closedn_mkApps Hcf forallb_app Hcargs /= andb_true_r. assumption.
          -- sq. rewrite mkApps_app. apply value_final. eapply eval_to_value.
             eapply eval_fix_value; tea.
          -- apply (proj2 (Stdlib.Lists.List.Forall_app _ _ _)); split; auto.
    (* cofix case *)
    - cls.
      match goal with Hd : R [] (mkApps (tCoFix _ _) args) ?w |- _ =>
        destruct (cofix_spine_inv _ _ _ _ Hd) as (mfix' & args' & [-> Hdefs Hargs]) end.
      match goal with Hc : is_true (closedn 0 (mkApps (tCoFix _ _) args)) |- _ =>
        rewrite closedn_mkApps in Hc; move/andP: Hc => [Hcf Hcargs] end.
      match goal with Hu : cunfold_cofix mfix idx = Some _ |- _ =>
        destruct (cunfold_cofix_rel _ _ _ _ _ Hdefs Hcf Hu) as (fn' & Hu' & Hfn);
        have Hcfn := closed_cunfold_cofix _ _ _ _ Hcf Hu end.
      match goal with Hb : Rbrs [] brs ?brs' |- _ =>
        have HG3 : R [] (tCase ip (mkApps fn args) brs) (tCase ip (mkApps fn' args') brs')
          by (apply R_s, Rs_case; auto; apply R_mkApps; auto) end.
      have Hc3 : closedn 0 (tCase ip (mkApps fn args) brs)
        by (cbn; rewrite closedn_mkApps Hcfn Hcargs /=; assumption).
      lft. eexists; split; [|eassumption]. sq. eapply eval_cofix_case; tea.
    (* cofix proj *)
    - cls.
      match goal with Hd : R [] (mkApps (tCoFix _ _) args) ?w |- _ =>
        destruct (cofix_spine_inv _ _ _ _ Hd) as (mfix' & args' & [-> Hdefs Hargs]) end.
      match goal with Hc : is_true (closedn 0 (mkApps (tCoFix _ _) args)) |- _ =>
        rewrite closedn_mkApps in Hc; move/andP: Hc => [Hcf Hcargs] end.
      match goal with Hu : cunfold_cofix mfix idx = Some _ |- _ =>
        destruct (cunfold_cofix_rel _ _ _ _ _ Hdefs Hcf Hu) as (fn' & Hu' & Hfn);
        have Hcfn := closed_cunfold_cofix _ _ _ _ Hcf Hu end.
      have HG3 : R [] (tProj p (mkApps fn args)) (tProj p (mkApps fn' args'))
        by (apply R_s, Rs_proj; apply R_mkApps; auto).
      have Hc3 : closedn 0 (tProj p (mkApps fn args))
        by (cbn; rewrite closedn_mkApps Hcfn Hcargs //).
      lft. eexists; split; [|eassumption]. sq. eapply eval_cofix_proj; tea.
    (* delta *)
    - match goal with Hb : cst_body decl = Some body |- _ =>
        destruct (Hcst _ _ _ isdecl Hb) as (decl' & b' & Hd' & Hb' & HG);
        have Hcb := lookup_env_closed clΣ isdecl; cbn in Hcb; rewrite Hb in Hcb; cbn in Hcb end.
      lft. eexists; split; [|eassumption]. sq. eapply eval_delta; tea.
    (* proj *)
    - cls.
      match goal with Hd : R [] (mkApps (tConstruct _ _ _) args) ?w, evw : eval Σ' _ ?w |- _ =>
        destruct (constr_spine_inv _ _ _ _ Hd (eval_to_value _ _ evw))
          as [(args' & -> & Hargs)|(p0 & a0 & vs' & j & [-> Hl _ Hj [Hlen _]])] end.
      2:{ exfalso.
          match goal with Hi : constructor_isprop_pars_decl Σ _ _ = Some _ |- _ =>
            destruct (pars_args_isprop _ _ _ _ _ _ _ Hi Hl) as [-> ->] end. lia. }
      apply Rl_Forall2 in Hargs. have Hlen := Forall2_length Hargs.
      match goal with Hn : nth_error args _ = Some a |- _ =>
        destruct (Forall2_nth_error_l _ _ _ _ _ Hargs Hn) as (a' & Hn' & Ha') end.
      match goal with Hc : is_true (closedn 0 (mkApps (tConstruct _ _ _) args)), Hn : nth_error args _ = Some a |- _ =>
        rewrite closedn_mkApps /= in Hc; eapply forallb_nth_error in Hc; erewrite Hn in Hc; cbn in Hc end.
      lft. eexists; split; [|eassumption]. sq. eapply eval_proj; tea.
      + rewrite -(same_constructor_isprop_pars_decl _ _ Hind). eassumption.
      + now rewrite -Hlen.
    (* proj prop *)
    - match goal with Hb : R [] tBox ?w |- _ => inv_s Hb end.
      exists tBox. split; [|apply R_s; constructor]. sq. eapply eval_proj_prop; tea.
      rewrite -(same_inductive_isprop_and_pars _ _ Hind). eassumption.
    (* construct *)
    - cls.
      match goal with Hc : is_true (closedn 0 (mkApps (tConstruct _ _ _) args)) |- _ =>
        have Hcargs := Hc; rewrite closedn_mkApps /= in Hcargs end.
      match goal with Ha : R [] a' ?w, eva : eval Σ' _ ?w |- _ =>
        rename eva into eva0; rename Ha into Hav; rename w into aw end.
      have Hsw : selfeval' aw by (sq; apply value_final; eapply eval_to_value; exact eva0).
      match goal with Hd : R [] (mkApps (tConstruct _ _ _) args) ?w, evw : eval Σ' _ ?w |- _ =>
        destruct (constr_spine_inv _ _ _ _ Hd (eval_to_value _ _ evw))
          as [(args' & -> & Hargs)|(p0 & a0 & vs' & j & [-> Hl Hargs Hj [Hlen Hself]])];
        rename evw into evf; rename Hd into Hf end.
      + have Hlen := Rl_length _ _ _ _ _ Hargs.
        eexists (tApp (mkApps (tConstruct ind c []) args') _). split.
        * sq. eapply eval_construct; tea.
          -- rewrite -(same_lookup_constructor _ _ Hind). eassumption.
          -- now rewrite -Hlen.
        * apply R_s, Rs_app; auto.
      + have Hlen' := Rl_length _ _ _ _ _ Hargs.
        match goal with Hlk : lookup_constructor Σ ind c = Some _ |- _ =>
          have Har := pars_args_lookup _ _ _ _ _ _ _ Hlk Hl;
          have Hlk' := Hlk; rewrite (same_lookup_constructor _ _ Hind) in Hlk' end.
        have Hcvs' : forallb (closedn 0) vs' by (eapply Rl_closed; tea).
        have Hrl : Rl [] (args ++ [a']) (vs' ++ [aw])
          by (apply Rl_app; auto; constructor; auto; constructor).
        have Hfa : Forall selfeval' (vs' ++ [aw]) by (apply (proj2 (Stdlib.Lists.List.Forall_app _ _ _)); split; auto).
        destruct j as [|j]; [lia|].
        change (pwrap (S j) (tConstruct ind c []) vs')
          with (tLambda nAnon (mk_lams j (mkApps (tConstruct ind c []) (vs' ++ rels_down (S j))))) in evf.
        destruct j as [|j].
        * exists (mkApps (tConstruct ind c []) (vs' ++ [aw])). split.
          -- destruct (eval_constr_self ind c (vs' ++ [aw]) _ _ _ Hlk') as [evc]; auto.
             { rewrite length_app /=. lia. }
             sq. eapply eval_beta; [exact evf|exact eva0|].
             rewrite csubst_pwrap //. unfold pwrap. cbn [mk_lams rels_down].
             rewrite app_nil_r. exact evc.
          -- change (tApp ?f ?x) with (mkApps f [x]). rewrite -mkApps_app.
             apply R_mkApps; auto. apply R_s; constructor; constructor.
        * exists (pwrap (S j) (tConstruct ind c []) (vs' ++ [aw])). split.
          -- sq. eapply eval_beta; [exact evf|exact eva0|].
             rewrite csubst_pwrap //. now apply eval_atom.
          -- change (tApp ?f ?x) with (mkApps f [x]). rewrite -mkApps_app.
             apply (R_constr_part Σ Σ' [] ind c p0 a0 (args ++ [a']) (vs' ++ [aw]) (S j)); auto.
             ++ lia.
             ++ rewrite length_app /=. lia.
             ++ rewrite closedn_mkApps forallb_app Hcargs /= andb_true_r. assumption.
             ++ sq. rewrite mkApps_app. apply value_final. eapply eval_to_value.
                eapply eval_construct; tea.
    (* app cong *)
    - cbn -[isFixApp isConstructApp isPrimApp isLazyApp isLambda isBox] in i.
      assert (Hnf : ~~ isFixApp f') by (apply/negP => Hx; move: i; rewrite Hx ?orb_true_r /= ?orb_true_r //).
      assert (Hnc : ~~ isConstructApp f') by (apply/negP => Hx; move: i; rewrite Hx ?orb_true_r /= ?orb_true_r //).
      match goal with Hf : R [] f' ?w |- _ => destruct (head_rel _ _ Hf Hnf Hnc) as [E1 E2 E3 E4 E5 E6] end.
      eexists. split; [|apply R_s, Rs_app; eassumption]. sq. eapply eval_app_cong; tea.
      cbn -[isFixApp isConstructApp isPrimApp isLazyApp isLambda isBox].
      rewrite E1 E2 E3 E4 E5 E6.
      rewrite (negbTE Hnf) (negbTE Hnc) in i. exact i.
    (* prim *)
    - depelim X. eexists. split; [sq; eapply eval_prim; constructor|apply R_s; constructor].
    - depelim X. eexists. split; [sq; eapply eval_prim; constructor|apply R_s; constructor].
    - depelim X. eexists. split; [sq; eapply eval_prim; constructor|apply R_s; constructor].
    - depelim X. cbn in Hc. move/andP: Hc => [Hcd Hcv].
      match goal with ev : All2_Set _ ?v _, a : All2_over ?ev _, H : Rl [] ?v _ |- _ =>
        destruct (sim_args _ _ ev a Hcv _ H) as (v1 & [evs] & Hv1) end.
      lft.
      eexists (tPrim (prim_array {| array_default := _; array_value := v1 |})).
      split; [sq; eapply eval_prim; now constructor|apply R_s; now constructor].
    (* force *)
    - match goal with Hl : R [] (tLazy _) ?w |- _ => inv_s Hl end.
      cls.
      match goal with Hc : is_true (closedn 0 (tLazy _)) |- _ => cbn in Hc end.
      lft. eexists; split; [|eassumption]. sq. eapply eval_force; tea.
    (* atoms *)
    - exists tBox. split; [sq; now apply eval_atom|apply R_s; constructor].
    - eexists; split; [sq; now apply eval_atom|apply R_s; constructor; assumption].
    - eexists; split; [sq; now apply eval_atom|apply R_s; constructor; assumption].
    - have Hcf' : closedn 0 (tFix mfix' idx)
        by (eapply R_closed; [apply R_s, Rs_fix; eassumption|exact Hc]).
      rewrite eta_wrap_pwrap //. eexists; split; [sq; now apply eval_atom|].
      apply (R_fix_part Σ Σ' [] mfix mfix' idx d [] [] (S (rarg d)));
        [assumption|assumption|constructor|lia|cbn; lia|exact Hc|sq; now apply eval_atom|constructor].
    - eexists; split; [sq; now apply eval_atom|apply R_s; constructor; assumption].
    - destruct args; [|cbn in i; discriminate i].
      match goal with HR : Rl [] [] _ |- _ => inversion HR; subst end.
      eexists; split; [sq; apply eval_atom|apply R_s; constructor; constructor].
      cbn -[lookup_constructor] in i |- *. rewrite -(same_lookup_constructor _ _ Hind). exact i.
    - destruct (p + a) as [|n] eqn:E.
      + rewrite eta_wrap_0.
        eexists; split; [sq; apply eval_atom|apply R_s; constructor; constructor].
        cbn -[lookup_constructor] in i |- *. rewrite -(same_lookup_constructor _ _ Hind). exact i.
      + rewrite eta_wrap_pwrap //. eexists; split; [sq; now apply eval_atom|].
        apply (R_constr_part Σ Σ' [] ind c p a [] [] (S n));
          [assumption|constructor|lia|cbn; lia|reflexivity|sq; now apply eval_atom|constructor].
    - eexists; split; [sq; now apply eval_atom|apply R_s; constructor; assumption].
  Qed.

  Theorem eta_simulation t t' v :
    closedn 0 t -> R [] t t' -> eval Σ t v ->
    exists v', ∥ eval Σ' t' v' ∥ /\ R [] v v'.
  Proof.
    intros Hc H ev. exact (sim_lift _ _ ev (eta_simulation_s _ _ ev) Hc _ H).
  Qed.
End Sim.

(** ** The expansion function is in the relation *)

Lemma Forall2_map_self {A B} (P : A -> B -> Prop) (f : A -> B) l :
  All (fun x => P x (f x)) l -> Forall2 P l (map f l).
Proof. induction 1; cbn; constructor; auto. Qed.

Lemma eta_Rs Σ Σ' t Γ napp : Rs Σ Σ' Γ t (eta Σ Γ napp t).
Proof.
  induction t in Γ, napp |- * using term_forall_list_ind; cbn [eta].
  all: try (constructor; auto using R_s; fail).
  - destruct nth_error eqn:E; [destruct Nat.ltb|]; constructor; auto.
  - constructor. apply Rl_Forall2, Forall2_map_self.
    eapply All_impl; [exact X|]. cbn. intros. now apply R_s.
  - destruct args as [|x args].
    + cbn [map]. destruct lookup_constructor_pars_args as [[p a]|] eqn:E.
      * destruct Nat.ltb; [now apply Rs_construct_eta|constructor; constructor].
      * constructor; constructor.
    + constructor. apply Rl_Forall2, Forall2_map_self.
      eapply All_impl; [exact X|]. cbn. intros. now apply R_s.
  - constructor; [now apply R_s|]. apply Rbrs_Forall2, Forall2_map_self.
    eapply All_impl; [exact X|]. cbn. intros. split; cbn; auto. now apply R_s.
  - assert (Hd : Rdefs Σ Σ' (fix_ctx m ++ Γ) m
              (map (map_def (eta Σ (rev_map (fun d => S (rarg d)) m ++ Γ) 0)) m)).
    { apply Rdefs_Forall2, Forall2_map_self. unfold fix_ctx.
      eapply All_impl; [exact X|]. cbn. intros. repeat split; cbn; auto. now apply R_s. }
    destruct nth_error eqn:E; [destruct Nat.leb|]; try (now constructor).
  - constructor. apply Rdefs_Forall2, Forall2_map_self.
    eapply All_impl; [exact X|]. cbn. intros. repeat split; cbn; auto. now apply R_s.
  - destruct p as [? []]; cbn; try constructor.
    destruct a as [d v]. depelim X. destruct p as [Hd Hv]. cbn in Hd, Hv |- *.
    constructor; [now apply R_s|]. apply Rl_Forall2, Forall2_map_self.
    eapply All_impl; [exact Hv|]. cbn. intros. now apply R_s.
Qed.

(** ** Program-level statement *)

Definition eta_value_rel (Σ : global_declarations) (v v' : term) : Prop :=
  R Σ (eta_expand_env Σ) [] v v'.

Theorem eta_expand_eval {efl : EWellformed.EEnvFlags} Σ t v :
  wf_glob Σ -> closedn 0 t -> eval Σ t v ->
  exists v', ∥ eval (eta_expand_env Σ) (eta Σ [] 0 t) v' ∥ /\ eta_value_rel Σ v v'.
Proof.
  intros wfΣ Hc ev.
  eapply (eta_simulation Σ (eta_expand_env Σ)); tea.
  - now eapply wellformed_closed_env.
  - intros kn. symmetry. apply (lookup_minductive_eta_env_gen Σ Σ).
  - intros c decl b Hd Hb.
    exists (eta_constant_decl Σ decl), (eta Σ [] 0 b). repeat split.
    + unfold declared_constant, eta_expand_env in *.
      rewrite (lookup_env_eta_env_gen Σ Σ) Hd //.
    + cbn. now rewrite Hb.
    + apply R_s, eta_Rs.
  - apply R_s, eta_Rs.
Qed.
