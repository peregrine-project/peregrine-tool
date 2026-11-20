(** * The lambda-box passes are chains of rewrite steps, and preserve evaluation

    [optimize o t] is reached from [t] by finitely many parallel steps of the
    rewrite relation [R] of [ELboxOptsSim] (one step per level of nesting),
    and each step is simulated by evaluation ([ELboxOptsSimEval]). *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
  ECSubst EGlobalEnv EWcbvEval EProgram EWellformed EBeta.
From MetaRocq.Erasure.Typed Require Optimize OptimizeCorrectness.
From Peregrine Require ELboxOptsWf_case.
From Peregrine Require Import ELboxOptsSimDB ELboxOpts ELboxOptsSim ELboxOptsSimEval.
From Peregrine Require ELiftConstants.
From Equations Require Import Equations.

Local Open Scope bool_scope.
Set Default Goal Selector "!".

(** ** Iterated relations *)

Fixpoint itr {A} (r : A -> A -> Prop) n x y : Prop :=
  match n with 0 => x = y | S n => exists z, r x z /\ itr r n z y end.

Lemma itr_S {A} (r : A -> A -> Prop) n x y :
  (forall x, r x x) -> itr r n x y -> itr r (S n) x y.
Proof. intros rf H. exists x. split; auto. Qed.

Lemma itr_pad {A} (r : A -> A -> Prop) n m x y :
  (forall x, r x x) -> n <= m -> itr r n x y -> itr r m x y.
Proof. intros rf Hle H. induction Hle; auto. now apply itr_S. Qed.

Lemma itr_snoc {A} (r : A -> A -> Prop) n x y z :
  itr r n x y -> r y z -> itr r (S n) x z.
Proof.
  induction n in x |- *; cbn.
  - intros -> H. exists z; split; auto.
  - intros (w & H1 & H2) H. exists w; split; auto. now apply IHn.
Qed.

Lemma itr_map1 {A B} (rA : A -> A -> Prop) (rB : B -> B -> Prop) (c : A -> B) n x y :
  (forall x y, rA x y -> rB (c x) (c y)) -> itr rA n x y -> itr rB n (c x) (c y).
Proof.
  intros Hc. induction n in x |- *; cbn.
  - now intros ->.
  - intros (z & H1 & H2). exists (c z). split; auto.
Qed.

Lemma itr_map2 {A B C} (rA : A -> A -> Prop) (rB : B -> B -> Prop) (rC : C -> C -> Prop)
  (c : A -> B -> C) n x x' y y' :
  (forall x x' y y', rA x x' -> rB y y' -> rC (c x y) (c x' y')) ->
  itr rA n x x' -> itr rB n y y' -> itr rC n (c x y) (c x' y').
Proof.
  intros Hc. induction n in x, y |- *; cbn.
  - now intros -> ->.
  - intros (z & H1 & H2) (w & H3 & H4). exists (c z w). split; auto.
Qed.

Lemma itr_lift2 {A B C} (rA : A -> A -> Prop) (rB : B -> B -> Prop) (rC : C -> C -> Prop)
  (c : A -> B -> C) x x' y y' :
  (forall x, rA x x) -> (forall y, rB y y) ->
  (forall x x' y y', rA x x' -> rB y y' -> rC (c x y) (c x' y')) ->
  (exists n, itr rA n x x') -> (exists n, itr rB n y y') ->
  exists n, itr rC n (c x y) (c x' y').
Proof.
  intros fA fB Hc [n Hn] [m Hm]. exists (Nat.max n m).
  eapply itr_map2; tea; eapply itr_pad; tea; lia.
Qed.

Lemma itr_lift1 {A B} (rA : A -> A -> Prop) (rB : B -> B -> Prop) (c : A -> B) x x' :
  (forall x y, rA x y -> rB (c x) (c y)) ->
  (exists n, itr rA n x x') -> exists n, itr rB n (c x) (c x').
Proof. intros Hc [n Hn]. exists n. eapply itr_map1; tea. Qed.

Lemma itr_app {A} (r : A -> A -> Prop) n m x y z :
  itr r n x y -> itr r m y z -> itr r (n + m) x z.
Proof.
  induction n in x |- *; cbn.
  - now intros ->.
  - intros (w & H1 & H2) H. exists w; split; auto.
Qed.

(** ** The static part *)

Section Static.
  Context {wfl : WcbvFlags}.

  Definition Rall t t' := forall Σ', R Σ' t t'.
  Definition Rsall l l' := forall Σ', Rs Σ' l l'.
  Definition Rbrsall l l' := forall Σ', Rbrs Σ' l l'.
  Definition Rdefsall l l' := forall Σ', Rdefs Σ' l l'.

  Lemma Rall_refl t : Rall t t.
  Proof. intros Σ'. apply R_refl. Qed.
  Lemma Rsall_refl l : Rsall l l.
  Proof. intros Σ'. apply Rs_refl. Qed.
  Lemma Rbrsall_refl l : Rbrsall l l.
  Proof. intros Σ'. induction l as [|[n b] l]; constructor; auto. apply R_refl. Qed.
  Lemma Rdefsall_refl l : Rdefsall l l.
  Proof. intros Σ'. induction l as [|[na b r] l]; constructor; auto. apply R_refl. Qed.

  Definition chain t t' := exists n, itr Rall n t t'.

  Lemma chain_refl t : chain t t.
  Proof. now exists 0. Qed.

  Lemma chain_trans t u v : chain t u -> chain u v -> chain t v.
  Proof. intros [n Hn] [m Hm]. exists (n + m). eapply itr_app; tea. Qed.

  Lemma chain_one t t' : Rall t t' -> chain t t'.
  Proof. intros H. exists 1, t'. split; auto. reflexivity. Qed.

  Variable o : lbox_opts.
  Hypothesis Hnode : forall t, chain t (rewrite_node o t).

  Lemma chain_node t t' : chain t t' -> chain t (rewrite_node o t').
  Proof. intros H. eapply chain_trans; [exact H|apply Hnode]. Qed.

  Lemma chains_map f l :
    All (fun t => chain t (f t)) l -> exists n, itr Rsall n l (map f l).
  Proof.
    induction 1; cbn; [now exists 0|].
    eapply (itr_lift2 Rall Rsall Rsall cons); tea;
      [apply Rall_refl|apply Rsall_refl|].
    intros ? ? ? ? H1 H2 Σ'. constructor; auto.
  Qed.

  Lemma chbrs_map f (l : list (list name × term)) :
    All (fun x => chain x.2 (f x.2)) l -> exists n, itr Rbrsall n l (map (on_snd f) l).
  Proof.
    induction 1 as [|[na b] l H X IH]; cbn; [now exists 0|].
    eapply (itr_lift2 Rall Rbrsall Rbrsall (fun b l => (na, b) :: l)); tea;
      [apply Rall_refl|apply Rbrsall_refl|].
    intros ? ? ? ? H1 H2 Σ'. constructor; auto.
  Qed.

  Lemma chdefs_map g (l : mfixpoint term) :
    All (fun x => chain (dbody x) (g (dbody x))) l ->
    exists n, itr Rdefsall n l (map (map_def g) l).
  Proof.
    induction 1 as [|[na b r] l H X IH]; cbn; [now exists 0|].
    eapply (itr_lift2 Rall Rdefsall Rdefsall
              (fun b l => {| dname := na; dbody := b; rarg := r |} :: l)); tea;
      [apply Rall_refl|apply Rdefsall_refl|].
    intros ? ? ? ? H1 H2 Σ'. constructor; auto.
  Qed.

  Ltac cg := intros; intros Σ'; apply R_head; constructor; auto.

  Lemma optimize_chain t :
    chain t (optimize o t) /\ chain t (optimize_fix_body (optimize o) t).
  Proof.
    induction t using term_forall_list_ind.
    all: try (match goal with |- chain (tLambda _ _) _ /\ _ => fail 1 | _ => idtac end;
              match goal with |- chain ?T _ /\ _ =>
                enough (H : chain T (optimize o T)) by (split; exact H) end;
              apply chain_node; cbn [map_subterms_fix map_subterms]).
    - apply chain_refl.
    - apply chain_refl.
    - apply chain_refl.
    - eapply (itr_lift1 Rsall Rall (tEvar n)); [cg|].
      apply chains_map. eapply All_impl; [exact X|]. now intros ? [].
    - destruct IHt as [IH _].
      assert (H : chain (tLambda n t) (tLambda n (optimize o t))).
      { eapply (itr_lift1 Rall Rall (tLambda n)); [cg|exact IH]. }
      split; [|exact H]. now apply chain_node.
    - destruct IHt1 as [IH1 _], IHt2 as [IH2 _].
      eapply (itr_lift2 Rall Rall Rall (tLetIn n)); tea; try apply Rall_refl. cg.
    - destruct IHt1 as [IH1 _], IHt2 as [IH2 _].
      eapply (itr_lift2 Rall Rall Rall tApp); tea; try apply Rall_refl. cg.
    - apply chain_refl.
    - eapply (itr_lift1 Rsall Rall (tConstruct i n)); [cg|].
      apply chains_map. eapply All_impl; [exact X|]. now intros ? [].
    - destruct IHt as [IH _].
      eapply (itr_lift2 Rall Rbrsall Rall (tCase p)); tea;
        [apply Rall_refl|apply Rbrsall_refl|cg|].
      apply chbrs_map. eapply All_impl; [exact X|]. now intros ? [].
    - destruct IHt as [IH _].
      eapply (itr_lift1 Rall Rall (tProj s)); [cg|exact IH].
    - eapply (itr_lift1 Rdefsall Rall (fun m => tFix m n)); [cg|].
      apply chdefs_map. eapply All_impl; [exact X|]. now intros ? [].
    - eapply (itr_lift1 Rdefsall Rall (fun m => tCoFix m n)); [cg|].
      apply chdefs_map. eapply All_impl; [exact X|]. now intros ? [].
    - destruct p as [? []]; cbn; try apply chain_refl.
      depelim X. destruct p as [Hd Hv]. destruct a; cbn in *.
      destruct Hd as [Hd _].
      eapply (itr_lift2 Rall Rsall Rall
                (fun d v => tPrim (prim_array {| array_default := d; array_value := v |}))); tea;
        [apply Rall_refl|apply Rsall_refl|cg|].
      apply chains_map. eapply All_impl; [exact Hv|]. now intros ? [].
    - destruct IHt as [IH _].
      eapply (itr_lift1 Rall Rall tLazy); [cg|exact IH].
    - destruct IHt as [IH _].
      eapply (itr_lift1 Rall Rall tForce); [cg|exact IH].
  Qed.

End Static.

(** ** Environments and programs *)

Section Program.
  Context {wfl : WcbvFlags}.
  Hypothesis Hguard : with_guarded_fix = false.
  Hypothesis Hprop : with_prop_case = false.

  Definition decl_step (d d' : global_decl) : Prop :=
    match d, d' with
    | ConstantDecl cb, ConstantDecl cb' =>
        match cst_body cb, cst_body cb' with
        | Some b, Some b' => Rall b b'
        | None, None => True
        | _, _ => False
        end
    | InductiveDecl m, InductiveDecl m' => m = m'
    | _, _ => False
    end.

  Inductive env_step : global_declarations -> global_declarations -> Prop :=
  | es_nil : env_step [] []
  | es_cons kn d d' Σ Σ' :
      decl_step d d' -> env_step Σ Σ' -> env_step ((kn, d) :: Σ) ((kn, d') :: Σ').

  Lemma decl_step_refl d : decl_step d d.
  Proof. destruct d as [[[b|]]|m]; cbn; auto. apply Rall_refl. Qed.

  Lemma env_step_refl Σ : env_step Σ Σ.
  Proof. induction Σ as [|[kn d] Σ]; constructor; auto. apply decl_step_refl. Qed.

  Lemma env_step_lookup Σ Σ' kn :
    env_step Σ Σ' ->
    match lookup_env Σ kn with
    | Some d => exists d', lookup_env Σ' kn = Some d' /\ decl_step d d'
    | None => lookup_env Σ' kn = None
    end.
  Proof.
    induction 1; cbn; auto.
    destruct (eq_kername kn kn0); eauto.
  Qed.

  Lemma env_step_minductive Σ Σ' kn :
    env_step Σ Σ' -> lookup_minductive Σ kn = lookup_minductive Σ' kn.
  Proof.
    intros H. pose proof (env_step_lookup _ _ kn H) as L.
    unfold lookup_minductive. destruct (lookup_env Σ kn) as [d|]; cbn.
    - destruct L as (d' & -> & Hd). cbn.
      destruct d as [cb|m], d' as [cb'|m']; cbn in *; try contradiction; congruence.
    - now rewrite L.
  Qed.

  Lemma env_step_constant Σ Σ' kn b :
    env_step Σ Σ' -> declared_constant Σ kn {| cst_body := Some b |} ->
    exists b', declared_constant Σ' kn {| cst_body := Some b' |} /\ R Σ' b b'.
  Proof.
    intros H Hd. pose proof (env_step_lookup _ _ kn H) as L.
    unfold declared_constant in *. rewrite Hd in L.
    destruct L as (d' & L & Hs). destruct d' as [[[b'|]]|]; cbn in Hs; try contradiction.
    exists b'. split; auto.
  Qed.

  Lemma env_step_closed Σ Σ' : env_step Σ Σ' -> closed_env Σ -> closed_env Σ'.
  Proof.
    induction 1; cbn; auto.
    move/andP => [Hd Hcl]. apply/andP; split; auto.
    unfold test_snd in *; cbn in *.
    destruct d as [[[b|]]|m], d' as [[[b'|]]|m']; cbn in *; try contradiction; auto.
    exact (R_closed [] _ _ 0 (H []) Hd).
  Qed.

  (** the observable relation on values: a chain of rewrite steps *)
  Inductive obs : term -> term -> Prop :=
  | obs_refl v : obs v v
  | obs_step Σ' v v' v'' : R Σ' v v' -> obs v' v'' -> obs v v''.

  Lemma step_pres Σ Σ' t t' v :
    env_step Σ Σ' -> Rall t t' -> closed_env Σ -> closed t ->
    eval Σ t v ->
    (closed_env Σ' /\ closed t') /\
    exists v', ∥ eval Σ' t' v' ∥ /\ R Σ' v v'.
  Proof.
    intros He Ht Hcl Hct ev.
    assert (Hcl' : closed_env Σ') by (eapply env_step_closed; tea).
    split.
    - split; auto.
      exact (R_closed [] _ _ 0 (Ht []) Hct).
    - eapply (simulation Hguard Hprop Σ Σ'); tea.
      + intros kn. now apply env_step_minductive.
      + intros kn b. now apply env_step_constant.
      + apply Ht.
  Qed.

  Lemma chain_pres n : forall Σ Σ' t t' v,
    itr env_step n Σ Σ' -> itr Rall n t t' -> closed_env Σ -> closed t ->
    eval Σ t v ->
    exists v', ∥ eval Σ' t' v' ∥ /\ obs v v'.
  Proof.
    induction n; cbn; intros Σ Σ' t t' v He Ht Hcl Hct ev.
    - subst. exists v. split; [now sq|constructor].
    - destruct He as (Σ1 & He1 & He), Ht as (t1 & Ht1 & Ht).
      destruct (step_pres _ _ _ _ _ He1 Ht1 Hcl Hct ev) as [(Hcl1 & Hct1) (v1 & [ev1] & Hv1)].
      destruct (IHn _ _ _ _ _ He Ht Hcl1 Hct1 ev1) as (v' & ev' & Hv').
      exists v'. split; auto. econstructor; tea.
  Qed.

  Variable o : lbox_opts.
  Hypothesis Hnode : forall t, chain t (rewrite_node o t).

  Lemma optimize_decl_chain d : exists n, itr decl_step n d (optimize_decl o d).
  Proof.
    destruct d as [[[b|]]|m]; cbn; try (now exists 0).
    destruct (optimize_chain o Hnode b) as [[n Hn] _]. exists n.
    eapply (itr_map1 Rall decl_step (fun b => ConstantDecl {| cst_body := Some b |})); tea.
    now cbn.
  Qed.

  Lemma optimize_env_chain Σ : exists n, itr env_step n Σ (optimize_env o Σ).
  Proof.
    induction Σ as [|[kn d] Σ IH]; cbn; [now exists 0|].
    eapply (itr_lift2 decl_step env_step env_step (fun d Σ => (kn, d) :: Σ)); tea;
      [apply decl_step_refl|apply env_step_refl| |apply optimize_decl_chain].
    intros; now constructor.
  Qed.

  Theorem lbox_opts_program_pres (p : eprogram) v :
    closed_env p.1 -> closed p.2 ->
    eval p.1 p.2 v ->
    exists v', ∥ eval (lbox_opts_program o p).1 (lbox_opts_program o p).2 v' ∥ /\ obs v v'.
  Proof.
    intros Hcl Hct ev.
    destruct (optimize_env_chain p.1) as [n Hn].
    destruct (optimize_chain o Hnode p.2) as [[m Hm] _].
    eapply (chain_pres (Nat.max n m)); tea.
    - eapply itr_pad; tea; [apply env_step_refl|lia].
    - eapply itr_pad; tea; [apply Rall_refl|lia].
  Qed.

End Program.

(** ** The rewrites, one node at a time *)

Section Nodes.
  Context {wfl : WcbvFlags}.

  Lemma chain_letin z v b b' : chain b b' -> chain (tLetIn z v b) (tLetIn z v b').
  Proof.
    eapply (itr_lift1 Rall Rall (tLetIn z v)). intros x y H Σ'.
    apply R_head; constructor; [apply R_refl|apply H].
  Qed.

  Lemma chain_app f f' a : chain f f' -> chain (tApp f a) (tApp f' a).
  Proof.
    eapply (itr_lift1 Rall Rall (fun f => tApp f a)). intros x y H Σ'.
    apply R_head; constructor; [apply H|apply R_refl].
  Qed.

  Lemma chain_mkApps f f' args : chain f f' -> chain (mkApps f args) (mkApps f' args).
  Proof. induction args in f, f' |- *; cbn; auto. intros H. apply IHargs. now apply chain_app. Qed.

  Lemma chain_case ci d brs brs' :
    (exists n, itr Rbrsall n brs brs') -> chain (tCase ci d brs) (tCase ci d brs').
  Proof.
    eapply (itr_lift1 Rbrsall Rall (tCase ci d)). intros x y H Σ'.
    apply R_head; constructor; [apply R_refl|apply H].
  Qed.

  Lemma chbrs_pointwise (g h : list name × term -> term) l :
    (forall br, chain (g br) (h br)) ->
    exists n, itr Rbrsall n (map (fun br => (br.1, g br)) l) (map (fun br => (br.1, h br)) l).
  Proof.
    intros H. induction l as [|br l IH]; cbn; [now exists 0|].
    eapply (itr_lift2 Rall Rbrsall Rbrsall (fun b l => (br.1, b) :: l)); tea;
      [apply Rall_refl|apply Rbrsall_refl| |apply H].
    intros ? ? ? ? H1 H2 Σ'. constructor; auto.
  Qed.

  (** *** beta_let *)

  Lemma chain_app_let z v b args :
    chain (mkApps (tLetIn z v b) args) (tLetIn z v (mkApps b (map (lift0 1) args))).
  Proof.
    induction args in b |- *; cbn; [apply chain_refl|].
    eapply chain_trans; [|apply IHargs].
    apply chain_mkApps, chain_one. intros Σ'. apply R_head, Rh_app_let; apply R_refl.
  Qed.

  Lemma chain_app_case ci d brs args :
    chain (mkApps (tCase ci d brs) args)
          (tCase ci d (map (fun br => (br.1, mkApps br.2 (map (lift0 #|br.1|) args))) brs)).
  Proof.
    induction args in brs |- *; cbn.
    - rewrite (map_ext _ id); [now intros []|]. rewrite map_id. apply chain_refl.
    - eapply chain_trans.
      { apply chain_mkApps, chain_one. intros Σ'. apply R_head, Rh_app_case; try apply R_refl.
        apply Rbrsall_refl. }
      eapply chain_trans; [apply IHargs|].
      rewrite map_map. cbn. apply chain_refl.
  Qed.

  Lemma chain_push_args fuel hd args : chain (mkApps hd args) (push_args fuel hd args).
  Proof.
    induction fuel in hd, args |- *; cbn; [apply chain_refl|].
    destruct args as [|a rest]; [apply chain_refl|].
    destruct hd; try apply chain_refl.
    - eapply chain_trans; [|apply IHfuel].
      cbn. apply chain_mkApps, chain_one. intros Σ'. apply R_head, Rh_beta; apply R_refl.
    - eapply chain_trans; [apply (chain_app_let _ _ _ (a :: rest))|].
      apply chain_letin, IHfuel.
  Qed.

  Lemma beta_let_chain t : chain t (beta_let t).
  Proof.
    unfold beta_let. destruct (decompose_app t) as [hd args] eqn:da.
    apply decompose_app_inv in da. subst t.
    destruct hd; try apply chain_refl; destruct args as [|a args]; try apply chain_refl.
    - match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply chain_push_args|apply chain_refl].
    - match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply chain_push_args|apply chain_refl].
    - match goal with |- context [if ?c then _ else _] => destruct c end; [|apply chain_refl].
      eapply chain_trans; [apply chain_app_case|]. apply chain_case.
      refine (chbrs_pointwise _
        (fun br => push_args (S (spine_len br.2)) br.2 (map (lift0 #|br.1|) (a :: args))) _ _).
      intros br. apply chain_push_args.
  Qed.

End Nodes.

(** ** The identity-case pass *)

Lemma case_id_node {wfl : WcbvFlags} t : chain t (rewrite_node case_id_opts t).
Proof.
  apply chain_one.
  intros Σ'. destruct t as [| | | | | | | | |[ind pars] d l| | | | | |]; try apply R_refl. cbn.
  destruct l as [|br brs]; [apply R_refl|].
  destruct pars as [|pars]; [|apply R_refl]. cbn.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end; [|apply R_refl].
  apply R_head, Rh_case_id; [apply R_refl|exact E].
Qed.

(** ** The other node rewrites *)

Lemma case_id_Rall {wfl : WcbvFlags} t : Rall t (case_id t).
Proof.
  intros Σ'. destruct t as [| | | | | | | | |[ind pars] d l| | | | | |]; try apply R_refl. cbn.
  destruct l as [|br brs]; [apply R_refl|].
  destruct pars as [|pars]; [|apply R_refl]. cbn.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end; [|apply R_refl].
  apply R_head, Rh_case_id; [apply R_refl|exact E].
Qed.

Lemma let_inline_node {wfl : WcbvFlags} t : Rall t (let_inline t).
Proof.
  intros Σ'. destruct t as [| | | | |z v b| | | | | | | | | |]; try apply R_refl.
  unfold let_inline. destruct (atomic v); [|apply R_refl].
  apply R_head, Rh_let_inline; apply R_refl.
Qed.

Lemma case_fun_node {wfl : WcbvFlags} t : Rall t (case_fun t).
Proof.
  intros Σ'. destruct t as [| | | | | | | | |ci d brs| | | | | |]; try apply R_refl.
  destruct d; try apply R_refl. destruct brs as [|br0 brs]; [apply R_refl|].
  unfold case_fun. cbv zeta.
  pose proof (ELboxOptsWf_case.fold_left_min_le (fun br : list name × term => count_lambdas br.2)
    (br0 :: brs) (count_lambdas br0.2)) as [_ hmin].
  cbv beta in hmin.
  set (m := fold_left _ _ _) in *.
  destruct (Nat.eqb_spec m 0) as [|nz]; [apply R_refl|].
  have hall : forall br, In br (br0 :: brs) -> has_lambdas m br.2.
  { intros br hin. apply count_has_lambdas. now apply hmin. }
  have L := length_lambda_names_has _ _ (hall br0 (or_introl eq_refl)).
  set (ys := lambda_names m br0.2) in *. clearbody ys m. subst m.
  replace (tRel (n + #|ys|)) with (lift0 #|ys| (tRel n)) by (cbn; now rewrite (Nat.add_comm n)).
  match goal with |- R _ _ (mk_lambdas _ (tCase _ _ ?B)) =>
    replace B with
      (map (fun br : list name × term => (br.1, exchange #|ys| #|br.1| 0 br.2))
         (map (fun br : list name × term => (br.1, strip_lambdas #|ys| br.2)) (br0 :: brs)))
      by (rewrite map_map; reflexivity) end.
  apply R_head, Rh_case_fun.
  - apply R_refl.
  - apply forallb_forall. exact hall.
  - apply Rbrsall_refl.
Qed.

(** ** [fix_eta]

    A variable that does not occur can be substituted and lifted back. *)

Lemma dead_lift n k t :
  (forall j, k <= j -> j < k + n -> Optimize.is_dead j t) ->
  lift n k (subst (repeat tBox n) k t) = t.
Proof.
  induction t in k |- * using term_forall_list_ind; intros H; cbn -[Nat.leb] in *;
    rewrite ?length_map; auto.
  - destruct (Nat.leb_spec k n0).
    + destruct (nth_error (repeat tBox n) (n0 - k)) eqn:E.
      * apply nth_error_Some_length in E. rewrite repeat_length in E.
        specialize (H n0 ltac:(lia) ltac:(lia)). now rewrite Nat.eqb_refl in H.
      * apply nth_error_None in E. rewrite !repeat_length in E |- *.
        cbn -[Nat.leb]. destruct (Nat.leb_spec k (n0 - n)); f_equal; lia.
    + cbn -[Nat.leb]. destruct (Nat.leb_spec k n0); auto; lia.
  - f_equal. induction X; cbn; auto. f_equal.
    + apply p. intros j h1 h2. specialize (H j h1 h2). cbn in H. now rtoProp.
    + apply IHX. intros j h1 h2. specialize (H j h1 h2). cbn in H. now rtoProp.
  - f_equal. apply IHt. intros [|j] h1 h2; [lia|]. apply (H j); lia.
  - f_equal.
    + apply IHt1. intros j h1 h2. specialize (H j h1 h2). now rtoProp.
    + apply IHt2. intros [|j] h1 h2; [lia|]. specialize (H j ltac:(lia) ltac:(lia)). now rtoProp.
  - f_equal.
    + apply IHt1. intros j h1 h2. specialize (H j h1 h2). now rtoProp.
    + apply IHt2. intros j h1 h2. specialize (H j h1 h2). now rtoProp.
  - f_equal. induction X; cbn; auto. f_equal.
    + apply p. intros j h1 h2. specialize (H j h1 h2). cbn in H. now rtoProp.
    + apply IHX. intros j h1 h2. specialize (H j h1 h2). cbn in H. now rtoProp.
  - f_equal.
    + apply IHt. intros j h1 h2. specialize (H j h1 h2). now rtoProp.
    + have H' : forall j, k <= j -> j < k + n ->
        forallb (fun '(ctx, t) => Optimize.is_dead (#|ctx| + j) t) l.
      { intros j h1 h2. specialize (H j h1 h2). now rtoProp. }
      clear H. induction X; cbn; auto. f_equal.
      * destruct x as [ctx b]. cbn in *. f_equal. apply p0.
        intros j h1 h2. specialize (H' (j - #|ctx|) ltac:(lia) ltac:(lia)).
        cbn in H'. replace (#|ctx| + (j - #|ctx|)) with j in H' by lia.
        now move/andP: H' => [].
      * apply IHX. intros j h1 h2. specialize (H' j h1 h2). cbn in H'. now rtoProp.
  - f_equal. apply IHt. intros j h1 h2. now apply H.
  - f_equal. set (L := #|m|) in *. clearbody L. induction X; cbn; auto. f_equal.
    + destruct x as [na b r]. unfold map_def. cbn in *. f_equal. apply p.
      intros j h1 h2. specialize (H (j - L) ltac:(lia) ltac:(lia)).
      cbn in H. replace (L + (j - L)) with j in H by lia.
      now move/andP: H => [].
    + apply IHX. intros j h1 h2. specialize (H j h1 h2). cbn in H. now rtoProp.
  - f_equal. set (L := #|m|) in *. clearbody L. induction X; cbn; auto. f_equal.
    + destruct x as [na b r]. unfold map_def. cbn in *. f_equal. apply p.
      intros j h1 h2. specialize (H (j - L) ltac:(lia) ltac:(lia)).
      cbn in H. replace (L + (j - L)) with j in H by lia.
      now move/andP: H => [].
    + apply IHX. intros j h1 h2. specialize (H j h1 h2). cbn in H. now rtoProp.
  - destruct p as [? []]; cbn in *; auto. depelim X. destruct p as [Hd Hv].
    destruct a as [def vals]; cbn in *. do 3 f_equal.
    unfold map_array_model, test_array_model in *; cbn in *. f_equal.
    + apply Hd. intros j h1 h2. specialize (H j h1 h2). now move/andP: H => [].
    + have H' : forall j, k <= j -> j < k + n -> forallb (Optimize.is_dead j) vals.
      { intros j h1 h2. specialize (H j h1 h2). now move/andP: H => []. }
      clear H. induction Hv; cbn; auto. f_equal.
      * apply p. intros j h1 h2. specialize (H' j h1 h2). cbn in H'. now move/andP: H' => [].
      * apply IHHv. intros j h1 h2. specialize (H' j h1 h2). cbn in H'. now move/andP: H' => [].
  - f_equal. apply IHt. intros j h1 h2. now apply H.
  - f_equal. apply IHt. intros j h1 h2. now apply H.
Qed.

Lemma has_lambdas_subst s k m t : has_lambdas m t -> has_lambdas m (subst s k t).
Proof.
  induction m in k, t |- *; destruct t; cbn; try discriminate; auto.
Qed.

Lemma strip_lambdas_subst s k m t :
  has_lambdas m t -> strip_lambdas m (subst s k t) = subst s (m + k) (strip_lambdas m t).
Proof.
  induction m in k, t |- *; destruct t; cbn; try discriminate; auto.
  intros H. rewrite IHm //. do 2 f_equal. lia.
Qed.

Lemma lift_mk_lambdas n k xs e :
  lift n k (mk_lambdas xs e) = mk_lambdas xs (lift n (#|xs| + k) e).
Proof.
  induction xs in k |- *; cbn; auto. rewrite IHxs. do 3 f_equal. lia.
Qed.

Lemma deadlam_has n i t :
  has_lambdas n t -> i < n -> Optimize.is_dead (n - 1 - i) (strip_lambdas n t) -> deadlam i t.
Proof.
  induction i in n, t |- *; (destruct n; [lia|]); destruct t; try discriminate;
    cbn [has_lambdas strip_lambdas deadlam]; intros hl lt hd.
  - replace (S n - 1 - 0) with n in hd by lia.
    eexists _, (mk_lambdas (lambda_names n t) (subst [tBox] n (strip_lambdas n t))).
    f_equal. rewrite lift_mk_lambdas length_lambda_names_has // Nat.add_0_r.
    rewrite (dead_lift 1 n).
    + intros j h1 h2. now replace j with n by lia.
    + now apply mk_lambdas_strip.
  - eexists _, _. split; [reflexivity|]. apply (IHi n); auto; [lia|].
    now replace (n - 1 - i) with (S n - 1 - S i) by lia.
Qed.

Lemma fix_param_dead_subst s mfix idx n i K :
  i < n -> fix_param_dead mfix idx n i ->
  param_dead (map (map_def (subst s K)) mfix) idx i.
Proof.
  unfold fix_param_dead, param_dead. intros lt. rewrite nth_error_map.
  destruct (nth_error mfix idx) as [d|]; [|discriminate]. move/andP => [hl hd].
  eexists. split; [reflexivity|]. cbn.
  apply (deadlam_has n); auto; [now apply has_lambdas_subst|].
  rewrite strip_lambdas_subst // OptimizeCorrectness.is_dead_subst_other; [lia|].
  unfold occurs_rel in hd. now rewrite negb_involutive in hd.
Qed.

Lemma args_ok_length mfix idx n i args :
  fix_eta_args_ok mfix idx n i args -> i + #|args| = n.
Proof.
  induction args in i |- *; cbn.
  - move/Nat.eqb_eq. lia.
  - move/andP => [_ ok]. apply IHargs in ok. lia.
Qed.

Lemma args_ok_eta mfix idx n (dead : nat -> Prop) :
  (forall i, i < n -> fix_param_dead mfix idx n i -> dead i) ->
  forall args i xs, fix_eta_args_ok mfix idx n i args -> #|xs| + i = n ->
  eta_args dead i xs args.
Proof.
  intros Hd. induction args; intros i xs ok L; cbn in ok.
  - apply Nat.eqb_eq in ok. destruct xs; [constructor|cbn in L; lia].
  - move/andP: ok => [h ok]. have len := args_ok_length _ _ _ _ _ ok.
    destruct xs as [|x xs]; cbn in L; [lia|].
    destruct a; try discriminate.
    + constructor; [apply Hd; auto; lia|]. apply IHargs; auto; lia.
    + apply Nat.eqb_eq in h. replace n0 with #|xs| by lia.
      constructor. apply IHargs; auto; lia.
Qed.

Lemma nofree_range_lift k t :
  nofree_range 0 k t -> lift0 k (subst (repeat tBox k) 0 t) = t.
Proof.
  unfold nofree_range. intros H. apply dead_lift. intros j _ lt.
  eapply forallb_forall in H; [|apply in_seq; split; [apply Nat.le_0_l|exact lt]].
  cbn in H. unfold occurs_rel in H. now rewrite negb_involutive in H.
Qed.

Lemma fix_eta_node {wfl : WcbvFlags} t : Rall t (fix_eta t).
Proof.
  intros Σ'. unfold fix_eta. cbv zeta.
  destruct (Nat.eqb_spec (count_lambdas t) 0) as [|nz]; [apply R_refl|].
  have hl : has_lambdas (count_lambdas t) t by (apply count_has_lambdas; lia).
  have E := mk_lambdas_strip _ _ hl. have L := length_lambda_names_has _ _ hl.
  destruct (decompose_app (strip_lambdas (count_lambdas t) t)) as [hd args] eqn:D.
  apply decompose_app_inv in D.
  destruct hd; try apply R_refl.
  destruct (_ && _) eqn:C; [|apply R_refl].
  move/andP: C => [/andP [nf ok] ar].
  rewrite {1}E D. clear E D hl.
  set (k := count_lambdas t) in *. clearbody k.
  destruct (lambda_names k t) as [|x xs]; cbn in L; [lia|]. subst k.
  rewrite -{1}(nofree_range_lift _ _ nf).
  cbn [mk_lambdas]. apply R_head. cbn [subst].
  eapply Rh_fix_eta; [reflexivity| | |].
  - induction (map _ _) as [|[na b r] l]; constructor; auto. apply R_refl.
  - unfold fix_arity_ok in *. rewrite nth_error_map.
    destruct (nth_error _ _) as [d|]; [|discriminate].
    cbn [option_map dbody map_def]. now apply has_lambdas_subst.
  - eapply args_ok_eta; [|exact ok|cbn; lia].
    intros i lt. now apply fix_param_dead_subst.
Qed.

(** Every node rewrite. *)
(** Generalised iota: every step is one target-side rewrite [crw] of a
    case, followed by rewrites below. *)
Lemma crw_chain {wfl : WcbvFlags} t u : crw t u -> chain t u.
Proof.
  intros H. apply chain_one. intros Σ'. have H' := H. revert H'.
  destruct H; intros H'; apply R_head;
    (eapply Rh_case_tgt; [apply R_refl|apply Rbrsall_refl|exact H']).
Qed.

Lemma iota_lets_chain {wfl : WcbvFlags} args :
  forall n nas b, chain (bind_lets n nas args b) (iota_lets n nas args b).
Proof.
  induction args as [|a args IH]; intros n nas b; cbn [bind_lets iota_lets]; [apply chain_refl|].
  eapply chain_trans; [apply chain_letin, IH|apply chain_one, let_inline_node].
Qed.

Lemma chbrs_pointwise_All {wfl : WcbvFlags} (g h : list name × term -> term) l :
  All (fun br => chain (g br) (h br)) l ->
  exists n, itr Rbrsall n (map (fun br => (br.1, g br)) l) (map (fun br => (br.1, h br)) l).
Proof.
  intros H. induction H as [|br l Hbr Hl IH]; cbn; [now exists 0|].
  eapply (itr_lift2 Rall Rbrsall Rbrsall (fun b l => (br.1, b) :: l)); tea;
    [apply Rall_refl|apply Rbrsall_refl|].
  intros ? ? ? ? H1 H2 Σ'. constructor; auto.
Qed.

Lemma iota_constr_chain {wfl : WcbvFlags} ci d c args brs :
  (forall br, nth_error brs c = Some br -> #|args| = ci.2 + #|br.1| ->
     crw (tCase ci d brs) (bind_lets 0 (List.rev br.1) (skipn ci.2 args) br.2)) ->
  chain (tCase ci d brs) (iota_constr ci c args brs (tCase ci d brs)).
Proof.
  intros H. unfold iota_constr.
  destruct (nth_error brs c) as [br|] eqn:E; [|apply chain_refl].
  destruct (Nat.eqb_spec #|args| (ci.2 + #|br.1|)) as [L|]; [|apply chain_refl].
  eapply chain_trans; [apply crw_chain; exact (H br eq_refl L)|apply iota_lets_chain].
Qed.

Lemma iota_case_chain {wfl : WcbvFlags} ci d :
  forall brs, chain (tCase ci d brs) (iota_case ci d brs).
Proof.
  induction d using term_forall_list_ind; intros brs; try apply chain_refl; cbn [iota_case].
  - eapply chain_trans; [apply crw_chain, crw_let|apply chain_letin, IHd2].
  - match goal with |- context [decompose_app ?t] =>
      destruct (decompose_app t) as [hd xs] eqn:Ed end.
    destruct hd; try apply chain_refl.
    match goal with |- context [match ?l with [] => _ | _ :: _ => _ end] =>
        destruct l; [|apply chain_refl] end.
    apply decompose_app_inv in Ed. rewrite Ed.
    apply iota_constr_chain. intros br Hb Hl. now apply crw_iota_app.
  - apply iota_constr_chain. intros br Hb Hl. now apply crw_iota.
  - destruct (_ && _); [|apply chain_refl].
    eapply chain_trans; [apply crw_chain, crw_case|].
    apply chain_case.
    apply (chbrs_pointwise_All (fun br => tCase ci br.2 (lift_brs #|br.1| brs))
             (fun br => iota_case ci br.2 (lift_brs #|br.1| brs))).
    eapply All_impl; [eassumption|]. intros br Hbr. apply Hbr.
Qed.

Lemma lbox_node {wfl : WcbvFlags} o t : chain t (rewrite_node o t).
Proof.
  destruct t; try apply chain_refl; unfold rewrite_node.
  - destruct (lbox_fix_eta o); [apply chain_one, fix_eta_node|apply chain_refl].
  - destruct (lbox_let_fun o); [apply chain_one, let_inline_node|apply chain_refl].
  - destruct (lbox_let_fun o); [apply beta_let_chain|apply chain_refl].
  - destruct (lbox_iota o); [apply iota_case_chain|]. cbv zeta.
    eapply chain_trans;
      [|destruct (lbox_case_fun o); [apply chain_one, case_fun_node|apply chain_refl]].
    destruct (lbox_case_id o); [apply chain_one, case_id_Rall|apply chain_refl].
Qed.
