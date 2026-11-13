(** * Evaluation preservation for the lambda-box simplifications of [ELboxOpts]

    [R Σ' t t'] relates a source term [t] to a target term [t'] obtained by
    rewriting some subterms of [t] with the local rewrites of [ELboxOpts]
    (one layer of rewrites: every rule looks at the shape of the *source*
    term).  [optimize] is a finite sequence of such steps, and each step is a
    forward simulation for [EWcbvEval.eval] at any flags with unguarded
    fixpoints and no propositional cases, for both representations of
    constructor applications ([cval]: blocks, as in the untyped pipeline, or
    applications, as in the typed one) and with or without constructor
    parameters.

    Besides the congruence rules and the rewrite rules, [R] has rules that keep
    the source fixed and expand the target ([R_cofix], ...): they describe the
    terms that appear at run time once the rewritten program has taken steps
    the source program has not (for instance, an identity case on a cofixpoint
    is removed, so the target holds an unfolded-later cofixpoint where the
    source holds a constructor).

    For fixpoint eta-hoisting ([Rh_fix_eta]) the source value is a closure
    [fun xj .. xk => (fix F ..) cs xj .. xk] where the target value is what
    the partial application [(fix F ..) cs] evaluates to.  [R_fix_part]
    relates the two, provided the target value can take the remaining
    arguments one at a time ([tarity]); [Rh_app_dead] relates a box passed
    for a dead parameter to any closed value. *)

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

(** ** Dead parameters and eta-expanded fixpoints ([fix_eta]) *)

(** [deadlam n t]: [t] is [fun z1 .. zn x => b] where [b] does not mention
    [x]. *)
Fixpoint deadlam (n : nat) (t : term) : Prop :=
  match n with
  | 0 => exists na d, t = tLambda na (lift0 1 d)
  | S n => exists na b, t = tLambda na b /\ deadlam n b
  end.

(** Parameter [i] of function [idx] of the fixpoint block [mf] is dead. *)
Definition param_dead (mf : mfixpoint term) (idx i : nat) : Prop :=
  exists d, nth_error mf idx = Some d /\ deadlam i (dbody d).

(** [eta_args dead j xs args]: under the binders [xs], the arguments [args]
    are the variables bound by [xs], in order, except that the argument at
    position [j + i] may also be a box when [dead (j + i)]. *)
Inductive eta_args (dead : nat -> Prop) : nat -> list name -> list term -> Prop :=
| eta_nil j : eta_args dead j [] []
| eta_var j x xs args :
    eta_args dead (S j) xs args -> eta_args dead j (x :: xs) (tRel #|xs| :: args)
| eta_box j x xs args :
    dead j -> eta_args dead (S j) xs args -> eta_args dead j (x :: xs) (tBox :: args).

(** A function that ignores its next argument: a lambda whose body does not
    mention its variable, or a fixpoint applied up to a dead parameter. *)
Definition dead_head (f : term) : Prop :=
  deadlam 0 f \/
  exists mf idx cs, f = mkApps (tFix mf idx) cs /\ param_dead mf idx #|cs|.

(** ** The relation *)

Section Rel.
  Context {wfl : WcbvFlags} (Σ' : global_declarations).

  (** A constructor applied to [args], in the representation of constructor
      applications selected by the evaluation flags: a block
      [tConstruct ind c args], or the application of [tConstruct ind c []]
      to [args]. *)
  Definition cval (ind : inductive) (c : nat) (args : list term) : term :=
    if with_constructor_as_block then tConstruct ind c args
    else mkApps (tConstruct ind c []) args.

  (** Constructor [c] of [ind] takes exactly [n] arguments. *)
  Definition cfull (ind : inductive) (c n : nat) : Prop :=
    exists mdecl idecl cdecl,
      lookup_constructor Σ' ind c = Some (mdecl, idecl, cdecl) /\ n = cstr_arity mdecl cdecl.

  (** [tarity m w]: [w] can be applied to [m] closed values, one after the
      other, and each of these applications evaluates. *)
  Fixpoint tarity (m : nat) (w : term) : Prop :=
    match m with
    | 0 => True
    | S m => forall a', closed a' -> ∥ value Σ' a' ∥ ->
        exists w3, ∥ eval Σ' (tApp w a') w3 ∥ /\ tarity m w3
    end.

  (** Head reduction steps of the target whose principal part is closed
      and evaluates. *)
  Inductive tred : term -> term -> Prop :=
  | tred_iota ind pars cdecl d c args brs br :
      ∥ eval Σ' d (cval ind c args) ∥ -> closed d -> forallb (closedn 0) args ->
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
      related to) the source constructor, which has all its arguments (so
      that the only way to use it is to analyse it, which unfolds the
      cofixpoint) *)
  | R_cofix ind c args v0 mfix idx args' narg fn :
      R (cval ind c args) v0 -> cfull ind c #|args| ->
      ∥ eval Σ' (mkApps fn args') v0 ∥ ->
      cunfold_cofix mfix idx = Some (narg, fn) ->
      ∥ value Σ' (mkApps (tCoFix mfix idx) args') ∥ ->
      closed (mkApps (tCoFix mfix idx) args') -> closed v0 ->
      R (cval ind c args) (mkApps (tCoFix mfix idx) args')
  (** the target is any closed term evaluating to something related *)
  | R_eval t v0 t' :
      R t v0 -> ∥ eval Σ' t' v0 ∥ -> closed t' -> closed v0 -> R t t'
  (** the target, under some lambdas, head-reduces to something related *)
  | R_exp ys s u t' :
      R s (mk_lambdas ys u) -> tred t' u ->
      closed (mk_lambdas ys u) -> closed (mk_lambdas ys t') ->
      R s (mk_lambdas ys t')
  (** [fix_eta] at run time: the source is the eta-expansion of a fixpoint
      already applied to [cs]; the target is the value of that partial
      application, which can still take the remaining arguments *)
  | R_fix_part x xs mf idx cs args t0 w :
      R (mkApps (tFix mf idx) cs) t0 -> ∥ eval Σ' t0 w ∥ -> tarity #|xs| w ->
      eta_args (param_dead mf idx) #|cs| (x :: xs) args ->
      closed (mkApps (tFix mf idx) cs) -> closed t0 -> closed w ->
      R (tLambda x (mk_lambdas xs (mkApps (tFix mf idx) (cs ++ args)))) w
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
  (** [case_id], for inductive types without parameters: the branches
      rebuild all the arguments of the constructor *)
  | Rh_case_id ind d d' brs :
      R d d' -> all_rebuild ind brs -> Rh (tCase (ind, 0) d brs) d'
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
  (** [fix_eta]: [F] is a fixpoint with at least as many leading lambdas as
      the eta-expansion has *)
  | Rh_fix_eta x xs F mf mf' idx args :
      F = tFix mf idx -> Rdefs mf mf' -> fix_arity_ok mf' idx (S #|xs|) ->
      eta_args (param_dead mf idx) 0 (x :: xs) args ->
      Rh (tLambda x (mk_lambdas xs (mkApps (lift0 (S #|xs|) F) args))) (tFix mf' idx)
  (** a box passed for a dead parameter is related to any closed value *)
  | Rh_app_dead f t0 a' :
      R f t0 -> dead_head f -> closed f -> closed t0 -> closed a' -> ∥ value Σ' a' ∥ ->
      Rh (tApp f tBox) (tApp t0 a')
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

  Lemma head_cval ind c args :
    head (cval ind c args) = tConstruct ind c (if with_constructor_as_block then args else []).
  Proof. unfold cval. destruct with_constructor_as_block; [reflexivity|]. now rewrite head_mkApps. Qed.

  Lemma cval_block ind c args :
    with_constructor_as_block = true -> cval ind c args = tConstruct ind c args.
  Proof. unfold cval. now intros ->. Qed.

  Lemma cval_app ind c args :
    with_constructor_as_block = false -> cval ind c args = mkApps (tConstruct ind c []) args.
  Proof. unfold cval. now intros ->. Qed.

  Lemma cfull_isprop ind c b pars cdecl n :
    constructor_isprop_pars_decl Σ' ind c = Some (b, pars, cdecl) ->
    n = pars + cstr_nargs cdecl -> cfull ind c n.
  Proof.
    unfold constructor_isprop_pars_decl, cfull.
    destruct lookup_constructor as [[[mdecl idecl] cdecl']|]; [|discriminate].
    cbn. intros [= <- <- <-] ->. now eexists _, _, _.
  Qed.

  Lemma closedn_cval k ind c args : closedn k (cval ind c args) = forallb (closedn k) args.
  Proof. unfold cval. destruct with_constructor_as_block; [reflexivity|]. now rewrite closedn_mkApps. Qed.

  Lemma csubst_cval a k ind c args :
    csubst a k (cval ind c args) = cval ind c (map (csubst a k) args).
  Proof. unfold cval. destruct with_constructor_as_block; [reflexivity|]. now rewrite csubst_mkApps. Qed.

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

  Lemma closedn_lift0_inv n k t : closedn (k + n) (lift0 n t) -> closedn k t.
  Proof.
    intros H. rewrite -(simpl_subst_k (repeat tBox n) t 0 n); [now rewrite repeat_length|].
    apply closedn_subst; rewrite ?repeat_length; [|now rewrite Nat.add_comm].
    clear. induction n; cbn; auto.

  Qed.

  Lemma deadlam_csubst a k n t : closed a -> deadlam n t -> deadlam n (csubst a k t).
  Proof.
    intros cl. induction n in k, t |- *; cbn.
    - intros (na & d & ->). cbn. exists na, (csubst a k d). f_equal.
      exact (csubst_lift0 a 1 k d cl).
    - intros (na & b & -> & H). cbn. eexists _, _; split; [reflexivity|]. now apply IHn.
  Qed.

  Lemma deadlam_substl s n t : forallb (closedn 0) s -> deadlam n t -> deadlam n (substl s t).
  Proof.
    unfold substl. induction s in t |- *; cbn; auto.
    move/andP => [cl cls] H. apply IHs; auto. now apply deadlam_csubst.
  Qed.

  Lemma param_dead_csubst a k mf idx i :
    closed a -> param_dead mf idx i -> param_dead (map (map_def (csubst a k)) mf) idx i.
  Proof.
    intros cl (d & E & H). exists (map_def (csubst a k) d). split.
    - now rewrite nth_error_map E.
    - cbn. now apply deadlam_csubst.
  Qed.

  Lemma eta_args_impl (dead dead' : nat -> Prop) j xs args :
    (forall i, dead i -> dead' i) -> eta_args dead j xs args -> eta_args dead' j xs args.
  Proof. intros Hd. induction 1; constructor; auto. Qed.

  Lemma eta_args_length dead j xs args : eta_args dead j xs args -> #|args| = #|xs|.
  Proof. induction 1; cbn; congruence. Qed.

  Lemma eta_args_closed
 dead j xs args :
    eta_args dead j xs args -> forallb (closedn #|xs|) args.
  Proof.
    induction 1; cbn; auto.
    - apply/andP; split; [apply Nat.ltb_lt; lia|].
      solve_all. eapply closed_upwards; tea. lia.
    - solve_all. eapply closed_upwards; tea. lia.
  Qed.

  Lemma eta_args_csubst dead j xs args a k :
    eta_args dead j xs args -> map (csubst a (#|xs| + k)) args = args.
  Proof.
    intros H%eta_args_closed. rewrite -{2}(map_id args). apply map_ext_in.
    intros x Hx. apply csubst_closed.
    eapply closed_upwards; [exact (proj1 (forallb_forall _ _) H x Hx)|lia].
  Qed.

  Lemma closedn_eta dead j x xs F cs args k :
    eta_args dead j (x :: xs) args -> closedn k (mkApps F cs) ->
    closedn k (tLambda x (mk_lambdas xs (mkApps F (cs ++ args)))).
  Proof.
    intros H%eta_args_closed. rewrite closedn_mkApps. move/andP => [cF ccs].
    cbn. rewrite closedn_mk_lambdas closedn_mkApps forallb_app. cbn in H.
    apply/andP; split; [eapply closed_upwards; tea; lia|].
    apply/andP; split; solve_all; eapply closed_upwards; tea; lia.
  Qed.

  Lemma csubst_eta_closed dead j x xs F cs args a k :
    eta_args dead j (x :: xs) args -> closed (mkApps F cs) ->
    csubst a k (tLambda x (mk_lambdas xs (mkApps F (cs ++ args)))) =
    tLambda x (mk_lambdas xs (mkApps F (cs ++ args))).
  Proof.
    intros H cl. apply csubst_closed. eapply closedn_eta; tea.
    eapply closed_upwards; tea. lia.
  Qed.

  Lemma csubst_fix_eta dead x xs mf idx args a k :
    closed a -> eta_args dead 0 (x :: xs) args ->
    csubst a k (tLambda x (mk_lambdas xs (mkApps (lift0 (S #|xs|) (tFix mf idx)) args))) =
    tLambda x (mk_lambdas xs
      (mkApps (lift0 (S #|xs|) (tFix (map (map_def (csubst a (#|mf| + k))) mf) idx)) args)).
  Proof.
    intros cl H. cbn [csubst]. rewrite csubst_mk_lambdas csubst_mkApps.
    have E := eta_args_csubst _ _ _ _ a k H. cbn [length] in E.
    replace (#|xs| + S k) with (S #|xs| + k) by lia.
    rewrite E csubst_lift0 //.
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
    - (* fix_eta *)
      rewrite closedn_mk_lambdas closedn_mkApps in H4. move/andP: H4 => [cF _].
      replace (#|xs| + S k) with (k + S #|xs|) in cF by lia.
      apply closedn_lift0_inv in cF. subst F. cbn in cF.

      rewrite -(Rdefs_length _ _ H0). auto.
    - (* dead argument *)
      apply/andP; split; eapply closed_upwards; tea; lia.
  Qed.

  Lemma R_closed t t' k : R t t' -> closedn k t -> closedn k t'.
  Proof. intros H. exact (proj1 R_closed_mut _ _ H k). Qed.

  Lemma Rs_closed l l' k : Rs l l' -> forallb (closedn k) l -> forallb (closedn k) l'.
  Proof. intros H. exact (proj1 (proj2 (proj2 R_closed_mut)) _ _ H k). Qed.

  (** *** Substitution *)

  Lemma R_csubst_mut a a' : R a a' -> closed a -> closed a' ->
    (forall t t', R t t' -> forall k, R (csubst a k t) (csubst a' k t')) /\
    (forall t t', Rh t t' -> forall k, R (csubst a k t) (csubst a' k t')) /\
    (forall l l', Rs l l' -> forall k, Rs (map (csubst a k) l) (map (csubst a' k) l')) /\
    (forall l l', Rbrs l l' -> forall k,
      Rbrs (map (fun br => (br.1, csubst a (#|br.1| + k) br.2)) l)
           (map (fun br => (br.1, csubst a' (#|br.1| + k) br.2)) l')) /\
    (forall l l', Rdefs l l' -> forall k,
      Rdefs (map (map_def (csubst a k)) l) (map (map_def (csubst a' k)) l')).
  Proof.
    intros Ha cl cla. apply R_mutind; intros; cbn; auto.
    all: try (constructor; eauto; fail).
    all: try (apply R_head; constructor; eauto; fail).
    - (* cofix expansion *)
      rewrite (csubst_closed a' k (mkApps _ _)); [eapply closed_upwards; tea; lia|].
      specialize (H0 k). rewrite (csubst_closed a' k v0) in H0; [eapply closed_upwards; tea; lia|].
      rewrite csubst_cval in H0. rewrite csubst_cval.
      eapply R_cofix; eauto. now rewrite length_map.
    - (* evaluation *)
      rewrite (csubst_closed a' k t'); [eapply closed_upwards; tea; lia|].
      specialize (H0 k). rewrite (csubst_closed a' k v0) in H0; [eapply closed_upwards; tea; lia|].
      eapply R_eval; eauto.
    - (* head expansion *)
      rewrite (csubst_closed a' k (mk_lambdas ys t')); [eapply closed_upwards; tea; lia|].
      specialize (H0 k).
      rewrite (csubst_closed a' k (mk_lambdas ys u)) in H0; [eapply closed_upwards; tea; lia|].
      eapply R_exp; eauto.
    - (* partially applied fixpoint *)
      change (R (csubst a k (tLambda x (mk_lambdas xs (mkApps (tFix mf idx) (cs ++ args)))))
                (csubst a' k w)).
      rewrite (csubst_closed a' k w); [eapply closed_upwards; tea; lia|].
      erewrite csubst_eta_closed; tea. eapply R_fix_part; tea.
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
    - (* fix_eta *)
      subst F.
      change (R (csubst a k (tLambda x (mk_lambdas xs (mkApps (lift0 (S #|xs|) (tFix mf idx)) args))))
                (tFix (map (map_def (csubst a' (#|mf'| + k))) mf') idx)).
      erewrite csubst_fix_eta; tea. apply R_head. eapply Rh_fix_eta; [reflexivity| | |].
      + rewrite -(Rdefs_length _ _ H0). apply H1.
      + unfold fix_arity_ok in *. rewrite nth_error_map.
        destruct nth_error; cbn [option_map]; auto.
        exact (has_lambdas_csubst _ _ (S #|xs|) _ H2).

      + eapply eta_args_impl; [|tea]. intros i. now apply param_dead_csubst.
    - (* dead argument *)
      rewrite !csubst_closed; try (eapply closed_upwards; tea; lia).
      apply R_head, Rh_app_dead; auto.
  Qed.

  Lemma R_csubst a a' t t' k :
    R a a' -> closed a -> closed a' -> R t t' -> R (csubst a k t) (csubst a' k t').
  Proof. intros Ha cl cla H. exact (proj1 (R_csubst_mut a a' Ha cl cla) _ _ H k). Qed.

  Lemma R_substl s s' t t' :
    Rs s s' -> forallb (closedn 0) s -> forallb (closedn 0) s' -> R t t' ->
    R (substl s t) (substl s' t').
  Proof.
    unfold substl. intros H. induction H in t, t' |- *; cbn; auto.
    move/andP => [cl0 cls0] /andP [cl cls] Ht. apply IHRs; auto. now apply R_csubst.
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
    Rdefs mf mf' -> closed (tFix mf idx) -> closed (tFix mf' idx) ->
    cunfold_fix mf idx = Some (narg, fn) ->
    exists fn', cunfold_fix mf' idx = Some (narg, fn') /\ R fn fn'.
  Proof.
    intros H cl0 cl. unfold cunfold_fix. destruct nth_error eqn:E; [|discriminate].
    intros [= <- <-].
    destruct (Rdefs_nth_error _ _ _ _ H E) as (d' & -> & Hr & Hb).
    eexists; split; [now rewrite Hr|]. apply R_substl; auto.
    - now apply R_fix_subst.
    - eapply closed_fix_subst'; tea.
    - eapply closed_fix_subst'; tea.
  Qed.

  Lemma R_cunfold_cofix mf mf' idx narg fn :
    Rdefs mf mf' -> closed (tCoFix mf idx) -> closed (tCoFix mf' idx) ->
    cunfold_cofix mf idx = Some (narg, fn) ->
    exists fn', cunfold_cofix mf' idx = Some (narg, fn') /\ R fn fn'.
  Proof.
    intros H cl0 cl. unfold cunfold_cofix. destruct nth_error eqn:E; [|discriminate].
    intros [= <- <-].
    destruct (Rdefs_nth_error _ _ _ _ H E) as (d' & -> & Hr & Hb).
    eexists; split; [now rewrite Hr|]. apply R_substl; auto.
    - now apply R_cofix_subst.
    - eapply closed_cofix_subst'; tea.
    - eapply closed_cofix_subst'; tea.
  Qed.

  Lemma R_iota_red pars args args' br br' :
    Rs args args' -> forallb (closedn 0) args -> forallb (closedn 0) args' -> R br.2 br'.2 ->
    R (iota_red pars args br) (iota_red pars args' br').
  Proof.
    intros Ha cl0 cl Hb. unfold iota_red. apply R_substl; auto.
    - now apply Rs_rev, Rs_skipn.
    - rewrite forallb_rev. now apply forallb_skipn.
    - rewrite forallb_rev. now apply forallb_skipn.
  Qed.


End Rel.

Arguments cval : simpl never.

(** [E : t = t'] where the heads of the two applications differ. *)
Ltac head_contra E :=
  exfalso; apply (f_equal head) in E; rewrite ?head_cval ?head_mkApps in E; cbn in E;
  discriminate E.

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

  Lemma value_app_head f a : value Σ (tApp f a) -> value Σ f.
  Proof.
    intros H. remember (tApp f a) as t eqn:E.
    destruct H as [? X|? ? ? ? ? ? ? ? ? ?|f0 args vh nn al].
    - exfalso. destruct X as [? i|?]; subst; [cbn in i|]; discriminate.
    - discriminate.
    - destruct (exists_last nn) as (l & x & ->). rewrite mkApps_app in E. cbn in E.
      injection E as <- <-. apply All_app in al as [al _].
      rewrite length_app in vh. cbn in vh.
      destruct l as [|y l].
      + cbn. destruct vh.
        * constructor. constructor. unfold atom. now rewrite e e0.
        * now do 2 constructor.
        * rewrite Hguard in y. destruct y.
      + eapply value_app_nonnil; auto; [|discriminate].
        destruct vh.
        * eapply value_head_cstr; tea. lia.
        * constructor.
        * rewrite Hguard in y0. destruct y0.
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

  (** *** Applications: pushing an argument into a let or a case *)

  Lemma eval_lambda_inv na b v : eval Σ (tLambda na b) v -> v = tLambda na b.
  Proof. intros ev. exact (eval_deterministic ev (eval_atom Σ (tLambda na b) eq_refl)). Qed.

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
            | solve [eapply eval_fix'; fin] | solve [eapply eval_construct; fin]
            | solve [eapply eval_app_cong; fin] ].
  Qed.

  Lemma eval_app_value x fv a r :
    eval Σ x fv -> eval Σ (tApp fv a) r -> eval Σ (tApp x a) r.
  Proof.
    intros ex ev. have vf := eval_to_value _ _ ex.
    depelim ev; try flag_contra.
    all: match goal with vf : value _ ?F, H : eval Σ ?F ?y |- _ =>
           eapply eval_value in H; [|exact vf]; subst end.
    all: first [ solve [eapply eval_box; eassumption] | solve [eapply eval_beta; eassumption]
               | solve [eapply eval_fix'; eassumption] | solve [eapply eval_construct; eassumption]
               | solve [eapply eval_app_cong; eassumption] ].
  Qed.

  (** Without constructors as blocks, a constructor carrying arguments is stuck. *)
  Lemma eval_mkApps_Construct_nonblock ind c args0 args1 res :
    with_constructor_as_block = false ->
    eval Σ (mkApps (tConstruct ind c args0) args1) res -> args0 = [].
  Proof.
    intros Hb. revert res. induction args1 using rev_ind; intros res ev.
    - cbn in ev. depelim ev; try flag_contra.
      destruct args0; [reflexivity|]. cbn in i. discriminate.
    - rewrite mkApps_app in ev. cbn in ev. apply eval_app_inv in ev as (fv & ef & _). eauto.
  Qed.

  (** *** Identity cases evaluate to their scrutinee *)

  Lemma case_id_iota ind c br args res :
    rebuilds ind c br -> #|args| = #|br.1| -> forallb (closedn 0) args ->
    value Σ (cval ind c args) ->
    eval Σ (iota_red 0 args br) res -> res = cval ind c args.
  Proof.
    intros Hr Hn cl V.
    destruct (rebuild_iota _ _ _ _ Hr Hn cl) as (args0 & args1 & -> & E). intros ev.
    destruct with_constructor_as_block eqn:Hb.
    - destruct (eval_mkApps_Construct_block_inv _ _ _ _ _ _ Hb ev) as (args' & -> & _ & _).
      cbn in ev. rewrite app_nil_r in E. subst.
      rewrite (cval_block _ _ _ Hb) in V. rewrite (cval_block _ _ _ Hb).
      symmetry. eapply eval_value; tea.
    - have E0 := eval_mkApps_Construct_nonblock _ _ _ _ _ Hb ev. subst args0. cbn in E. subst args1.
      rewrite (cval_app _ _ _ Hb) in V. rewrite (cval_app _ _ _ Hb). symmetry. eapply eval_value; tea.
  Qed.

  Lemma case_id_result t v :
    eval Σ t v -> forall ind d brs, t = tCase (ind, 0) d brs -> closed d ->
    all_rebuild ind brs -> exists c args, v = cval ind c args /\ cfull Σ ind c #|args|.
  Proof.
    induction 1; intros ind0 d0 brs0 E cl Hb; try discriminate.
    all: try (exfalso; unfold is_true in *; congruence).
    1-2: injection E; intros; subst;
      match goal with H : eval Σ ?d _ |- _ =>
        have clv := eval_closed Σ HclΣ _ _ cl H; have vv := eval_to_value _ _ H end;
      match goal with H : #|skipn 0 _| = _ |- _ => rewrite skipn_0 in H end;
      match goal with H : with_constructor_as_block = _ |- _ =>
        first [erewrite <- cval_block in clv by exact H; erewrite <- cval_block in vv by exact H
              |erewrite <- cval_app in clv by exact H; erewrite <- cval_app in vv by exact H] end;
      rewrite closedn_cval in clv;
      do 2 eexists; split; [eapply case_id_iota; tea; eapply all_rebuild_nth; tea|];
      eapply cfull_isprop; tea; reflexivity.
    - injection E; intros; subst.
      eapply IHeval2; [reflexivity| |tea].
      have clv := eval_closed Σ HclΣ _ _ cl H. rewrite closedn_mkApps in clv.
      move/andP: clv => [clf cla]. rewrite closedn_mkApps. apply/andP; split; auto.
      eapply closed_cunfold_cofix; tea.
    - subst. cbn in i. discriminate.
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
    1-2: injection E as <- <- <-;
      first [ eapply eval_iota_block with (br := (br.1, tApp br.2 (lift0 #|br.1| a)));
              [eassumption|..]
            | eapply eval_iota with (br := (br.1, tApp br.2 (lift0 #|br.1| a)));
              [eassumption|..] ]; tea;
      [ unfold push_arg; rewrite nth_error_map;
        match goal with H : nth_error _ _ = Some _ |- _ => now rewrite H end
      | unfold iota_red; cbn; rewrite substl_tApp;
        rewrite (lift_closed _ 0 a) // (substl_closed _ a) //;
        eapply eval_app_value; eassumption ].
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

  (** *** Applications of lambdas and fixpoints; functions ignoring an argument *)

  Lemma eval_app_lambda_inv f a r na b :
    eval Σ (tApp f a) r -> eval Σ f (tLambda na b) ->
    ∑ av, eval Σ a av × eval Σ (csubst av 0 b) r.
  Proof.
    intros ev ef. depelim ev; try flag_contra.
    all: match goal with H : eval Σ _ _ |- _ =>
           tryif constr_eq H ef then fail else have E := eval_deterministic H ef end.
    all: try discriminate E.
    all: try (head_contra E).
    - injection E as -> ->. eexists; split; eassumption.
    - subst. cbn in *. discriminate.
  Qed.

  Lemma eval_app_fix_inv f a r mf idx :
    eval Σ (tApp f a) r -> eval Σ f (tFix mf idx) ->
    ∑ av narg fn, eval Σ a av × (cunfold_fix mf idx = Some (narg, fn)) × eval Σ (tApp fn av) r.
  Proof.
    intros ev ef. depelim ev; try flag_contra.
    all: match goal with H : eval Σ _ _ |- _ =>
           tryif constr_eq H ef then fail else have E := eval_deterministic H ef end.
    all: try discriminate E.
    all: try (head_contra E).
    - injection E as -> ->. eexists _, _, _; repeat split; eassumption.
    - subst. rewrite Hguard in i. cbn in i. discriminate.
  Qed.

  Lemma eval_app_arg f a av r :
    eval Σ a av -> eval Σ (tApp f av) r -> eval Σ (tApp f a) r.
  Proof.
    intros ea ev. have vav := eval_to_value _ _ ea.
    depelim ev; try flag_contra.
    all: try match type of vav with value _ ?v0 =>
           match goal with H : eval Σ v0 ?x |- _ =>
             have E := eval_value _ _ vav H; subst x end end.
    - eapply eval_box; tea.
    - eapply eval_beta; tea.
    - eapply eval_fix'; tea.
    - eapply eval_construct; tea.
    - eapply eval_app_cong; tea.
  Qed.

  Lemma deadlam_lambda n t : deadlam n t -> exists na b, t = tLambda na b.
  Proof. destruct n; cbn; [intros (na & d & ->)|intros (na & b & -> & _)]; eauto. Qed.

  Lemma eval_dead_spine cs : forall h fv,
    closed (mkApps h cs) -> eval Σ (mkApps h cs) fv ->
    (forall hv, eval Σ h hv -> deadlam #|cs| hv) -> deadlam 0 fv.
  Proof.
    induction cs as [|c cs IH]; cbn [mkApps length]; intros h fv cl ev Hh.
    - now apply Hh.
    - eapply IH; tea. intros hv' ev'.
      rewrite closedn_mkApps in cl. move/andP: cl => [cl _].
      change (is_true (closedn 0 h && closedn 0 c)) in cl. move/andP: cl => [ch cc].
      destruct (eval_app_inv _ _ _ ev') as (hv & eh & ev2).
      destruct (Hh _ eh) as (na & b & -> & D).
      destruct (eval_app_lambda_inv _ _ _ _ _ ev' eh) as (av & ea & eb).
      have cav := eval_closed Σ HclΣ _ _ cc ea.
      have D' := deadlam_csubst av 0 _ _ cav D.
      destruct (deadlam_lambda _ _ D') as (na' & b' & E). rewrite E in eb.
      apply eval_lambda_inv in eb. subst hv'. rewrite -E. exact D'.
  Qed.

  (** A function that ignores its next argument evaluates to a lambda whose
      body does not mention its variable, or is such a fixpoint. *)
  Lemma dead_head_eval f fv :
    closed f -> dead_head f -> eval Σ f fv ->
    deadlam 0 fv \/ (exists mf idx, f = tFix mf idx /\ fv = tFix mf idx /\ param_dead mf idx 0).
  Proof.
    intros cl [D|(mf & idx & cs & -> & P)] ev.
    - left. destruct D as (na & d & ->). apply eval_lambda_inv in ev. subst. now eexists _, _.
    - destruct cs as [|c cs].
      + right. cbn in *. have E := eval_deterministic ev (eval_atom Σ (tFix mf idx) eq_refl).
        subst. eauto.
      + left. cbn [mkApps] in *. eapply (eval_dead_spine cs (tApp (tFix mf idx) c)); tea.
        intros hv ev'.
        rewrite closedn_mkApps in cl. move/andP: cl => [cl _].
        change (is_true (closedn 0 (tFix mf idx) && closedn 0 c)) in cl.
        move/andP: cl => [cf cc].
        destruct (eval_app_fix_inv _ _ _ _ _ ev' (eval_atom Σ (tFix mf idx) eq_refl))
          as (av & narg & fn & ea & Hc & ef).
        destruct P as (d & Hd & D). change (deadlam (S #|cs|) (dbody d)) in D.
        unfold cunfold_fix in Hc. rewrite Hd in Hc. injection Hc as <- <-.
        have D1 := deadlam_substl (fix_subst mf) _ _ (closed_fix_subst' mf idx cf) D.
        destruct D1 as (na & b & E & D1). rewrite E in ef.
        destruct (eval_app_lambda_inv _ _ _ _ _ ef (eval_atom Σ (tLambda na b) eq_refl))
          as (av' & ea' & eb).
        have cav := eval_closed Σ HclΣ _ _ cc ea.
        have cav' := eval_closed Σ HclΣ _ _ cav ea'.
        have D' := deadlam_csubst av' 0 _ _ cav' D1.
        destruct (deadlam_lambda _ _ D') as (na' & b' & E'). rewrite E' in eb.
        apply eval_lambda_inv in eb. subst hv. rewrite -E'. exact D'.
  Qed.

End Flags.
