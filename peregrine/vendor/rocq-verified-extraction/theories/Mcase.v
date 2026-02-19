From Stdlib Require Import List Lia.
Export ListNotations.

From MetaRocq.Utils Require Import bytestring All_Forall MRList ReflectEq.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq Require Import EWcbvEvalNamed.
From Malfunction Require Import utils_array SemanticsSpec.

From Malfunction Require Import Malfunction Compile.
Open Scope list_scope.

Definition Func_ `{H : Heap} nms locals b v :=
  match nms with
  | n :: nms => Func (locals, n, Mlambda_ (nms, b))
  | nil => v
  end.

Fixpoint Mnapply (l : t) (args : list t) :=
  match args with
    [] => l
  | a :: args => Mnapply (Mapply_ (l, [a])) args
  end.

Lemma Mnapply_app l args1 args2 :
  Mnapply l (args1 ++ args2) = Mnapply (Mnapply l args1) args2.
Proof.
  induction args1 in l, args2 |- *; cbn.
  - reflexivity.
  - now rewrite IHargs1.
Qed. 

Arguments SemanticsSpec.eval {_ _}.

Lemma eval_app_nested_ `{Heap} globals locals args l args' v h h' :
  SemanticsSpec.eval globals locals h (Mnapply l (args' ++ args)) h' v ->
  SemanticsSpec.eval globals locals h (Mapply_ (Mnapply l args', args)) h' v.
Proof.
  rename H into HP. rename H0 into HH. induction args in args' |- *.
  - cbn. now rewrite app_nil_r.
  - cbn. intros H. specialize (IHargs (args' ++ [a])%list). destruct args.
    + now rewrite Mnapply_app in H.
    + econstructor. cbn in *.
      rewrite !Mnapply_app in IHargs.
      eapply IHargs. rewrite Mnapply_app in H. cbn in H.
      cbn. eauto.
Qed.

Lemma eval_app_nested_inv `{Heap} globals locals args l args' v h h' :
  SemanticsSpec.eval globals locals h (Mapply_ (Mnapply l args', args)) h' v ->
  SemanticsSpec.eval globals locals h (Mnapply l (args' ++ args)) h' v.
Proof.
  rename H into HP. rename H0 into HH. induction args in args' |- *.
  - cbn. now rewrite app_nil_r.
  - cbn. intros H. specialize (IHargs (args' ++ [a])%list). destruct args.
    + rewrite Mnapply_app. cbn. eauto.
    + cbn in *. rewrite <- app_assoc in *. cbn in IHargs.
      eapply IHargs.
      inversion H; subst.
      rewrite Mnapply_app. eauto.
Qed.

From Stdlib Require Import FunctionalExtensionality.

Definition add_multiple `{Heap} nms values locals := fold_right (fun '(a,b) l => @Ident.Map.add value a b l) locals (map2 pair nms values).

Lemma add_to_add_multiple `{Heap} nm y nms' values' locals :
  NoDup (nm :: nms') ->
  #|nms'| = #|values'| ->
  Ident.Map.add nm y (add_multiple nms' values' locals) =
  add_multiple (nms' ++ [nm]) (values' ++ [y]) locals.
Proof.
  rename H into HP; rename H0 into HH. 
  intros H Hlen. induction nms' in values', H, Hlen, nm, y |- *.
  - destruct values'; cbn in Hlen; try lia. reflexivity.
  - destruct values'; cbn in Hlen; try lia.
    cbn.
    fold (add_multiple (nms') (values') locals).
    fold (add_multiple (nms' ++ [nm]) (values' ++ [y]) locals).
    rewrite <- IHnms'.
    3: lia. 2:{ inversion H; subst. econstructor. cbn in *. eauto. inversion H3; eauto. }
    inversion H; subst. inversion H3; subst.
    assert (nm <> a). { intros ?. subst. cbn in *. eauto. }
    eapply functional_extensionality. intros x.
    unfold Ident.Map.add, Ident.eqb.
    destruct (eqb_spec x nm), (eqb_spec x a); subst; congruence.
Qed. 

Lemma NoDup_app {X} (l1 l2 : list X) :
  NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2.
Proof.
  induction l1; inversion 1; subst; split; try econstructor; firstorder.
  rewrite in_app_iff in *; firstorder subst.
Qed.

Lemma eval_app_ `{Heap} globals locals args values values' nms' nms b v l h :
  #|args| = #|nms| -> 
  #|nms'| = #|values'| ->
  NoDup (nms' ++ nms) ->
  Forall2 (fun e v => eval globals locals h e h v) args values ->
  eval globals (add_multiple (nms' ++ nms) (values' ++ values) locals) h b h v ->
  eval globals locals h l h (Func_ nms (add_multiple nms' values' locals) b v) ->
  eval globals locals h (Mapply_ (l, args)) h v.
Proof.
  rename H into HP; rename H0 into HH. 
  intros Hlen Hlenv Hdup H Heval Hl.
  eapply (eval_app_nested_ globals locals args l []). cbn.
  induction args in H, b, nms, nms', Hlen, Heval, v, values, values', Hl, l, Hdup, Hlenv |- *.
  - cbn. destruct nms; cbn in *; try lia. eauto.
  - destruct nms as [ | nm nms]; cbn in Hlen. 1: lia.
    inversion H. subst. rename H2 into Hx.
    destruct args.
    + destruct nms; cbn in Hlen; try lia. inversion H4; subst. clear H4.
      cbn. econstructor; eauto.
      rewrite add_to_add_multiple; eauto.
      eapply NoDup_incl_NoDup; eauto. rewrite length_app; cbn; lia. intros ? ?; rewrite in_app_iff in *; firstorder.
    + destruct nms as [ | nm' nms]. cbn in *; lia.
      cbn. eapply IHargs with (nms' := nms' ++ [nm]) (values' := values' ++ [y]).
      5:{ rewrite <- !app_assoc. cbn. eapply Heval. }
      1: cbn; eauto. 1:{ rewrite !length_app; cbn; lia. } 1:{ rewrite <- !app_assoc. cbn. eauto. } eauto.
      econstructor; [ eauto.. | ].
      cbn. destruct nms; rewrite add_to_add_multiple.
      * econstructor.
      * assert (nms' ++ [nm; nm'] = (nms' ++ [nm]) ++ [nm']) as Eq by now rewrite <- !app_assoc.
        rewrite Eq in Hdup. eapply NoDup_app in Hdup as [Hdup _].
        eapply NoDup_incl_NoDup; eauto. rewrite !length_app; cbn; lia. intros ? ?; rewrite !in_app_iff in *; firstorder subst.
      * lia.
      * econstructor. cbn. lia.
      * assert (nms' ++ nm :: nm' :: t0 :: nms = (nms' ++ [nm]) ++ (nm' :: t0 :: nms)) as Eq by now rewrite <- !app_assoc.
        rewrite Eq in Hdup. eapply NoDup_app in Hdup as [Hdup _].
        eapply NoDup_incl_NoDup; eauto. rewrite !length_app; cbn; lia. intros ? ?; rewrite !in_app_iff in *; firstorder subst.
      * lia.
Qed.

Lemma eval_apply_lambda `{Heap} globals locals args nms b values v h : 
  #|args| = #|nms| -> 
  NoDup nms ->
  Forall2 (fun e v => eval globals locals h e h v) args values ->
  eval globals (add_multiple nms values locals) h b h v ->
  eval globals locals h (Mapply_ (Mlambda_ (nms, b), args)) h v.
Proof.
  rename H into HP; rename H0 into HH. intros.
  eapply eval_app_ with (nms' := []) (values' := []); eauto.
  destruct nms.
  - cbn. eauto.
  - cbn. destruct nms.
    + econstructor; firstorder.
    + econstructor. cbn. lia.
Qed.

From Stdlib Require Import ZArith.

Lemma eval_case_block `{Heap} globals locals discr i args brs nms br v h num_args  :
  eval globals locals h discr h (Block (int_of_nat (blocks_until i num_args), args)) ->
  nms <> [] ->
  #|num_args| < Z.to_nat Int63.wB ->
  #|args| < int_to_nat PArray.max_length ->
  nth_error num_args i = Some (length nms) ->
  nth_error brs i = Some (nms, br) -> 
  NoDup nms ->
  #|args| = #|nms| ->
  eval globals (add_multiple nms args locals) h br h v ->
  eval globals locals h (Mcase (num_args, discr, brs)) h v.
Proof.
  rename H into HP; rename H0 into HH. 
  intros Hdiscr Hnms Hln Hargs Hnum Hnth Hdup Hlen Hbr.
  eapply eval_switch with (e := Mapply_ (Mlambda_ (nms, br), mapi (fun i _ => Mfield (int_of_nat i, discr)) (nms))).
  - eauto.
  - clear - Hnth Hnms Hnum Hln.
    revert Hnms Hnth Hnum Hln.
    unfold mapi at 1.
    change num_args with ([] ++ num_args) at 2 3 4 5 6 7 8.
    assert (length (@nil nat) = 0) by reflexivity. revert H.
    generalize (@nil nat).
    change i with (0 + i) at 3.
    generalize 0 as n.
    intros n brs0 Hbrs0 Hnms Hnth Hnum Hln. induction brs as [ | [nms' br'] brs IH] in i, Hnth, Hnms, nms, br, n, brs0, Hbrs0, Hnum, Hln, num_args |- *.
    + destruct i; cbn in *; congruence.      
    + destruct num_args; cbn in *; try congruence.
      { clear Hln. now destruct i. }
      destruct i; cbn in Hnth.
      * inversion Hnth as [ ]. subst; clear Hnth. cbn.
        rewrite nth_error_app2; try lia. cbn.
        rewrite Nat.sub_diag. cbn.
        destruct n0; cbn in *; try congruence.
        destruct nms; cbn in *; try congruence.
        cbn. rewrite Bool.orb_false_r. now rewrite <- plus_n_O, Int63.eqb_refl.
      * cbn [mapi_rec]. unfold find_match. cbn. fold find_match.
        destruct existsb eqn:E.
        2:{ fold find_match. specialize IH with (i := i) (n := S n) (brs0 := brs0 ++ [n0]).
            replace (n + S i) with (S n + i) by lia.
            replace ((brs0 ++ n0 :: num_args)) with ((brs0 ++ [n0]) ++ num_args).
            etransitivity. eapply IH. 
            -- rewrite length_app. cbn. lia.
            -- eauto.
            -- eauto.
            -- eauto.
            -- revert Hln. now rewrite <- !app_assoc.
            -- reflexivity.
            -- now rewrite <- !app_assoc.
        } exfalso.
        revert E. subst. rewrite nth_error_app2; try lia. cbn.
        rewrite Nat.sub_diag. cbn.
        destruct n0; cbn in *; try congruence.
        cbn. rewrite Bool.orb_false_r. unfold blocks_until. cbn.
        rewrite firstn_app_left. 2: eauto.
        rewrite firstn_app. cbn.
        rewrite firstn_ge. 2: lia. 
        replace (#|brs0| + S i - #|brs0|) with (S i) by lia.
        cbn. rewrite !filter_app. cbn. rewrite length_app. 
        intros E. eapply Uint63.eqb_correct in E.
        eapply (f_equal int_to_nat) in E.
        rewrite !int_to_of_nat in E. cbn in *. lia.
        cbn.
        revert Hln. rewrite length_app. cbn.
        pose proof (filter_length brs0 (fun x : nat => match x with
        | 0%nat => false
        | S _ => true
        end)).
        pose proof (filter_length (firstn i num_args) (fun x : nat => match x with
        | 0%nat => false
        | S _ => true
        end)).
        rewrite length_firstn in H0.
        lia.
        revert Hln. rewrite length_app. cbn.
        pose proof (filter_length brs0 (fun x : nat => match x with
        | 0%nat => false
        | S _ => true
        end)). lia. 
  - eapply eval_apply_lambda. 2: eassumption. 3: eassumption. 1: now rewrite mapi_length.
    revert Hargs.
    unfold mapi. change 0 with (#|@nil value|).
    revert Hdiscr. change args with ([] ++ args) at 1 2. generalize (@nil value) as args'. 
    intros args' Hdiscr Hargs.
    induction args in Hargs, nms, Hlen, Hdup, Hdiscr, args' |- *.
    + destruct nms; inversion Hlen. cbn. econstructor.
    + destruct nms; inversion Hlen. cbn. econstructor.
      2: specialize IHargs with (args' := args' ++ [a]).
      2: rewrite !length_app in IHargs. 2: cbn in IHargs.
      2: replace (S #|args'|) with (#|args'| + 1) by lia_max_length.
      2: eapply IHargs.
      * evar (v' : value).
        enough (a = v') as E. subst v'. rewrite E. econstructor.
        eapply Hdiscr.
        rewrite !length_app in *. lia_max_length.
        rewrite !length_app in *. rewrite int_to_of_nat; lia_max_length.
        subst v'. rewrite int_to_of_nat.     
        rewrite app_nth2, PeanoNat.Nat.sub_diag; [ reflexivity | lia_max_length].
        rewrite length_app in *. lia_max_length. 
      * now inversion Hdup.
      * assumption.
      * rewrite <- app_assoc. eapply Hdiscr.
      * rewrite !length_app in *. cbn in *. lia_max_length.
Qed.

Lemma Z_and_int n :
  (Z.of_nat n < Int63.wB)%Z ->
  Int63.to_Z (int_of_nat n) = Z.of_nat n.
Proof.
  intros H.
  unfold int_of_nat.
  rewrite Int63.of_Z_spec.
  rewrite Z.mod_small. 2:lia.
  reflexivity.
Qed.

Lemma eval_case_int `{Heap} globals locals discr i brs br v h  num_args :
  eval globals locals h discr h (value_Int (Int, Z_of_nat (nonblocks_until i num_args))) ->
  #|num_args| < Z.to_nat Int63.wB ->
  nth_error num_args i = Some 0 ->
  nth_error brs i = Some ([], br) -> 
  eval globals locals h br h v ->
  eval globals locals h (Mcase (num_args, discr, brs)) h v.
Proof.
  rename H into HP; rename H0 into HH. 
  intros Hdiscr Hln Hnum Hnth Hbr.
  eapply eval_switch with (e := br).
  - eauto.
  - clear - Hnth Hnum Hln.
    revert Hnth Hnum Hln.
    unfold mapi at 1.
    change num_args with ([] ++ num_args) at 2 3 4 5 6 7 8.
    assert (length (@nil nat) = 0) by reflexivity. revert H.
    generalize (@nil nat).
    change i with (0 + i) at 3.
    generalize 0 at 1 3 4 as n.
    intros n brs0 Hbrs0 Hnth Hnum Hln. induction brs as [ | [nms' br'] brs IH] in Hln, i, Hnth, br, n, brs0, Hbrs0, Hnum, num_args |- *.
    + destruct i; cbn in *; congruence.      
    + destruct num_args; cbn in *; try congruence.
      { clear Hln. now destruct i. }
      destruct i; cbn in Hnth.
      * inversion Hnth as [ ]. subst; clear Hnth. cbn.
        rewrite nth_error_app2; try lia.
        rewrite Nat.sub_diag. cbn. cbn in *. inversion Hnum. subst.
        cbn [existsb cond nth_error option_map fst].
        rewrite Bool.orb_false_r.
        rewrite andb_true_intro. reflexivity.
        split; rewrite Z_and_int; try rewrite <- plus_n_O; try lia.
        all: unfold nonblocks_until;
        rewrite firstn_app_left; eauto;
        pose proof (filter_length brs0 (fun x : nat => match x with
        | 0%nat => true
        | S _ => false
        end)); rewrite length_app in Hln; cbn in Hln; lia.
      * cbn [mapi_rec]. unfold find_match. cbn. fold find_match.
        destruct existsb eqn:E.
        2:{ fold find_match. specialize IH with (i := i) (n := S n) (brs0 := brs0 ++ [n0]).
            replace (n + S i) with (S n + i) by lia.
            replace ((brs0 ++ n0 :: num_args)) with ((brs0 ++ [n0]) ++ num_args).
            etransitivity. eapply IH. 
            -- rewrite length_app. cbn. lia.
            -- eauto.
            -- eauto.
            -- now rewrite <- !app_assoc.
            -- eauto.
            -- now rewrite <- !app_assoc.
        } exfalso.
        revert E. subst. rewrite nth_error_app2; try lia. cbn.
        rewrite Nat.sub_diag. cbn.
        destruct n0; cbn [existsb cond nth_error option_map fst]. 2: cbn; congruence.
        rewrite Bool.orb_false_r. rewrite Bool.andb_true_iff. intros [].
        eapply Zle_bool_imp_le in H0.
        revert H0. unfold nonblocks_until.
        setoid_rewrite firstn_app_left at 2. 2: eauto.
        rewrite firstn_app. cbn [app firstn].
        rewrite firstn_ge. 2: lia. 
        replace (#|brs0| + S i - #|brs0|) with (S i) by lia.
        cbn [app filter firstn]. rewrite !filter_app. cbn [firstn app]. rewrite length_app.
        cbn [filter length].
        rewrite Z_and_int. lia.
        pose proof (filter_length brs0 (fun x : nat => match x with
        | 0%nat => true
        | S _ => false
        end)).
        rewrite length_app in Hln. cbn in Hln. lia.
  - eauto.
Qed.
