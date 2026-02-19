From Stdlib Require Import ssreflect ssrbool Eqdep_dec.
From Equations Require Import Equations. 
From MetaRocq.Utils Require Import All_Forall MRPrelude MRSquash MRList utils.
From MetaRocq.Common Require Import Transform config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICFirstorder PCUICCasesHelper BDStrengthening PCUICCumulativity PCUICProgram.
From MetaRocq.Erasure Require Import EWcbvEval EWcbvEvalNamed.
From MetaRocq.ErasurePlugin Require Import Erasure ErasureCorrectness.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.

From Malfunction Require Import Malfunction Interpreter SemanticsSpec utils_array 
  Compile RealizabilitySemantics Pipeline PipelineCorrect.

From Stdlib Require Import ZArith Array.PArray List String Floats Lia Bool.
Import ListNotations.
From MetaRocq.Utils Require Import bytestring.

Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

Section firstorder.

  Context {Σb : list (kername * bool)}.

  Definition RocqType_to_camlType_oneind_type n k decl_type :
    is_true (@firstorder_type Σb n k decl_type) -> camlType.
  Proof.
    unfold firstorder_type. destruct (fst _).
    all: try solve [inversion 1].
    (* case of tRel with a valid index *)
    - intro; exact (Rel (n - S (n0-k))).  (* n0 - k *)  
    (* case of tInd where Σb is saying that inductive_mind is first order *)
    - intro; destruct ind. exact (Adt inductive_mind inductive_ind []).
  Defined.
  

  Fixpoint RocqType_to_camlType_ind_ctor n m cstr :
    is_true
    (alli
       (fun (k : nat) '{| decl_type := t |} =>
        @firstorder_type Σb m k t) n cstr) -> list camlType. 
  Proof. 
    destruct cstr; cbn; intros. 
    (* no more arguments *)
    * exact [].
    * apply andb_and in H. destruct H. destruct c.
    (* we convert the type of the first type of the constructor *)
      apply RocqType_to_camlType_oneind_type in H.
      refine (H :: _).
    (* we recursively convert *)
      exact (RocqType_to_camlType_ind_ctor _ _ _ H0).
  Defined. 

  Fixpoint RocqType_to_camlType_ind_ctors mind ind_ctors : 
    ind_params mind = [] -> 
    is_true (forallb (@firstorder_con Σb mind) ind_ctors) -> list (list camlType).
  Proof. 
    destruct ind_ctors; intros Hparam H.
    (* no more constructor *)
    - exact [].
    (* a :: ind_ctors constructors *)
    - cbn in H. apply andb_and in H. destruct H. 
      refine (_ :: RocqType_to_camlType_ind_ctors _ _ Hparam H0). clear H0.
      destruct c. unfold firstorder_con in H. cbn in H.
      eapply RocqType_to_camlType_ind_ctor; eauto.     
  Defined. 

  Definition RocqType_to_camlType_oneind mind ind : 
    ind_params mind = [] -> 
    is_true (@firstorder_oneind Σb mind ind) -> list (list camlType).
  Proof.
    destruct ind. intros Hparam H. apply andb_and in H.
    destruct H as [H _]. cbn in *. clear -H Hparam.
    eapply RocqType_to_camlType_ind_ctors; eauto. 
  Defined.

  Lemma bool_irr b (H H' : is_true b) : H = H'.
    destruct b; [| inversion H].
    assert (H = eq_refl).
    eapply (K_dec (fun H => H = eq_refl)); eauto.
    etransitivity; eauto. 
    eapply (K_dec (fun H => eq_refl = H)); eauto.
    Unshelve. all: cbn; eauto. 
    all: intros b b'; pose (Stdlib.Bool.Bool.bool_dec b b'); intuition. 
  Qed.

  Lemma RocqType_to_camlType_oneind_type_fo n k decl_type Hfo :
    let T := RocqType_to_camlType_oneind_type n k decl_type Hfo in
    is_true (negb (isArrow T)).
  Proof.
    unfold RocqType_to_camlType_oneind_type.
    unfold firstorder_type in Hfo.
    set (fst (PCUICAstUtils.decompose_app decl_type)) in *.
    destruct t; inversion Hfo; cbn; eauto. 
    now destruct ind.
  Qed.     

  Lemma RocqType_to_camlType_oneind_fo mind ind Hparam Hfo larg T : 
    In larg (RocqType_to_camlType_oneind mind ind Hparam Hfo) -> 
    In T larg -> is_true (negb (isArrow T)).
  Proof. 
    destruct mind, ind. revert Hfo. induction ind_ctors0; intros Hfo Hlarg HT.
    - cbn in *; destruct andb_and. destruct (a Hfo). destruct (in_nil Hlarg).
    - cbn in Hlarg. destruct andb_and. destruct (a0 Hfo). 
      destruct andb_and. destruct (a1 i0). destruct a.
      unfold In in Hlarg. destruct Hlarg.
      2: { eapply IHind_ctors0; eauto. cbn. destruct andb_and.
            destruct (a _). rewrite (bool_irr _ i6 i4). eauto.
            Unshelve.
            cbn. apply andb_and. split; cbn; eauto. }
      cbn in Hparam, i3. rewrite Hparam in i3, H. rewrite app_nil_r in i3, H.
      clear - i3 HT H. set (rev cstr_args0) in *. rewrite <- H in HT. revert T HT. clear H. 
      set (Datatypes.length ind_bodies0) in *. revert i3. generalize n 0. clear.
      induction l; cbn; intros; [inversion HT|].
      destruct andb_and. destruct (a0 i3). destruct a.
      unfold In in HT. destruct HT.
      + rewrite <- H; eapply RocqType_to_camlType_oneind_type_fo; eauto.
      + eapply IHl. eauto.
  Qed.    

  (* The following function morally do (map RocqType_to_camlType_oneind) while passing 
  the proof that everything is first order *)

  Fixpoint RocqType_to_camlType_fix ind_bodies0 
    ind_finite0 
    ind_params0 ind_npars0 ind_universes0 
    ind_variance0 {struct ind_bodies0}: 
  ind_params0 = [] -> 
  forall ind_bodies1 : list one_inductive_body,
  is_true
    (forallb
     (@firstorder_oneind Σb
        {|
          Erasure.P.PCUICEnvironment.ind_finite := ind_finite0;
          Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
          Erasure.P.PCUICEnvironment.ind_params := ind_params0;
          Erasure.P.PCUICEnvironment.ind_bodies := ind_bodies1;
          Erasure.P.PCUICEnvironment.ind_universes := ind_universes0;
          Erasure.P.PCUICEnvironment.ind_variance := ind_variance0
        |}) ind_bodies0) -> list (list (list camlType)).
  Proof.
    destruct ind_bodies0; cbn in *; intros.
    - exact [].
    - refine (RocqType_to_camlType_oneind _ _ _ _ :: RocqType_to_camlType_fix _ _ _ _ _ _ _ _ _); eauto. 
      2-3: unfold firstorder_oneind, firstorder_con; apply andb_and in H0; destruct H0; eauto.
      eauto.
  Defined.   

  Definition RocqType_to_camlType' mind : 
    ind_params mind = [] -> 
    is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind)) -> 
    list (list (list camlType)).
  Proof.
    intros Hparam. destruct mind; unshelve eapply RocqType_to_camlType_fix; eauto.
  Defined.

  Lemma RocqType_to_camlType'_fo mind Hparam Hfo lind larg T : 
    In lind (RocqType_to_camlType' mind Hparam Hfo) -> 
    In larg lind ->
    In T larg -> is_true (negb (isArrow T)).
  Proof.
    destruct mind. cbn in Hparam. unfold RocqType_to_camlType'. cbn in *.
    revert Hfo. 
    enough (forall ind_bodies1
    (Hfo : is_true
            (forallb
               (firstorder_oneind
                  {|
                    Erasure.P.PCUICEnvironment.ind_finite :=
                      ind_finite0;
                    Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
                    Erasure.P.PCUICEnvironment.ind_params :=
                      ind_params0;
                    Erasure.P.PCUICEnvironment.ind_bodies :=
                      ind_bodies1;
                    Erasure.P.PCUICEnvironment.ind_universes :=
                      ind_universes0;
                    Erasure.P.PCUICEnvironment.ind_variance :=
                      ind_variance0
                  |}) ind_bodies0)),
  In lind
    (RocqType_to_camlType_fix ind_bodies0 ind_finite0 ind_params0
       ind_npars0 ind_universes0 ind_variance0 Hparam ind_bodies1 Hfo) ->
  In larg lind -> In T larg -> is_true (negb (isArrow T))).
  eapply H; eauto. 
  induction ind_bodies0; cbn in * ; [now intros |].   
  intros bodies1 Hfo Hlind Hlarg HT. unfold In in Hlind. destruct Hlind.
    - rewrite <- H in Hlarg. eapply RocqType_to_camlType_oneind_fo; eauto.
    - eapply IHind_bodies0; eauto.
  Qed. 

  Lemma RocqType_to_camlType'_fo_alt T1 T2 Ts mind ind Hparam Hfo:
    In Ts
       (nth ind (RocqType_to_camlType'
           mind Hparam Hfo) []) -> ~ In (T1 → T2) Ts.
  Proof.
    intros H H0. 
    epose proof (RocqType_to_camlType'_fo _ _ _ _ _ _ _ _ H0).
    now cbn in H1. Unshelve. all:eauto.  
    case_eq (Nat.ltb ind (List.length (RocqType_to_camlType' mind
    Hparam Hfo))); intro Hleq.
    - apply nth_In. apply leb_complete in Hleq. lia. 
    - apply leb_complete_conv in Hleq. 
      assert (Datatypes.length (RocqType_to_camlType' mind Hparam Hfo) <= ind) by lia.
      pose proof (nth_overflow _ [] H1).
      rewrite H2 in H. destruct (in_nil H).
  Qed.  

  Lemma RocqType_to_camlType'_length mind Hparam Hfo :
    List.length (RocqType_to_camlType' mind Hparam Hfo) 
    = List.length (ind_bodies mind).
  Proof.
    destruct mind. cbn in *. revert Hfo.
    enough (forall ind_bodies1
      (Hfo : is_true
            (forallb
               (firstorder_oneind
                  {|
                    Erasure.P.PCUICEnvironment.ind_finite :=
                      ind_finite0;
                    Erasure.P.PCUICEnvironment.ind_npars :=
                      ind_npars0;
                    Erasure.P.PCUICEnvironment.ind_params :=
                      ind_params0;
                    Erasure.P.PCUICEnvironment.ind_bodies :=
                      ind_bodies1;
                    Erasure.P.PCUICEnvironment.ind_universes :=
                      ind_universes0;
                    Erasure.P.PCUICEnvironment.ind_variance :=
                      ind_variance0
                  |}) ind_bodies0)),
    #|RocqType_to_camlType_fix
        ind_bodies0 ind_finite0
        ind_params0 ind_npars0
        ind_universes0 ind_variance0
        Hparam ind_bodies1 Hfo| =
    #|ind_bodies0|); eauto.
    induction ind_bodies0; cbn; eauto.
    intros. f_equal. destruct andb_and.
    destruct (a0 Hfo). eauto. 
  Qed.      

  
  Lemma RocqType_to_camlType_oneind_length mind Hparam x Hfo:
  List.length
      (RocqType_to_camlType_oneind
            mind x Hparam Hfo) =
  List.length (ind_ctors x).
  Proof.
    destruct x; cbn. destruct andb_and.
    destruct (a Hfo). clear.
    induction ind_ctors0; cbn; eauto.
    destruct andb_and. destruct (a0 i0).
    destruct a. cbn. f_equal. eapply IHind_ctors0.
  Qed. 

  Lemma RocqType_to_camlType'_nth mind Hparam x Hfo Hfo' ind:
  nth_error (ind_bodies mind) ind = Some x -> 
  ind < Datatypes.length (ind_bodies mind) -> 
    nth ind
         (RocqType_to_camlType'
            mind
            Hparam
            Hfo) [] =
    RocqType_to_camlType_oneind mind x Hparam Hfo'.
  Proof.
    destruct mind. revert ind. cbn in *. revert Hfo Hfo'.
    enough (
    forall ind_bodies1 (Hfo : is_true
           (forallb
              (firstorder_oneind
              (Build_mutual_inductive_body
              ind_finite0 ind_npars0
              ind_params0 ind_bodies1
              ind_universes0 ind_variance0)) ind_bodies0))
  (Hfo' : is_true
            (firstorder_oneind
            (Build_mutual_inductive_body
            ind_finite0 ind_npars0
            ind_params0 ind_bodies1
            ind_universes0 ind_variance0) x)) (ind : nat),
nth_error ind_bodies0 ind = Some x ->
ind < Datatypes.length ind_bodies0 ->
nth ind
  (RocqType_to_camlType_fix ind_bodies0 ind_finite0
     ind_params0 ind_npars0 ind_universes0
     ind_variance0 Hparam ind_bodies1 Hfo) [] =
RocqType_to_camlType_oneind
(Build_mutual_inductive_body
ind_finite0 ind_npars0
ind_params0 ind_bodies1
ind_universes0 ind_variance0) x Hparam Hfo'); eauto.
    induction ind_bodies0; intros. cbn in *; lia.
    destruct ind; cbn.
    - destruct andb_and. destruct (a0 Hfo).  
      cbn in H. inversion H. subst. f_equal. clear. apply bool_irr.
    - eapply IHind_bodies0; eauto.
      cbn in *; lia.
  Qed.

  Lemma RocqType_to_camlType'_nth_length mind Hparam Hfo ind x:
    nth_error (ind_bodies mind) ind = Some x -> 
    List.length
        (nth ind
           (RocqType_to_camlType'
              mind
              Hparam
              Hfo) []) =
    List.length (ind_ctors x).
  Proof.
    intros; erewrite RocqType_to_camlType'_nth; eauto.
    eapply RocqType_to_camlType_oneind_length; eauto.
    eapply nth_error_Some_length; eauto.   
    Unshelve. eapply forallb_nth_error in Hfo.
      erewrite H in Hfo. exact Hfo.         
  Qed. 

  Definition RocqType_to_camlType mind : 
    ind_params mind = [] -> 
    is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind)) -> ADT :=
    fun Hparam H => (0, RocqType_to_camlType' mind Hparam H).
  
  Lemma RocqType_to_camlType_ind_ctors_nth 
    mind ind_ctors Hparam a k i :
    nth_error (RocqType_to_camlType_ind_ctors mind ind_ctors Hparam i) k
    = Some a ->
    exists a', nth_error ind_ctors k = Some a' /\
    exists i', 
    a = RocqType_to_camlType_ind_ctor 0 #|ind_bodies mind| (rev (cstr_args a' ++ ind_params mind)) i'.
  Proof. 
    revert a k i.
    induction ind_ctors; cbn; intros.
    - destruct k; inversion H.
    - destruct andb_and. destruct (a1 _).
      destruct k; destruct a.
      + inversion H. eexists; split; [reflexivity|].
        cbn. unfold firstorder_con in i. cbn in i.
        apply andb_and in i. destruct i as [i ?]. 
        exists i. repeat f_equal. apply bool_irr.
      + eapply IHind_ctors; eauto.
  Qed. 

  Lemma RocqType_to_camlType_ind_ctors_length 
  l n m i:
  List.length (RocqType_to_camlType_ind_ctor n m l i) = List.length l.
  revert n m i. induction l; cbn; eauto; intros. 
  destruct andb_and. destruct (a0 _). destruct a.
  cbn. now f_equal.
  Qed. 

  Lemma RocqType_to_camlType_ind_ctor_app
  l l' n m i : { i' & { i'' &  RocqType_to_camlType_ind_ctor n m (l++l') i = RocqType_to_camlType_ind_ctor n m l i' ++ RocqType_to_camlType_ind_ctor (#|l| + n) m l' i''}}.
  pose proof (ii := i). rewrite alli_app in ii. eapply andb_and in ii. destruct ii as [i' i''].
  exists i', i''. revert n i i' i''. induction l; cbn in *; intros.  
  - f_equal. eapply bool_irr.
  - destruct andb_and. destruct (a0 _). destruct a.      
    destruct andb_and. destruct (a _). rewrite <- app_comm_cons; repeat f_equal.
    * apply bool_irr.
    * assert (S (#|l| + n) = #|l| + S n) by lia. revert i''. rewrite H. apply IHl.
  Qed.      
  
  Lemma RocqType_to_camlType_oneind_nth_ctors mind Hparam x Hfo k l :
  nth_error (RocqType_to_camlType_oneind mind x Hparam Hfo) k = Some l ->
  exists i0, nth_error (RocqType_to_camlType_ind_ctors mind (ind_ctors x) Hparam i0) k = Some l.
  Proof.
  destruct x; cbn. destruct andb_and.
  destruct (a Hfo). now eexists.
  Qed. 

  Lemma RocqType_to_camlType_oneind_nth mind Hparam x Hfo k l :
  nth_error (RocqType_to_camlType_oneind mind x Hparam Hfo) k = Some l
  -> exists l', nth_error (ind_ctors x) k = Some l' /\ #|l| = #|cstr_args l'|.
  Proof.
  destruct x; cbn. destruct andb_and.
  destruct (a Hfo). clear.
  revert k l. induction ind_ctors0; cbn; eauto.
  - intros k l H. rewrite nth_error_nil in H. inversion H.
  - destruct andb_and. destruct (a0 i0).
      destruct a. intros k l H. destruct k; cbn. 
      + eexists; split; [reflexivity |]. cbn in *.
        inversion H. rewrite RocqType_to_camlType_ind_ctors_length.
        rewrite Hparam. rewrite app_nil_r. apply length_rev.
      + cbn in *. now eapply IHind_ctors0. 
  Qed. 

  Lemma RocqType_to_camlType_oneind_nth' mind Hparam x Hfo k l :
  nth_error (ind_ctors x) k = Some l 
  -> exists l', nth_error (RocqType_to_camlType_oneind mind x Hparam Hfo) k = Some l' /\ #|l'| = #|cstr_args l|.
  Proof.
    destruct x; cbn. destruct andb_and.
    destruct (a Hfo). clear.
    revert k l. induction ind_ctors0; cbn; eauto.
    - intros k l H. rewrite nth_error_nil in H. inversion H.
    - destruct andb_and. destruct (a0 i0).
      destruct a. intros k l H. destruct k; cbn. 
      + eexists; split; [reflexivity |]. cbn in *.
        inversion H. rewrite RocqType_to_camlType_ind_ctors_length.
        rewrite Hparam. rewrite app_nil_r. apply length_rev.
      + cbn in *. now eapply IHind_ctors0. 
  Qed. 


  #[local] Instance cf_ : checker_flags := extraction_checker_flags.
  #[local] Instance nf_ : PCUICSN.normalizing_flags := PCUICSN.extraction_normalizing.

  Parameter Normalisation : forall Σ0 : PCUICAst.PCUICEnvironment.global_env_ext, PCUICTyping.wf_ext Σ0 -> PCUICSN.NormalizationIn Σ0.

  Definition compile_pipeline `{Heap} (Σ:global_env_ext_map) t HΣ expΣ expt (typing : {T:term & ∥ Σ;;; [] |- t : T ∥})  := 
      (@compile_malfunction_pipeline _ _ Σ t (projT1 typing) HΣ expΣ expt (projT2 typing) Normalisation).2.
  
  Fixpoint wellformed_pure Σ Γ x :
    CompileCorrect.wellformed Σ Γ x -> isPure x
    with wellformed_binding_subset Σ Γ x :
    CompileCorrect.wellformed_binding Σ Γ x -> isPure_binding x.
  Proof.
    2: destruct x. destruct x.
    all: intros Hwf. 
    all: try solve [cbn in *; eauto].
    - cbn in *. destruct p; rtoProp; eauto. 
    - cbn in *. destruct p; rtoProp; split; eauto. clear H. 
      induction l; eauto. cbn in *. rtoProp. split; eauto.
    - cbn in *. destruct p; cbn in *; rtoProp; split; eauto. clear H H0. induction l; eauto.
      cbn in *. rtoProp. split; eauto.
    - cbn in *. destruct p; cbn in *; rtoProp; split; eauto. clear H. induction l; eauto.
      cbn in *. rtoProp. split; eauto. destruct a. eauto.  
    - cbn in *. destruct p; rtoProp; eauto. destruct p; eauto.  
    - cbn in *. destruct p; rtoProp; eauto. repeat destruct p; eauto. rtoProp. split; eauto.   
    - cbn in *. destruct p; rtoProp; eauto. repeat destruct p; eauto.
    - cbn in *. destruct p; rtoProp; eauto. clear H. induction l; eauto.  
      cbn in *. rtoProp. split; eauto.
    - cbn in *. destruct p; rtoProp; eauto.
    - cbn in *. destruct p; rtoProp; eauto.
    - cbn in *. revert Hwf. set (_ ++ _). clearbody l0. revert l0. induction l; eauto; intros. 
      destruct a; cbn in *. rtoProp. split; eauto.
  Qed. 

  Lemma compile_pure `{Heap} `{WcbvFlags} (Σ:global_env_ext_map) t HΣ expΣ expt typing :
    is_true (isPure (compile_pipeline Σ t HΣ expΣ expt typing)).
  Proof.
    eapply wellformed_pure, verified_malfunction_pipeline_wellformed. 
  Qed. 

  Lemma compile_value_pure `{Heap} (Σ:global_env_ext) (wf: PCUICTyping.wf_ext Σ) Σ' t
    (Hnparam : forall (i : kername) (mdecl : mutual_inductive_body),
    lookup_env Σ i = Some (InductiveDecl mdecl) ->
    ind_npars mdecl = 0):
    firstorder_value Σ [] t ->
    isPure_value (compile_value_mf' Σ Σ' t).
  Proof.
    revert t. eapply firstorder_value_inds. intros.
    cbn. unfold compile_value_mf'. rewrite compile_value_box_mkApps. cbn.
    unfold ErasureCorrectness.pcuic_lookup_inductive_pars, EGlobalEnv.lookup_constructor_pars_args.
    rewrite PCUICExpandLetsCorrectness.trans_lookup.  
    unshelve eapply PCUICInductiveInversion.Construct_Ind_ind_eq' in X; eauto. 
    repeat destruct X as [? X]. repeat destruct d as [d ?]. unfold declared_minductive in d.
    revert d; intro. cbn in d. unfold PCUICExpandLetsCorrectness.SE.lookup_env.  
    erewrite PCUICExpandLetsCorrectness.SE.lookup_global_Some_iff_In_NoDup in d.
    2: { eapply NoDup_on_global_decls. destruct wf as [wf ?]. destruct wf. eauto. } 
    rewrite d. cbn. erewrite Hnparam. 2: now rewrite <- d.
    rewrite skipn_0; destruct args; cbn.
    - destruct Compile.lookup_constructor_args; cbn; eauto.
    - destruct Compile.lookup_constructor_args; cbn; eauto.
      inversion H2; subst. econstructor; eauto. 
      repeat rewrite map_map. now rewrite Forall_map.
  Qed.

  Definition isFunction_named (v : EWcbvEvalNamed.value) := 
    match v with 
      EWcbvEvalNamed.vClos _ _ _ | EWcbvEvalNamed.vRecClos _ _ _ => true 
    | _ => false 
    end.

  Lemma isFunction_isfunction_named t v : ErasureCorrectness.isFunction t ->
    represents_value v (EImplementBox.implement_box t) ->
    isFunction_named v.
  Proof.
    intros H H'; destruct t; inversion H; inversion H'; eauto.
  Qed. 

  Lemma compile_function {P : Pointer} {HP : CompatiblePtr P P}  {HHeap : @Heap P} `{@CompatibleHeap P P _ _ _} `{WcbvFlags} 
    (cf:=config.extraction_checker_flags)
    (Σ:global_env_ext_map) h h' f v na A B HΣ expΣ 
    (Hax: Extract.axiom_free Σ)
    (Hheap_refl : forall h, R_heap h h)
    (wf : ∥ Σ ;;; [] |- f : tProd na A B ∥) expf :
    ∥Extract.nisErasable Σ [] f∥ ->
    forall p,
    let Σ_erase := (Transform.transform verified_named_erasure_pipeline (Σ, f) p).1 in
    forall Σ' (HΣ' : CompileCorrect.malfunction_env_prop Σ_erase Σ')
      (Hcons : forall (nm : Ident.t) (val val' : value),
      In (nm, val) Σ' -> In (nm, val') Σ' -> vrel val val') ,
      eval Σ' empty_locals h (compile_pipeline Σ f HΣ expΣ expf (_;wf)) h' v ->
    isFunction v = true.
  Proof.
    intros Hnerase ? ? ? ? ? Heval. pose Normalisation.
    unshelve epose proof (Hfunction := transform_erasure_pipeline_function' _ _ _ _ _).
    6: eauto. all: eauto.
    - destruct Hfunction as [v'[Heval' ?]]. 
      unshelve eapply (Transform.preservation post_verified_named_erasure_pipeline) in Heval' as [v'' [Heval' [? [? ?]]]].
      1: cbn; eauto.
      Opaque post_verified_named_erasure_pipeline verified_erasure_pipeline.
      destruct o as [? [? ?]]. destruct o as [? ?].
      unfold implement_box_transformation, Transform.obseq in o1.
      unfold name_annotation, Transform.obseq, Transform.run, time in o0.
      sq. subst.  
      unfold compile_pipeline, compile_malfunction_pipeline, verified_malfunction_pipeline in Heval.
      revert Heval; destruct_compose; intros. 
      unfold Transform.transform at 1 in Heval. cbn - [Transform.transform] in Heval.
      unfold verified_named_erasure_pipeline in Heval.
      revert Heval; destruct_compose; intros. 
      set (precond _ _ _ _ _ _ _ _) in Heval.
      pose proof (ProofIrrelevance.proof_irrelevance _ p0 p). subst.
      eapply CompileCorrect.compile_correct with (Σ' := Σ') (Γ' := empty_locals) (h:=h) in Heval'. 
      2: { intros. split; eapply assume_can_be_extracted; eauto. }
      2: { intros. eauto. }
      2: { intros. unfold verified_named_erasure_pipeline in Σ_erase. 
         revert Σ_erase HΣ'. destruct_compose; intros. eapply HΣ'. }
      destruct H4. 
      eapply eval_det in Heval' as [? ?]; try eapply Heval; eauto. 
      2: { econstructor. }
      clear Heval H2. eapply isFunction_isfunction_named in o0; eauto.
      destruct v''; cbn in H5; try inversion o0; inversion H5; eauto.
  Qed.

  Opaque compile_pipeline compile_malfunction_pipeline verified_named_erasure_pipeline. 

  Definition irred Σ Γ t := forall t', PCUICReduction.red1 Σ Γ t t' -> False.

  Lemma tConstruct_irred Σ Γ i n inst : irred Σ Γ (tConstruct i n inst).
  Proof. 
    inversion 1. clear - H. destruct args; [inversion H|cbn in H].
    revert H. generalize (tFix mfix idx) t. induction args; cbn; intros; eauto.
    inversion H.
  Qed.

  Lemma compile_pipeline_tConstruct_nil : forall `{Heap} 
    kn ind n inst mind univ retro univ_decl 
    (Σ0 := mk_global_env univ [(kn , InductiveDecl mind)] retro),
    let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl) in
    let i := mkInd kn ind in
    forall HΣ expΣ expt 
    (fo : firstorder_ind Σ (firstorder_env Σ) i)
    (Hnparam : forall (i : kername) (mdecl : mutual_inductive_body),
        lookup_env Σ i = Some (InductiveDecl mdecl) ->
        ind_npars mdecl = 0)
    (Hlookup : lookup_env Σ kn = Some (InductiveDecl mind))
    (wt : ∥ Σ;;; [] |-  tConstruct i n inst : mkApps (tInd i inst) [] ∥),
    let Σ_t := (Transform.transform verified_named_erasure_pipeline
    (Σ, tConstruct i n inst)
    (ErasureCorrectness.precond Σ (tConstruct i n inst)
       (mkApps (tInd i inst) []) HΣ expΣ expt wt Normalisation)).1 in
    forall Σ' (HΣ' : CompileCorrect.malfunction_env_prop Σ_t Σ')  
      (Hax : PCUICClassification.axiom_free Σ) h, 
    eval Σ' empty_locals h (compile_pipeline Σ (tConstruct i n inst) HΣ expΣ expt (existT _ _ wt))
    h match Compile.lookup_constructor_args Σ_t i with
    | Some num_args => let num_args_until_m := firstn n num_args in
                      let index := #| filter (fun x => match x with 0 => true | _ => false end) num_args_until_m| in
                      SemanticsSpec.value_Int (Malfunction.Int, BinInt.Z.of_nat index)
    | None => fail "inductive not found"
      end.
  Proof.
    intros.
    unshelve epose proof (Hthm := verified_malfunction_pipeline_theorem H H0 Σ Hax HΣ expΣ
    (tConstruct i n inst) expt (tConstruct i n inst) i inst [] wt fo Hnparam Normalisation _ _ _ Σ' HΣ' h);eauto.
    { eapply tConstruct_irred. }
    cbn in Hthm.
    unshelve epose proof (Hthm' := verified_named_erasure_pipeline_fo H H0 Σ HΣ expΣ
    (tConstruct i n inst) expt (tConstruct i n inst) i inst [] fo Normalisation wt _ Hax);eauto.
    eapply red_eval; eauto. eapply Normalisation.
    { eapply tConstruct_irred. }
    sq. cbn in Hthm'.
    unfold ErasureCorrectness.pcuic_lookup_inductive_pars, EGlobalEnv.lookup_constructor_pars_args in *. 
    rewrite PCUICExpandLetsCorrectness.trans_lookup in Hthm, Hthm'. cbn in Hthm, Hthm'.
    rewrite ReflectEq.eqb_refl in Hthm, Hthm'. cbn in Hthm, Hthm'. 
    erewrite Hnparam, skipn_0 in Hthm; [|eauto]. 
    inversion Hthm'; subst. clear Hthm'. 
    unfold EGlobalEnv.lookup_constructor_pars_args, Compile.lookup_constructor_args, 
      EGlobalEnv.lookup_constructor, EGlobalEnv.lookup_inductive, 
      EGlobalEnv.lookup_minductive in *. cbn in *. 
    set (EGlobalEnv.lookup_env _ _ ) in H3, Hthm.  
    case_eq o. 2: { intro X0. rewrite X0 in H3. inversion H3. }
    intros ? eq. rewrite eq in Hthm, H3. pose proof (eq':=eq).
    unfold o in eq'. eapply (verified_malfunction_pipeline_lookup  H H0 Σ HΣ expΣ
    (tConstruct i n inst) expt (tConstruct i n inst) i inst [] fo Normalisation wt _ Hax) in eq'.
    rewrite eq'; eauto.
  Qed.

  Fixpoint map_forall {A B} {P : A -> Type} (f : forall a:A, P a -> B ) (l:list A) (Hl: All P l) : list B := 
    match Hl with 
      All_nil => []
    | All_cons x l HP Hl => f x HP :: map_forall f l Hl
    end. 

  Definition isConstruct_ind t :=
  match fst (PCUICAstUtils.decompose_app t) with
  | tConstruct i _ _ => i
  | _ =>  mkInd (MPfile [],"") 0
  end.

  Lemma typing_tConstruct_fo Σ args :
    Forall (firstorder_value Σ []) args ->
    Forall (fun t => exists inst pandi, 
      ∥ Σ;;; [] |- t : mkApps (tInd (isConstruct_ind t) inst) pandi ∥) args.
  Proof.
    eapply Forall_impl. eapply firstorder_value_inds. intros.
    unfold isConstruct_ind. rewrite PCUICAstUtils.decompose_app_mkApps; eauto.
  Qed.  

  Lemma mkApps_irred Σ Γ t args :
    (irred Σ Γ t) ->
    (isLambda t -> False) ->
    (forall mfix idx args, t = mkApps (tFix mfix idx) args -> False) ->
    Forall (irred Σ Γ) args ->
    irred Σ Γ (mkApps t args).
  Proof.
    revert t. induction args; eauto; cbn. intros t Ht Hlam Hfix Hargs X.
    inversion Hargs; subst; clear Hargs. eapply IHargs; eauto.
    { clear X H2. intro X.
      inversion 1; subst; eauto.
      eapply (Hfix mfix idx (removelast args0)).
      destruct args0. inversion H.
      rewrite PCUICAstUtils.mkApps_nonempty in H; [inversion 1|].
      inversion H; subst; eauto. }
    intros. eapply (Hfix mfix idx (removelast args0)).
    destruct args0. inversion H.
    rewrite PCUICAstUtils.mkApps_nonempty in H; [inversion 1|].
    inversion H; subst; eauto. 
  Qed.  

  Lemma tConstruct_tFix_discr i n inst  (mfix : mfixpoint term) (idx : nat) (args : list term) :
  tConstruct i n inst = mkApps (tFix mfix idx) args -> False.
  Proof. 
    eapply rev_ind with (l := args); cbn; intros.
    - inversion H.
    - rewrite <- PCUICSafeReduce.tApp_mkApps in H0. inversion H0.
  Qed.

  Definition compile_pipeline_tConstruct_cons `{Heap} `{EWellformed.EEnvFlags}
  kn ind n inst args mind univ retro univ_decl 
  (Σ0 := mk_global_env univ [(kn , InductiveDecl mind)] retro) :
  let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl) in
  let i := mkInd kn ind in
  forall HΣ expΣ expt 
  (fo : firstorder_ind Σ (firstorder_env Σ) i)
  (Hnparam : forall (i : kername) (mdecl : mutual_inductive_body),
      lookup_env Σ i = Some (InductiveDecl mdecl) ->
      ind_npars mdecl = 0)
  (Hlookup : lookup_env Σ kn = Some (InductiveDecl mind))
  (Hargs: #|args| > 0)
  (Hirred : Forall (irred Σ []) args)
  (wt : ∥ Σ;;; [] |-  mkApps (tConstruct i n inst) args : mkApps (tInd i inst) [] ∥),
  let t := mkApps (tConstruct i n inst) args in
  let Σ_t := (Transform.transform verified_named_erasure_pipeline
  (Σ, t)
  (ErasureCorrectness.precond Σ t
     (mkApps (tInd i inst) []) HΣ expΣ expt wt Normalisation)).1 in
  forall Σ' (HΣ' : CompileCorrect.malfunction_env_prop Σ_t Σ')
    (Hax : PCUICClassification.axiom_free Σ) h,
  let Σ_v := (Transform.transform
  verified_named_erasure_pipeline
  (Σ, t)
  (ErasureCorrectness.precond2 Σ t
     (mkApps (tInd i inst) []) HΣ expΣ expt wt
     Normalisation t
     (red_eval H H0 Σ Hax HΣ expΣ
        (mkApps (tConstruct i n inst) args)
        expt t i
        inst [] wt fo Normalisation
        (sq
           (PCUICReduction.refl_red Σ []
              (mkApps (tConstruct i n inst)
                 args)))
        (mkApps_irred Σ []
           (tConstruct i n inst) args
           (tConstruct_irred Σ [] i n inst)
           (fun
              H2 : isLambda
                     (tConstruct i n inst) =>
            ssrbool.not_false_is_true H2)
           (tConstruct_tFix_discr i n inst)
           Hirred)))).1 in
  let vargs :=  map (compile_value_mf' Σ0 Σ_v) args in
  eval Σ' empty_locals h (compile_pipeline Σ (mkApps (tConstruct i n inst) args) HΣ expΣ expt (existT _ _ wt))
  h match Compile.lookup_constructor_args Σ_t i with
  | Some num_args => let num_args_until_m := firstn n num_args in
                    let index := #| filter (fun x => match x with 0 => false | _ => true end) num_args_until_m| in
                    Block (int_of_nat index, vargs)
  | None => fail "inductive not found"
  end.
Proof.
  intros.
  unshelve epose proof (Hthm := verified_malfunction_pipeline_theorem H H0 Σ Hax HΣ expΣ
  (mkApps (tConstruct i n inst) args) expt (mkApps (tConstruct i n inst) args) i inst [] wt fo Hnparam Normalisation _ _ _ _ HΣ' h);eauto.
  { eapply mkApps_irred; eauto. eapply tConstruct_irred. eapply tConstruct_tFix_discr. }
  cbn in Hthm.
  unshelve epose proof (Hthm' := verified_named_erasure_pipeline_fo H H0 Σ HΣ expΣ
  (mkApps (tConstruct i n inst) args) expt (mkApps (tConstruct i n inst) args) i inst [] fo Normalisation wt _ Hax);eauto.
  { eapply red_eval; eauto. eapply Normalisation.
    eapply mkApps_irred; eauto. eapply tConstruct_irred. eapply tConstruct_tFix_discr. }
  sq. 
  unfold compile_value_mf' in Hthm, Hthm'. rewrite compile_value_box_mkApps in Hthm, Hthm'.
  cbn in Hthm, Hthm'.  
  unfold ErasureCorrectness.pcuic_lookup_inductive_pars, EGlobalEnv.lookup_constructor_pars_args in *. 
  rewrite PCUICExpandLetsCorrectness.trans_lookup in Hthm, Hthm'. cbn in Hthm, Hthm'.
  rewrite ReflectEq.eqb_refl in Hthm, Hthm'. cbn in Hthm, Hthm'. 
  erewrite Hnparam, skipn_0 in Hthm; [|eauto]. 
  inversion Hthm'; subst. clear Hthm'. 
  unfold Compile.lookup_constructor_args, EGlobalEnv.lookup_constructor_pars_args,
  EGlobalEnv.lookup_constructor, EGlobalEnv.lookup_inductive, 
  EGlobalEnv.lookup_minductive in *. cbn in *. 
  set (EGlobalEnv.lookup_env _ _ ) in H4, Hthm.  
  case_eq o. 2: { intro X0. rewrite X0 in H4. inversion H4. }
  intros ? eq. rewrite eq in Hthm, H4. pose proof (eq':=eq).
  unfold o in eq'. eapply (verified_malfunction_pipeline_lookup  H H0 Σ HΣ expΣ
  (mkApps (tConstruct i n inst) args) expt (mkApps (tConstruct i n inst) args) i inst [] fo Normalisation wt _ Hax) in eq'.
  rewrite eq'; eauto.
  destruct args; [inversion Hargs |].
  destruct g; [inversion H4 |]. cbn in *. 
  destruct (nth_error _ _); [|inversion H4].
  set (map _ (map _ _)) in Hthm. simpl in Hthm.
  erewrite (f_equal (eval _ _ _ _ _)); eauto. clear Hthm. repeat f_equal.
  unfold l. now erewrite map_map.
Qed.

  Lemma filter_length_nil ind k mind Eind Hparam Hfo :
    nth_error (ind_bodies mind) ind = Some Eind ->
  List.length
  (filter (fun x0 : nat =>  match x0 with
      | 0 => true
      | S _ => false
      end)
     (firstn k (map cstr_nargs (ind_ctors Eind)))) = 
  List.length
           (filter (fun x : list camlType =>
               match x with
               | [] => true
               | _ :: _ => false
               end)
              (firstn k
                 (nth ind
                    (RocqType_to_camlType' mind
                       Hparam Hfo) []))).
   Proof. 
    intro Hind. unshelve erewrite RocqType_to_camlType'_nth; eauto.
    - eapply nth_error_forallb in Hfo; eauto.
    - destruct Eind; cbn. destruct andb_and. destruct (a _).
      rewrite (filter_ext _ (fun x =>
      match #|x| with
      | 0 => true
      | S _ => false
      end)).
      { clear. intro l; induction l; eauto. }
      revert k i0. clear Hind i i1 a. induction ind_ctors0; cbn; intros. 
      + intros. now repeat rewrite firstn_nil.
      + destruct k; eauto; cbn. destruct andb_and. destruct (a0 _). cbn.
        destruct a. cbn. rewrite RocqType_to_camlType_ind_ctors_length.
        revert i1. cbn. rewrite Hparam app_nil_r. cbn.
        rewrite length_rev. intro.  
        destruct cstr_args0; cbn. 
        * intros; f_equal. eapply IHind_ctors0; eauto.
        * eapply IHind_ctors0.
    - now eapply nth_error_Some_length. 
  Qed.                       

    Lemma filter_length_not_nil ind k mind Eind Hparam Hfo :
    nth_error (ind_bodies mind) ind = Some Eind ->
  List.length
  (filter (fun x0 : nat =>  match x0 with
      | 0 => false
      | S _ => true 
      end)
     (firstn k (map cstr_nargs (ind_ctors Eind)))) = 
  List.length
           (filter (fun x : list camlType =>
               match x with
               | [] => false
               | _ :: _ => true
               end)
              (firstn k
                 (nth ind
                    (RocqType_to_camlType' mind
                       Hparam Hfo) []))).
  Proof. 
    intro Hind. unshelve erewrite RocqType_to_camlType'_nth; eauto.
    - eapply nth_error_forallb in Hfo; eauto.
    - destruct Eind; cbn. destruct andb_and. destruct (a _).
      rewrite (filter_ext _ (fun x =>
      match #|x| with
      | 0 => false
      | S _ => true
      end)).
      { clear. intro l; induction l; eauto. }
      revert k i0. clear Hind i i1 a. induction ind_ctors0; cbn; intros. 
      + intros. now repeat rewrite firstn_nil.
      + destruct k; eauto; cbn. destruct andb_and. destruct (a0 _). cbn.
        destruct a. cbn. rewrite RocqType_to_camlType_ind_ctors_length.
        revert i1. cbn. rewrite Hparam app_nil_r. cbn.
        rewrite length_rev. intro.  
        destruct cstr_args0; cbn. 
        * eapply IHind_ctors0.
        * intros; f_equal. eapply IHind_ctors0; eauto.
    - now eapply nth_error_Some_length. 
  Qed. 
End firstorder.

Opaque compile_pipeline compile_malfunction_pipeline verified_named_erasure_pipeline. 

Lemma RocqType_to_camlType_oneind_type_Rel n k decl_type Hfo :
let T := RocqType_to_camlType_oneind_type (Σb := []) n k decl_type Hfo in
  exists i,  (k <= i) /\ (i < n + k) /\ T = Rel (n - S (i-k)).
Proof.
unfold RocqType_to_camlType_oneind_type.
unfold firstorder_type in Hfo.
set (fst (PCUICAstUtils.decompose_app decl_type)) in *.
set (snd (PCUICAstUtils.decompose_app decl_type)) in *.
destruct t; destruct l; inversion Hfo; cbn; eauto.
- apply andb_and in H0. destruct H0. apply leb_complete in H, H0. 
  exists n0; repeat split; eauto.
- destruct ind. inversion Hfo. 
- destruct ind; inversion Hfo.
Qed.   

Lemma RocqType_to_camlType_oneind_Rel mind ind larg T k  Hfo Hparam :
In larg (RocqType_to_camlType_oneind (Σb := []) mind ind Hparam Hfo) ->
nth_error larg k = Some T ->  
  exists i, (k <= i) /\ (i < #|ind_bodies mind| + k) /\ T = Rel (#|ind_bodies mind| - S (i-k)).
Proof. 
destruct mind, ind. revert k Hfo. induction ind_ctors0; intros k Hfo Hlarg HT.
- cbn in *; destruct andb_and. destruct (a Hfo). destruct (in_nil Hlarg).
- cbn; cbn in Hlarg. destruct andb_and. cbn in Hfo. destruct (a0 Hfo). 
  destruct andb_and. destruct (a1 i0). destruct a.
  unfold In in Hlarg. destruct Hlarg.
  2: { eapply IHind_ctors0; eauto. cbn. destruct andb_and.
        destruct (a _). rewrite (bool_irr _ i6 i4). eauto.
        Unshelve.
        cbn. apply andb_and. split; cbn; eauto. }
  cbn in Hparam, i3. rewrite Hparam in i3, H. rewrite app_nil_r in i3, H.
  clear - i3 HT H. set (rev cstr_args0) in *. rewrite <- H in HT.
  pose proof (nth_error_Some_length HT).
  revert T HT. clear H H0. cbn; set (#|ind_bodies0|) in *. 
  setoid_rewrite <- (Nat.sub_0_r k) at 1. assert (k >= 0) by lia. revert H.  
  revert k i3. generalize 0 at 1 2 3 4.
  induction l; cbn; intros. 1: { rewrite nth_error_nil in HT. inversion HT. }
  destruct andb_and. destruct (a0 i3). destruct a.
  cbn in HT. 
  case_eq (k - n0).
  + intro Heq.
    rewrite Heq in HT. inversion HT. 
    unshelve epose (RocqType_to_camlType_oneind_type_Rel _ _ _ _).
    5: erewrite H1 in e.
    rewrite H1. destruct e as [i2 [? [? ?]]]. exists (i2 + k - n0).
    repeat split. all: try lia. rewrite H3; f_equal. lia.
  + intros ? Heq. rewrite Heq in HT. cbn in HT. eapply IHl.
    2: { assert (n1 = k - S n0) by lia. now rewrite H0 in HT. }
    lia.  
Qed.  

Lemma RocqType_to_camlType'_unfold mind Σb Hparam Hfo l :
In l (RocqType_to_camlType' (Σb := Σb) mind Hparam Hfo) ->
exists ind Hfo', l =  RocqType_to_camlType_oneind (Σb := Σb) mind ind Hparam Hfo'.
Proof.
  destruct mind; cbn in *. revert Hfo.
  enough (forall ind_bodies1, forall
  Hfo : is_true
          (forallb
             (firstorder_oneind
                {|
                  Erasure.P.PCUICEnvironment.ind_finite := ind_finite0;
                  Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
                  Erasure.P.PCUICEnvironment.ind_params := ind_params0;
                  Erasure.P.PCUICEnvironment.ind_bodies := ind_bodies1;
                  Erasure.P.PCUICEnvironment.ind_universes := ind_universes0;
                  Erasure.P.PCUICEnvironment.ind_variance := ind_variance0
                |}) ind_bodies0),
In l
  (RocqType_to_camlType_fix (Σb := Σb) ind_bodies0 ind_finite0 ind_params0 ind_npars0 ind_universes0 ind_variance0
     Hparam ind_bodies1 Hfo) ->
exists
  (ind : one_inductive_body) (Hfo' : is_true
                                       (firstorder_oneind
                                          {|
                                            Erasure.P.PCUICEnvironment.ind_finite := ind_finite0;
                                            Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
                                            Erasure.P.PCUICEnvironment.ind_params := ind_params0;
                                            Erasure.P.PCUICEnvironment.ind_bodies := ind_bodies1;
                                            Erasure.P.PCUICEnvironment.ind_universes := ind_universes0;
                                            Erasure.P.PCUICEnvironment.ind_variance := ind_variance0
                                          |} ind)),
  l =
  RocqType_to_camlType_oneind (Σb := Σb)
    {|
      Erasure.P.PCUICEnvironment.ind_finite := ind_finite0;
      Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
      Erasure.P.PCUICEnvironment.ind_params := ind_params0;
      Erasure.P.PCUICEnvironment.ind_bodies := ind_bodies1;
      Erasure.P.PCUICEnvironment.ind_universes := ind_universes0;
      Erasure.P.PCUICEnvironment.ind_variance := ind_variance0
    |} ind Hparam Hfo').
  { eapply H; eauto. }
  induction ind_bodies0; cbn; intros.
  - inversion H.
  - destruct andb_and. destruct (a0 Hfo). destruct H.
    + exists a. now exists i0.
    + eapply IHind_bodies0; eauto.
  Qed.  
    
Lemma RocqType_to_camlType'_Rel mind ind larg T k Hfo Hparam: 
let typ := (RocqType_to_camlType' (Σb := []) mind Hparam Hfo) in
In larg (nth ind typ []) -> 
nth_error larg k = Some T -> 
  exists i, (k <= i) /\ (i < #|ind_bodies mind| + k) /\ T = Rel (#|ind_bodies mind| - S (i-k)).
Proof.
  intros typ. destruct (nth_in_or_default ind typ []).
  2: { rewrite e. intros Hlarg; destruct (in_nil Hlarg). }
  intro Hlarg. unfold typ in *. eapply RocqType_to_camlType'_unfold in i.
  destruct i as [ind' [Hfo' i]]. rewrite i in Hlarg. 
  now unshelve eapply RocqType_to_camlType_oneind_Rel; eauto.
Qed.

(* Lemma RocqType_to_camlType'_Rel' mind ind Hparam Hfo larg T k : 
let typ := (RocqType_to_camlType' (Σb := []) mind Hparam Hfo) in
In larg (nth ind typ []) -> 
nth_error larg k = Some T -> exists i, (0 <= i) /\ (i < #| ind_bodies mind|) /\ T = Rel (#|ind_bodies mind| - S i).
Proof.
  intros. unshelve epose (RocqType_to_camlType'_Rel _ ind); eauto. 
  edestruct e as [i [? [? ?]]]; eauto. exists (i - k). repeat split; eauto.
  all: lia.
Qed. *)

  Inductive nonDepProd : term -> Type :=
    | nonDepProd_tInd : forall i u, nonDepProd (tInd i u)
    | nonDepProd_Prod : forall na A B, closed A -> nonDepProd B -> nonDepProd (tProd na A B).

  Lemma nonDep_closed t : nonDepProd t -> closed t.  
  Proof.
    induction 1; cbn; eauto. 
    rewrite i; cbn. eapply PCUICLiftSubst.closed_upwards; eauto.
  Qed. 

  Fixpoint nonDep_decompose (t:term) (HnonDep : nonDepProd t) : list term * term
    := match HnonDep with 
    | nonDepProd_tInd i u => ([], tInd i u)
    | nonDepProd_Prod na A B clA ndB => let IH := nonDep_decompose B ndB in (A :: fst IH, snd IH)
    end.

  Lemma nonDep_typing_spine (cf:=config.extraction_checker_flags) (Σ:global_env_ext) us u_ty s (nonDep : nonDepProd u_ty) :
    PCUICTyping.wf Σ ->
    Σ ;;; [] |- u_ty : tSort s -> 
    All2 (fun u uty => Σ ;;; [] |- u : uty) us (fst (nonDep_decompose u_ty nonDep))  ->
    PCUICGeneration.typing_spine Σ [] u_ty us (snd (nonDep_decompose u_ty nonDep)).
  Proof.
  revert s us. induction nonDep; cbn in *; intros s us wfΣ Hty; cbn.
  - intro H; depelim H. econstructor; [|reflexivity]. repeat eexists; eauto.
  - set (PCUICInversion.inversion_Prod Σ wfΣ Hty) in *.
    destruct s0 as [s1 [s2 [HA [HB ?]]]]; cbn. intro H; depelim H.   
    epose (strengthening_type [] ([],, vass na A) [] B s2).
    pose proof (nonDep_closed _ nonDep).
    edestruct s0 as [s' [Hs _]]. cbn.  rewrite PCUICLiftSubst.lift_closed; eauto.
    econstructor; try reflexivity; eauto.
    + repeat eexists; eauto.
    + rewrite /subst1 PCUICClosed.subst_closedn; eauto.
  Qed.      

  Lemma firstorder_con_notApp `{checker_flags} {Σb} mind a :
    @firstorder_con Σb mind a -> 
    All (fun decl => ~ (isApp (decl_type decl))) (cstr_args a).
  Proof.
    intros Hfo. destruct a; cbn in *. induction cstr_args0; eauto.
    cbn in Hfo. rewrite rev_app_distr in Hfo. cbn in Hfo.
    rewrite alli_app in Hfo. rewrite <- plus_n_O in Hfo. apply andb_and in Hfo. destruct Hfo as [? Hfo].
    econstructor.
    - clear H0 IHcstr_args0. destruct a.
      simpl in *. apply andb_and in Hfo. destruct Hfo as [Hfo _].
      unfold firstorder_type in Hfo. cbn in Hfo. 
      assert (snd (PCUICAstUtils.decompose_app decl_type) = []).
      { destruct snd; eauto. destruct fst; try destruct ind; inversion Hfo. } 
      destruct decl_type; try solve [inversion Hfo]; eauto. intros _.
      cbn in H0. pose proof (PCUICInduction.decompose_app_rec_length decl_type1 [decl_type2]).
      rewrite H0 in H1. cbn in H1. lia. 
    - apply IHcstr_args0. now rewrite rev_app_distr.
  Qed. 

  Lemma firstorder_type_closed kn l k T :
    ~ (isApp T) -> 
    firstorder_type (Σb := []) #|ind_bodies l| k T -> 
    closed (subst (inds kn [] (ind_bodies l)) k T@[[]]).
  Proof. 
    intro nApp; destruct T; try solve [inversion 1]; cbn in *; eauto.  
    - intro H; apply andb_and in H. destruct H. rewrite H.
      eapply leb_complete in H, H0. rewrite nth_error_inds; [lia|eauto].
    - now destruct nApp.
  Qed. 

  Lemma firstorder_type_closed_gen Σb kn l k T :
    ~ (isApp T) -> 
    firstorder_type (Σb := Σb) #|ind_bodies l| k T -> 
    closed (subst (inds kn [] (ind_bodies l)) k T).
  Proof. 
    intro nApp; destruct T; try solve [inversion 1]; cbn in *; eauto.  
    - intro H; apply andb_and in H. destruct H. rewrite H.
      eapply leb_complete in H, H0. rewrite nth_error_inds; [lia|eauto].
    - now destruct nApp.
  Qed. 

  Lemma firstorder_nonDepProd mind kn Eind cstr_args0 x lind ind :
  nth_error (ind_bodies mind) ind = Some Eind ->
  is_assumption_context cstr_args0 ->
  All (fun decl => ~ (isApp (decl_type decl))) cstr_args0 ->
  let Ts := RocqType_to_camlType_ind_ctor (Σb := []) 0 #|ind_bodies mind| (rev cstr_args0) x in 
  All2 (fun a b => 0 <= a /\ a < #|ind_bodies mind| /\ b = Rel (#|ind_bodies mind| - S a)) lind Ts -> 
  { nd : nonDepProd (subst0 (inds kn [] (ind_bodies mind))
                     (it_mkProd_or_LetIn cstr_args0 (tRel (#|ind_bodies mind| - S ind + #|cstr_args0|)))@[[]]) &
  (fst (nonDep_decompose _ nd) = map (fun b : nat => tInd {| inductive_mind := kn; inductive_ind := #|ind_bodies mind| - S b |} []) lind) /\
  (snd (nonDep_decompose _ nd) = tInd {| inductive_mind := kn; inductive_ind := ind |} []) }.
Proof.
    intros Hind Hlets Happ. 
    set (X := (tRel (#|ind_bodies mind| - S ind + #|cstr_args0|))).
    assert (Hmind: #|ind_bodies mind| > 0).
    { destruct (ind_bodies mind); [|cbn; lia]. rewrite nth_error_nil in Hind. inversion Hind. }
    assert (HX : {nd : nonDepProd (subst (inds kn [] (ind_bodies mind)) #|cstr_args0| X@[[]]) &
      (fst (nonDep_decompose _ nd) = map (fun b : nat => tInd {| inductive_mind := kn; inductive_ind := #|ind_bodies mind| - S b |} []) []) /\ 
      (snd (nonDep_decompose _ nd) = tInd {| inductive_mind := kn; inductive_ind := ind |} [])}).
    { cbn.
      assert (#|cstr_args0| <= #|ind_bodies mind| - S ind + #|cstr_args0|) by lia.
      apply leb_correct in H. 
      destruct (_ <=? _); [| lia]. 
      assert (Heq : #|ind_bodies mind| - S ind + #|cstr_args0| - #|cstr_args0| < #|ind_bodies mind|) by lia. 
      pose proof (@nth_error_inds kn [] _ _ Heq). revert H0. 
      destruct (nth_error (inds _ _ _) _); [| inversion 1].
      inversion 1. clear H0 H2. unshelve eexists. econstructor. cbn. split; [sq; eauto|].
      repeat f_equal. destruct (ind_bodies _); [inversion Hmind|]. apply nth_error_Some_length in Hind. cbn in *. lia.  
    }
    clearbody X. intros Ts Hrel. rewrite <- (app_nil_r lind). revert HX Ts Hrel. generalize (@nil nat) as lind_done.
    revert X lind x. 
    induction cstr_args0; intros X lind x lind_done HX Ts Hrel; simpl in *; eauto.
    1: { eapply All2_length in Hrel. apply MRList.length_nil in Hrel.   
         now subst. }
    unfold Ts in Hrel. edestruct (RocqType_to_camlType_ind_ctor_app (Σb := [])) as [? [? ->]] in Hrel.
    apply All2_app_inv_r in Hrel as [lind' [lind'' [? [Hrel Ha]]]]. subst.
    rewrite <- app_assoc. eapply IHcstr_args0; eauto.
    { destruct decl_body;[inversion Hlets| eauto]. }
    { inversion Happ; eauto. }
    destruct a. destruct decl_body.
    + inversion Hlets.
    + destruct HX as [ndX [Xfst Xsnd]]. cbn. 
      unshelve econstructor. econstructor; eauto.
      { cbn in *. clear -x1 Happ. 
        apply andb_and in x1; destruct x1 as [x1 _].
        rewrite <- plus_n_O in x1. rewrite length_rev in x1. apply firstorder_type_closed; eauto.
        inversion Happ; eauto.
      }
      split; eauto.
      rewrite map_app. cbn. set (subst _ _ _). set (fst _). change (t :: y) with ([t]++y). f_equal; eauto. 
      unfold t. cbn in Ha. destruct andb_and. destruct (a _). clear a i i1.
      destruct decl_type; inversion i0.
      * cbn. revert i0 Ha. rewrite length_rev. cbn.  intros. apply andb_and in i0. destruct i0. rewrite <- plus_n_O in H.
        inversion Ha. subst. apply All2_length in X0. apply MRList.length_nil in X0. subst. clear Ha. 
        rewrite H. rewrite nth_error_inds. { apply leb_complete in H1. lia. } 
        cbn. repeat f_equal; eauto. destruct H4 as [? [? ?]]. inversion H4. 
        apply leb_complete in H1. lia.   
      * cbn in *. inversion Happ; subst. now cbn in H1. 
      * cbn in H0. destruct ind0. inversion H0.
  Qed. 

  Record pcuic_good_for_extraction {Σ : global_env} := 
    { ctors_max_length : forall mind j k ind ctors, nth_error mind j = Some ind -> nth_error (ind_ctors ind) k = Some ctors -> 
        #|cstr_args ctors| < int_to_nat max_length;
      ind_ctors_wB : forall mind j ind, nth_error mind j = Some ind -> #|ind_ctors ind| <= Z.to_nat Uint63.wB }.
  Arguments pcuic_good_for_extraction : clear implicits.

  Lemma is_assumption_context_length c : is_assumption_context c -> #|c| = context_assumptions c.
  Proof.
    induction c; eauto; cbn. destruct decl_body; cbn. 
    - inversion 1.
    - intros; f_equal; eauto.
  Qed.  

  Lemma Malfunction_ind_env_empty {funext:Funext}  `{EWellformed.EEnvFlags} 
  {P : Pointer} {HP : CompatiblePtr P P}  {HHeap : @Heap P} `{@CompatibleHeap P P _ _ _} 
  `{WcbvFlags} (cf:=config.extraction_checker_flags)
  univ retro univ_decl kn mind : 
  let Σ : global_env_ext_map := (build_global_env_map (mk_global_env univ [(kn , InductiveDecl mind)] retro), univ_decl) in
  forall t T HΣ expΣ expt typing Normalisation,
  let Σ_erase := (Transform.transform verified_named_erasure_pipeline (Σ, t) 
                  (precond Σ t T HΣ expΣ expt typing Normalisation)).1 in
  CompileCorrect.malfunction_env_prop Σ_erase [].   
  Proof.
    red. intros. cbn in *. unfold EGlobalEnv.declared_constant, EGlobalEnv.declared_inductive, 
    EGlobalEnv.declared_minductive in *.
    eapply verified_named_erasure_pipeline_lookup_env_in in H2 as [? [? ?]]; eauto.
    cbn in H2. destruct (c == kn); inversion H2. rewrite <- H7 in H5. inversion H5.
  Qed.       

  Import PCUICInductiveInversion PCUICWfUniverses.

  Lemma camlValue_to_RocqValue {funext:Funext}  `{EWellformed.EEnvFlags} 
    {P : Pointer} {HP : CompatiblePtr P P}  {HHeap : @Heap P} `{@CompatibleHeap P P _ _ _} 
    `{WcbvFlags} (cf:=config.extraction_checker_flags)
    univ retro univ_decl kn mind
    (Hheap_refl : forall h, R_heap h h)
    (Hparam : ind_params mind = [])
    (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
    (Hmono : ind_universes mind = Monomorphic_ctx)
    (Hfin : ind_finite mind == Finite )
    (empty_heap : heap):
    let Σ : global_env_ext_map := (build_global_env_map (mk_global_env univ [(kn , InductiveDecl mind)] retro), univ_decl) in
    forall 
      (HfoΣ : is_true (forallb (@firstorder_oneind (firstorder_env Σ) mind) (ind_bodies mind))) 
      (Hfo : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind)))
      (Hnparam : forall (i : kername) (mdecl : mutual_inductive_body),
      lookup_env Σ i = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0),
     let adt := RocqType_to_camlType mind Hparam Hfo in
    pcuic_good_for_extraction Σ ->
    forall (wfΣ : PCUICTyping.wf_ext Σ) expΣ,
    with_constructor_as_block = true ->
    forall v ind Eind, 
    ind < List.length (snd adt) ->
    lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
    realize_ADT _ _ [] [] adt [] All_nil ind v ->
    exists t expt (typing : ∥Σ ;;; [] |- t : tInd (mkInd kn ind) []∥), 
    irred Σ [] t /\
       forall h, eval [] empty_locals h (compile_pipeline Σ t wfΣ expΣ expt (existT _  (tInd (mkInd kn ind) []) typing)) h v.
  Proof. 
    rename H into HEnv. rename H0 into Hcompat. rename H1 into H.   
    intros Σ HfoΣ Hfo Hnparam adt good wfΣ expΣ Hflag v ind Eind Hind Hlookup [step Hrel].
    revert kn mind Hparam Hindices Hmono Hfin v ind Eind Σ HfoΣ Hfo Hnparam adt good wfΣ expΣ Hflag Hind Hlookup Hrel. 
    induction step; intros; [inversion Hrel|]. 
    apply leb_correct in Hind. simpl in Hrel, Hind. 
    unfold Nat.ltb in Hrel. rewrite Hind in Hrel.
    assert (Hax: PCUICClassification.axiom_free Σ).
    { intros ? ? X. now inversion X. }
    destruct Hrel as [Hrel | Hrel].
    - apply Existsi_spec in Hrel as [k [Ts [Hk [HkS [Hrel HTs]]]]].
      cbn in HkS.
      destruct (filter_firstn' _ _ _ _ HkS) as [k' [Hk' [Hfilter Hwit]]].
      destruct Hwit as [As [Ha [Ha' Ha'']]].
      pose (MRList.nth_error_spec (ind_bodies mind) ind).
      destruct n; intros.
        2: { apply leb_complete in Hind.
             rewrite RocqType_to_camlType'_length in Hind. lia. } 
      pose (MRList.nth_error_spec (ind_ctors x) k').
      assert (Hfo_x : is_true (@firstorder_oneind [] mind x)).
        { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
      destruct n; intros; eauto.
        2: { 
          unshelve erewrite RocqType_to_camlType'_nth in Hk'; eauto.
          rewrite RocqType_to_camlType_oneind_length in Hk'.
          lia. }
    set (i := {| inductive_mind := kn; inductive_ind := ind |}) in *. 
    assert (Hcstr': forall b n, nth_error (ind_ctors x) n = Some b -> #|cstr_args b| = cstr_arity b). 
    { intros b m Hx; assert (declared_constructor Σ (i, m) mind x b).
      { split; eauto. split; eauto. simpl. now left. }
        erewrite <- ErasureCorrectness.declared_constructor_arity; eauto.
        eapply PCUICWeakeningEnvTyp.on_declared_constructor in H0
        as [? [? ?]].
        eapply All2_In in onConstructors as [[univs onConstructor]].
        2: { now eapply nth_error_In. }
        eapply on_lets_in_type in onConstructor.
        now apply is_assumption_context_length.
     } 
     assert (Hcstr_gen: forall b n, nth_error (ind_ctors x) n = Some b -> 
        is_assumption_context (cstr_args b) /\
        test_context (closedu 0) (cstr_args b)). 
      { intros b m Hx; assert (declared_constructor Σ ({| inductive_mind := kn; inductive_ind := ind |}, m) mind x b).
        { split; eauto. split; eauto. simpl. now left. }
        eapply PCUICWeakeningEnvTyp.on_declared_constructor in H0 as [? [? ?]].
        eapply All2_In in onConstructors as [[univs onConstructor]].
          2: { now eapply nth_error_In. } 
        have isa: is_assumption_context (cstr_args b).
        { now eapply on_lets_in_type in onConstructor. }
        split => //.
        destruct onConstructor.
        rewrite Hmono in on_cargs.
        clear -isa on_cargs wfΣ.
        induction (cstr_args b) in univs, on_cargs, isa |- *; cbn; auto.
        cbn in on_cargs.
        destruct a => //. destruct decl_body => //.
        destruct univs => //. destruct on_cargs as [onca hty].
        rewrite (IHc univs) //=; cbn.
        hnf in hty. destruct hty as [onb [s [onty eq]]]. cbn in *. destruct eq; try subst s.
        eapply typing_wf_universes in onty => //. 2:apply wfΣ.
        move/andP: onty => [hdecl _]. eapply wf_universes_closedu in hdecl => //.
        red. cbn. intro. csets. }
      assert (Hcstr : forall b n, nth_error (ind_ctors x) n = Some b ->
             #|cstr_args b| = context_assumptions (cstr_args b)).
        { intros b m hx; eapply Hcstr_gen in hx as [hctx _].
          now eapply is_assumption_context_length in hctx. }
      exists (tConstruct (mkInd kn ind) k' []). 
      unshelve refine (let expt := _ in ex_intro _ expt _). 
      { eapply PCUICEtaExpand.expanded_tConstruct_app with (mind := mind) (idecl := x) (cdecl := x0) (args:=[]).
        3: eauto. { unfold declared_constructor, declared_inductive. now cbn. }
           unshelve erewrite RocqType_to_camlType'_nth in Ha; eauto.
           eapply RocqType_to_camlType_oneind_nth in Ha as [? [? ?]].
           erewrite Hnparam. 2: cbn; now erewrite ReflectEq.eqb_refl. 
           erewrite <- Hcstr; eauto. cbn. rewrite e0 in H0.
           inversion H0. destruct As; inversion Ha''; subst. clear - H1; cbn in *; lia. }
      clearbody expt. unshelve refine (let wt := _ in ex_intro _ wt _). 
      { unshelve epose proof (Htyp := type_Construct Σ [] (mkInd kn ind) k' [] mind x x0 _ _ _).
          ** econstructor.
          ** unfold declared_constructor, declared_inductive. now cbn.
          ** unfold consistent_instance_ext, consistent_instance; cbn.
             now rewrite Hmono.
          ** 
          unshelve erewrite RocqType_to_camlType'_nth in Hfilter, Ha, Ha'; eauto.
          unfold RocqType_to_camlType_oneind in Hfilter, Ha, Ha'. destruct x. 
          destruct andb_and. destruct (a _).
          apply RocqType_to_camlType_ind_ctors_nth in Ha.
          destruct Ha as [a0 [? [? ?]]].
          rewrite H1 in Ha''.
          unfold type_of_constructor in Htyp.  
          assert (RocqType_to_camlType_ind_ctor 0 #|ind_bodies mind|
          (rev (cstr_args a0 ++ ind_params mind)) x = []).
          { destruct RocqType_to_camlType_ind_ctor; eauto. }
          clear Ha''. apply f_equal with (f := @List.length _) in H2.
          rewrite RocqType_to_camlType_ind_ctors_length in H2.
          cbn in H2. erewrite length_rev, length_app in H2.
          assert (Ha0 : #|cstr_args a0| = 0) by lia. apply MRList.length_nil in Ha0.
          rewrite e0 in H0. inversion H0. subst; clear H0.
          destruct wfΣ as [wfΣ _]. inversion wfΣ as [_ wfΣ'].
          cbn in wfΣ'. inversion wfΣ'; subst. clear X.
          inversion X0 as [_ ? _ wf_ind].
          destruct wf_ind as [wf_ind _ _ _].
          inversion wfΣ'; subst. inversion X1; subst. inversion on_global_decl_d. 
          eapply Alli_nth_error in onInductives; eauto. cbn in onInductives.
          inversion onInductives. unfold PCUICGlobalMaps.on_constructors in *. cbn in *. 
          eapply All2_nth_error_Some  in onConstructors; eauto. destruct onConstructors as [l' [? onConstructor]].
          erewrite @cstr_eq with (i:=ind) in Htyp; eauto.
          unfold cstr_concl in Htyp. 
          erewrite Hparam, Ha0 in Htyp. cbn in Htyp. 
          assert (cstr_indices a0 = []).
          { apply MRList.length_nil. erewrite @cstr_indices_length with (Σ:=Σ) (ind:=(mkInd kn ind,k')); eauto. 
            2: { repeat split. cbn. left. reflexivity. all:cbn; eauto. } cbn. eapply nth_error_forall in Hindices; eauto.
                 cbn in Hindices. now rewrite Hindices. }
          rewrite H0 in Htyp; clear H0; cbn in Htyp.
          rewrite Ha0 Hparam in Htyp. cbn in Htyp.   
          rewrite inds_spec in Htyp.  
          assert (#|ind_bodies mind| - S ind + 0 + 0 - 0 = #|ind_bodies mind| - S ind)
          by lia. rewrite H0 in Htyp; clear H0.
          erewrite <- mapi_length in Htyp.
          rewrite <- MRList.nth_error_rev, MRList.nth_error_mapi, e in Htyp.
          cbn in Htyp. sq; exact Htyp.  
          now rewrite mapi_length. }
        clearbody wt. split.
        { eapply tConstruct_irred. }
        intros h. 
        assert (Hlookup_env : lookup_env Σ kn = Some (InductiveDecl mind)).
        { unfold firstorder_ind. clear -Hlookup e. unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen in Hlookup.
          destruct (lookup_env _ _). 2: { inversion Hlookup. }
          destruct g; [inversion Hlookup|]. 
          destruct (nth_error _ _); inversion Hlookup; subst; eauto. }
        assert (firstorder_ind Σ (firstorder_env Σ) i). 
        { unfold firstorder_ind. rewrite Hlookup_env.
          unfold firstorder_mutind. eapply andb_and. split; eauto.
          destruct ind_finite; inversion Hfin; eauto. }
        unshelve epose proof (Hcompile := compile_pipeline_tConstruct_nil _ _ _ _ _ _ _ _ wfΣ expΣ expt _ _ _ wt [] _ Hax h); eauto.
        { eapply Malfunction_ind_env_empty; eauto. }
        unfold Compile.lookup_constructor_args, EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in Hcompile.
        cbn in Hcompile. rewrite Hrel.
        unshelve epose proof (Hthm' := verified_named_erasure_pipeline_fo P HHeap Σ wfΣ expΣ
        (tConstruct i k' []) expt (tConstruct i k' []) i [] [] _ Normalisation wt _ Hax);eauto.
        { eapply red_eval with (args := []); eauto. eapply Normalisation.
          clear. eapply tConstruct_irred. }
        inversion Hthm'; subst; clear Hthm'; rename H2 into Hthm'.  
        unfold ErasureCorrectness.pcuic_lookup_inductive_pars, EGlobalEnv.lookup_constructor_pars_args in *. 
        rewrite PCUICExpandLetsCorrectness.trans_lookup in H1. cbn in H1.
        rewrite ReflectEq.eqb_refl in H1. cbn in H1.
        unfold EGlobalEnv.lookup_constructor_pars_args, EGlobalEnv.lookup_constructor, 
        EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in Hthm'. 
        set (EGlobalEnv.lookup_env _ _) in Hthm'.
        case_eq o. 2: { intro He; rewrite He in Hthm'. cbn in Hthm'. inversion Hthm'. }
        intros ? He. inversion H1; subst. rewrite He in Hthm'. pose proof (He' := He). 
        unfold o in He. eapply (verified_malfunction_pipeline_lookup P HHeap Σ wfΣ expΣ
        (tConstruct i k' []) expt (tConstruct i k' []) i [] [] _ _ wt) in He; eauto.
        rewrite He in Hcompile. destruct g. { inversion Hthm'. }
        eapply verified_named_erasure_pipeline_lookup_env_in' in He' as [? [? ?]]; eauto. 
        cbn in H2. rewrite ReflectEq.eqb_refl in H2. inversion H2; cbn in H4; subst. clear H2 Hthm'.
        rewrite H4 in Hcompile. cbn in Hcompile. rewrite nth_error_map nth_error_mapi in Hcompile.
        rewrite e in Hcompile. cbn in Hcompile.
        erewrite <- filter_length_nil; eauto.
        set (size := #|_|) in Hcompile. set (size' := #|_|).
        enough (size = size').
        { now rewrite <- H2. }
        unfold size, size'. clear -Hcstr'. revert Hcstr' k'.  generalize (ind_ctors x). clear.
        induction l; eauto; cbn; intros.  
        cbn. destruct k'; cbn; eauto. pose proof (Hcstr' a 0 eq_refl).
        destruct a; cbn in *. rewrite H. destruct cstr_arity0; cbn; [f_equal|].
        eapply IHl.
        {intros; eapply Hcstr' with (n := S n); eauto. }  
        eapply IHl.
        {intros; eapply Hcstr' with (n := S n); eauto. }  
    - apply leb_complete in Hind. 
      apply Existsi_spec in Hrel as [k [Ts [Hk [HkS [Hrel HTs]]]]].
      cbn in HkS.  
      destruct (filter_firstn' _ _ _ _ HkS) as [k' [Hk' [Hfilter Hwit]]].
      destruct Hrel as [v' [eq Hv']].
      destruct Ts as [|T Ts]. (* not possible filtered *) 
      + apply filter_nth_error in HTs. destruct HTs as [_ HTs]. 
        inversion HTs.
      + pose proof (HTs' := HTs). apply filter_nth_error in HTs. destruct HTs as [HTs _].
        subst.
        assert (Forall2 (fun v T => 
        (exists t (expt : PCUICEtaExpand.expanded Σ [] (fst t))  
               (wt : ∥ (Σ , univ_decl) ;;; [] |- fst t : tInd (mkInd kn (#|ind_bodies mind| - S (snd t))) [] ∥),
        irred Σ [] (fst t) /\
        (forall h, eval [] empty_locals h (compile_pipeline Σ (fst t) wfΣ expΣ expt (_ ; wt)) h v)
        /\ (0 <= snd t) /\ (snd t < #|ind_bodies mind|) /\ T = Rel (#|ind_bodies mind| - S (snd t)))) v' (T::Ts)).
        { 
          assert (Forall (fun T => exists l l', In (l ++ [T] ++ l') (nth ind (RocqType_to_camlType' (Σb:=[]) mind Hparam Hfo) [])) (T::Ts)).
          { clear -HTs. set (l := T::Ts) in *. clearbody l.
            assert (exists l', In (l' ++ l) (nth ind (RocqType_to_camlType' mind Hparam Hfo) [])).  
            { exists []; eauto.  }
            clear T Ts HTs; revert H. induction l; econstructor.
            - destruct H as [l' HIn]. exists l'; exists l; eauto.
            - eapply IHl. destruct H as [l' HIn]. exists (l' ++ [a]). 
              now rewrite <- app_assoc. } 
          eapply Forall2_Forall_mix; [| apply H0]; clear H0 Hwit HkS Hk HTs HTs'. 
          unfold realize_value, to_realize_value in Hv'.
          induction Hv'; econstructor. 
          - clear IHHv'. intros [l0 [l0' HTs]].
            unshelve eapply RocqType_to_camlType'_Rel with (k:=#|l0|) in HTs; try reflexivity.
            3: { rewrite nth_error_app2; eauto. rewrite Nat.sub_diag. reflexivity. }
            destruct HTs as [i [? [? Hx ]]]; subst. 
            cbn in H0. unfold realize_term in H0.
            specialize (H0 empty_heap).
            destruct H0 as [t [h' [Hheap ?]]].
            specialize (H0 empty_heap h' _ Hheap). rewrite to_list_nth in H0.
            + rewrite RocqType_to_camlType'_length. lia.
            + pose (MRList.nth_error_spec (ind_bodies mind) (i - #|l0|)).
              destruct n. 2: { clear -H1 H2 l1. lia. }
              eapply IHstep in H0; eauto.
              2: { unfold RocqType_to_camlType; cbn. now rewrite RocqType_to_camlType'_length. }
              destruct H0 as [t' H0]. cbn. 
              exists (t',i - #|l0|). cbn. intros. destruct H0 as [expt [wt H0]].
              cbn in H0. destruct H0. 
              exists expt, wt. repeat split; eauto. lia. 
              unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen, lookup_env. cbn.
              rewrite ReflectEq.eqb_refl. erewrite nth_error_nth'; cbn; [eauto|lia].
              Unshelve. all:eauto. apply wfΣ.  
          - eapply IHHv'. 
        }
        pose proof (Hv'Ts := Forall2_length H0).
        destruct (Forall2_exists _ _ _ _ _ _ H0) as [lv' Hlv']. clear H0. 
        eapply Forall2_sym in Hlv'.
        destruct (Forall2_exists_dep _ _ _ _ _ _ Hlv') as [explv Hlv'']. 
        clear Hlv'. rename Hlv'' into Hlv'. 
        destruct (Forall2_exists_dep _ _ _ _ _ _ Hlv') as [typ_lv Hlv'']. 
        clear Hlv'. rename Hlv'' into Hlv'. cbn in Hlv'. 
        eapply Forall_Forall2_and_inv in Hlv' as [Hlv' Hirred].
        eapply Forall_map in Hirred.
        rewrite (zipAll_fst _ _ (fun x => (x.π1).1)) in Hirred. 
        rewrite (zipAll_fst _ _ fst) in Hirred. 
        eapply Forall2_and_inv in Hlv' as [Hlv'' Hlv'].
        pose proof (Forall2_forall _ _ Hlv''). clear Hlv''. rename H0 into Hlv_eval.
        eapply (Forall2_map (fun tu a => 0 <= tu /\
          (tu < #|ind_bodies mind| /\ a = Rel (#|ind_bodies mind| - S tu)))) in Hlv'.
        rewrite zip_snd in Hlv'; eauto.
        rewrite (zipAll_fst _ _ (fun x => (x.π1).2)) in Hlv'. 
        rewrite (zipAll_fst _ _ snd) in Hlv'. 
        set (t := mkApps (tConstruct (mkInd kn ind) k' []) (map fst lv')).
        assert (HEind: nth_error (ind_bodies mind) ind = Some Eind).
        { 
          unfold lookup_inductive, lookup_inductive_gen,lookup_minductive_gen in Hlookup. 
          cbn in Hlookup. rewrite ReflectEq.eqb_refl in Hlookup.
          destruct (nth_error (ind_bodies mind) ind); inversion Hlookup; eauto. }
        erewrite RocqType_to_camlType'_nth_length in Hk'; eauto.
        eapply nth_error_Some' in Hk'. destruct Hk' as [decl Hk'].
        assert (Hinductive : declared_inductive Σ.1 (mkInd kn ind) mind Eind).
        {
          red. unfold declared_inductive. cbn. repeat split; eauto.
        }
        assert (hfo_Eind : is_true (@firstorder_oneind [] mind Eind)).
          { clear - HEind Hfo; eapply forallb_nth_error with (n := ind) in Hfo.
            now rewrite HEind in Hfo. }    
        assert (is_true (@firstorder_con [] mind decl)).
          { unfold firstorder_oneind in hfo_Eind. eapply andb_and in hfo_Eind.
            destruct hfo_Eind as [hfo_Eind _]. eapply forallb_nth_error with (n := k') in hfo_Eind. 
            now rewrite Hk' in hfo_Eind.  }
        assert (Hconstructor: declared_constructor Σ.1 (mkInd kn ind,k') mind Eind decl).
        { red. split; eauto. }
        assert (expt : PCUICEtaExpand.expanded Σ.1 [] t).
        { eapply PCUICEtaExpand.expanded_tConstruct_app; eauto.
          2: { eapply All_Forall. now apply All_map. }
          erewrite Hnparam; cbn. 2: now erewrite ReflectEq.eqb_refl. 
          rewrite length_map. eapply Forall2_length in Hlv'.
          rewrite length_map in Hlv'. rewrite Hlv'.  
          revert Hind HEind Hk' HTs' Hwit; intros.
          destruct Hwit as [A [HA [HA' _]]]. rewrite Nat.sub_0_r in HTs'. rewrite HTs' in HA'. 
          inversion HA'; subst; clear HA'.
          rewrite RocqType_to_camlType'_length in Hind. 
          unshelve erewrite RocqType_to_camlType'_nth in HA; eauto.
          unshelve eapply RocqType_to_camlType_oneind_nth_ctors in HA; eauto.
          destruct HA as [? HA].
          eapply RocqType_to_camlType_ind_ctors_nth in HA. 
          destruct HA as [a0 [? [? ?]]]. rewrite Hk' in H1. symmetry in H1; inversion H1; subst; clear H1.
          revert x0 H2. rewrite Hparam. rewrite app_nil_r. intros.
          rewrite H2. rewrite RocqType_to_camlType_ind_ctors_length.
          rewrite length_rev. epose (context_assumptions_length_bound (cstr_args decl)). lia.
        }
        assert (Hcstr_indices : cstr_indices decl = []).
        { apply MRList.length_nil. erewrite @cstr_indices_length with (Σ:=Σ) (ind:=(mkInd kn ind,k')); eauto. 
          cbn. eapply nth_error_forall in Hindices; eauto.
               cbn in Hindices. now rewrite Hindices. }
        exists t; exists expt.
        assert (wt : ∥ Σ;;; [] |- t : tInd (mkInd kn ind) [] ∥).
        {
        clear Hlv_eval. set (typ_lv' := typ_lv) in Hirred.
        clearbody typ_lv'. 
        eapply All_Forall in typ_lv. eapply All_sq in typ_lv. 
        destruct Hwit as [A [HA [HA' _]]]. rewrite Nat.sub_0_r in HTs'. rewrite HTs' in HA'. 
        inversion HA'; subst; clear HA'.
        rewrite RocqType_to_camlType'_length in Hind. 
        unshelve erewrite RocqType_to_camlType'_nth in HA; eauto.
        unshelve eapply RocqType_to_camlType_oneind_nth_ctors in HA; eauto.
        destruct HA as [? HA].
        eapply RocqType_to_camlType_ind_ctors_nth in HA. 
        destruct HA as [a0 [? [? ?]]]. rewrite Hk' in H1. symmetry in H1; inversion H1; subst; clear H1.
        revert x0 H2. rewrite Hparam. rewrite app_nil_r. intros.
        sq. 
        eapply PCUICGeneration.type_mkApps.
        ++ eapply type_Construct; eauto. 
          unfold consistent_instance_ext, consistent_instance; cbn.
          now rewrite Hmono. 
        ++ pose proof (wfΣ_c := wfΣ). destruct wfΣ as [wfΣ _]. inversion wfΣ as [_ wfΣ'].
          cbn in wfΣ'. inversion wfΣ'. clear X. inversion X0. inversion on_global_decl_d.
          eapply Alli_nth_error in onInductives; eauto. cbn in onInductives.
          inversion onInductives. unfold PCUICGlobalMaps.on_constructors in *. cbn in *.
          unfold type_of_constructor. cbn.
          eapply All2_nth_error_Some  in onConstructors; eauto.
          destruct onConstructors as [l' [? onConstructor]].          
          pose proof (Hlets := on_lets_in_type _ _ _ _ _ _ _ _ _ onConstructor). cbn in Hlets. 
          revert typ_lv. erewrite cstr_eq; eauto. rewrite Hparam. cbn. 
          unfold cstr_concl, cstr_concl_head. 
          rewrite Hparam Hcstr_indices. cbn. rewrite <- plus_n_O. intro.  
          revert typ_lv; intro.   
          eapply @All_map with (P := fun a =>
          (Σ, univ_decl);;; []
           |- a.1 : tInd {| inductive_mind := kn;
           inductive_ind := #|ind_bodies mind| - S a.2 |} []) in typ_lv.
          rewrite (zipAll_fst _ _ id) map_id in typ_lv.
          eapply @All_All2_refl with (R := fun a b: term * nat =>
            (Σ, univ_decl);;; []
             |- a.1 : tInd {| inductive_mind := kn;
             inductive_ind := #|ind_bodies mind| - S b.2 |} []) in typ_lv.
          eapply @All2_map_left with (P := fun a b =>
            (Σ, univ_decl);;; []
             |- a : tInd {| inductive_mind := kn;
                   inductive_ind := #|ind_bodies mind| - S (snd b) |} []) in typ_lv.
          eapply @All2_map_right with (P := fun a b =>
            (Σ, univ_decl);;; []
                     |- a : tInd {| inductive_mind := kn; inductive_ind := #|ind_bodies mind| - S b |} []) in typ_lv. 
          set (lind:= map snd lv') in *. set (lterm := map fst lv') in *. clearbody lind lterm.
          epose (Hnd := firstorder_nonDepProd). edestruct Hnd as [Hnd' [Hndfst Hndsnd]]; eauto. 
          1: eapply firstorder_con_notApp; eauto. 
          2: {
          unshelve epose proof (PCUICInductiveInversion.declared_constructor_valid_ty (Σ, univ_decl) [] mind Eind  
          {| inductive_mind := kn; inductive_ind := ind |} k' decl [] _ _ _); eauto.
          destruct X as [_ [sctype [Hctype _]]].
          { unfold consistent_instance_ext, consistent_instance; cbn. now rewrite Hmono. }
          rewrite <- Hndsnd. eapply nonDep_typing_spine with (s:=sctype) ; eauto.
          { revert Hctype; intro. unfold type_of_constructor in Hctype. cbn in Hctype.
            erewrite cstr_eq in Hctype; eauto. rewrite Hparam in Hctype. cbn in Hctype. 
            unfold cstr_concl, cstr_concl_head in Hctype. rewrite Hparam Hcstr_indices app_nil_r in Hctype.
            cbn in Hctype. rewrite <- plus_n_O in Hctype. eauto. }
          rewrite Hndfst. now apply All2_map_right. } 
          Unshelve. 2: eauto. 
          rewrite <- H2. now eapply Forall2_All2.
          }
          
        exists wt.
        assert (Hirred_t : irred Σ [] t).
        { eapply mkApps_irred; eauto. eapply tConstruct_irred. eapply tConstruct_tFix_discr. }
        split; eauto. intros h. set (i := mkInd _ _) in *. 
        assert (Hfo_ind : firstorder_ind Σ (firstorder_env Σ) i).
        { unfold firstorder_ind. cbn. rewrite ReflectEq.eqb_refl. eapply andb_and.  
          split; eauto. clear -Hfin. destruct ind_finite; eauto. }
        unshelve epose proof (Hcompile := compile_pipeline_tConstruct_cons _ _ _ _ _ _ _ _ _ wfΣ expΣ expt _ _ _ _ _ wt _ _ Hax h); eauto.
        { cbn. now rewrite ReflectEq.eqb_refl. }
        { rewrite length_map. eapply Forall2_length in Hlv'. rewrite length_map in Hlv'. cbn in Hlv'; lia. }
        2: { eapply Malfunction_ind_env_empty; eauto. }
        unshelve epose proof (Hthm' := verified_named_erasure_pipeline_fo P HHeap Σ wfΣ expΣ
        t expt t _ [] [] _ Normalisation wt _ Hax);eauto.
        { eapply red_eval with (args := []); eauto. eapply Normalisation. }
        inversion Hthm'; subst; clear Hthm'; rename H2 into Hthm'.  
        cbn in Hthm'; cbn in Hcompile. 
        unfold t in H1. rewrite compile_value_box_mkApps in H1. cbn in H1.
        unfold EGlobalEnv.lookup_constructor_pars_args, EGlobalEnv.lookup_constructor , 
          Compile.lookup_constructor_args, ErasureCorrectness.pcuic_lookup_inductive_pars, 
          EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *. cbn in Hcompile, H1.
        rewrite ReflectEq.eqb_refl in H1. 
        set (EGlobalEnv.lookup_env _ _) in Hthm'.
        case_eq o. 2: { intro He; rewrite He in Hthm'. cbn in Hthm'. inversion Hthm'. }
        intros ? He. inversion H1; subst. rewrite He in Hthm'. 
        pose proof (He' := He). 
        unfold o in He. eapply verified_malfunction_pipeline_lookup with (args := []) in He; eauto.
        rewrite He in Hcompile. destruct g. { inversion Hthm'. }
        eapply verified_named_erasure_pipeline_lookup_env_in' with (args := []) in He' as [? [? ?]]; eauto. 
        cbn in H2. rewrite ReflectEq.eqb_refl in H2. inversion H2; cbn in H4; subst. clear H2 Hthm'. rewrite H4 in Hcompile. clear H4. 
        cbn in Hcompile. rewrite nth_error_map nth_error_mapi in Hcompile.
        rewrite HEind in Hcompile. cbn in Hcompile.
        erewrite <- filter_length_not_nil; eauto.
        set (size := #|_|) in Hcompile. set (size' := #|_|).
        enough (size = size').
        { rewrite <- H2. 
          set (vv := map (compile_value_mf' _ _) _) in Hcompile.
          enough (v' = vv). { now subst. }
          unfold vv; clear vv Hcompile. revert Hlv_eval; intro.
          rewrite -/ t. rewrite <- (map_id v'). specialize (Hlv_eval h).
          eapply Forall2_map_eq. set (Σ0 := mk_global_env _ _ _) in Σ.
          rewrite -/ Σ -/ Σ0. set (precond2 _ _ _ _ _ _ _ _ _ _). unfold t.
          set (f := compile_value_mf' _ _).
          eapply Forall2_Forall_mix; try apply Hirred. 
          erewrite Hnparam, skipn_0 in H3.
          2: cbn; now erewrite ReflectEq.eqb_refl.
          set (ff:= fun v : term => _) in H3. 
          eapply (Forall_map ff) in H3.
          eapply Forall2_Forall_mix; try apply H3. set (precond2 _ _ _ _ _ _ _ _ _ _).
          eapply (Forall2_impl (fun x y => firstorder_evalue_block (Transform.transform verified_named_erasure_pipeline (Σ, t) p0).1 (ff (x.π1.π1.1)) 
              -> irred Σ [] x.π1.π1.1 -> f (x.π1.π1.1) = y.1)) in Hlv_eval.
          {
            eapply (Forall2_map (fun x y => firstorder_evalue_block (Transform.transform verified_named_erasure_pipeline (Σ, t) p0).1  (ff x) -> irred Σ [] x -> f x = y)) in Hlv_eval.
            rewrite zip_fst in Hlv_eval; eauto.
            rewrite (zipAll_fst _ _ (fun x => (x.π1).1)) in Hlv_eval.
            rewrite (zipAll_fst _ _ fst) in Hlv_eval.
            eapply Forall2_sym; eauto. 
            eapply Forall2_impl; eauto. intros. symmetry; eauto.  
          }
          { intros. destruct a, b; cbn. destruct x; cbn. destruct x. cbn; clear f. cbn in H5, H6.  
            pose Normalisation. set (Σ_t := (_).1).
            erewrite (ProofIrrelevance.proof_irrelevance _ p0 p) in H5.
            rewrite -/ Σ_t -/ Σ0 in H5. set (compile_value_box _ _ _) in *.
            cbn in s. 
            unshelve epose proof (Hfo' := verified_named_erasure_pipeline_fo P HHeap Σ wfΣ expΣ
              t0 e t0 _ [] [] _ Normalisation s _ _); eauto.
            { eapply red_eval with (args:=[]); eauto. }
            unfold Σ_t. erewrite (ProofIrrelevance.proof_irrelevance _ p).
            set (p2 := precond2 _ _ _ _ _ _ _ _ _ _) in Hfo'.
            erewrite (ProofIrrelevance.proof_irrelevance _ p2) in Hfo'.
            unfold Σ_t in H5.
            erewrite (ProofIrrelevance.proof_irrelevance _ p) in H5.
            unshelve erewrite compile_value_mf_fo. 4,7,8,10:eauto.
            1,2,4: eauto.
            set (pt0 := precond _ _ _ _ _ _ _ _). clearbody pt0. 
            unshelve epose proof (Heval' := verified_malfunction_pipeline_theorem_gen P HHeap Σ wfΣ expΣ
              t0 e t0 _ [] [] _ Hnparam Normalisation s _ _ _ _ h); eauto.
            { eapply red_eval with (args:=[]); eauto. }
            2: eapply Malfunction_ind_env_empty; eauto.
            cbn in Heval'. 
            assert ((compile_malfunction_pipeline expΣ e s).2 =
                     compile_pipeline _ t0 _ expΣ e (_ ; s)).
            { Transparent compile_pipeline. reflexivity. Opaque verified_named_erasure_pipeline. }
            rewrite H7 in Heval'; clear H7. 
            unshelve eapply eval_det in H4 as [? ?]; try apply Heval'; eauto.
            2: { intros. inversion H7. }
            2: { intros; econstructor. }
            set (pt0' := precond2 _ _ _ _ _ _ _ _ _ _) in H7. clearbody pt0'.
            eapply isPure_value_vrel_eq in H7. 
            2:{
              eapply (compile_value_pure Σ); eauto. destruct s as [s].
              eapply firstorder_value_spec with (args:=[]); eauto.
              eapply PCUICWcbvEval.eval_to_value with (e:=t0).
              eapply @PCUICNormalization.wcbv_standardization_fst with (args := []); eauto.
              cbn. rewrite ReflectEq.eqb_refl. reflexivity.
              unfold irred in H6. intros []. eapply H6. eassumption.  
            }
            cbn in H7. rewrite <- H7. erewrite (ProofIrrelevance.proof_irrelevance _ pt0 pt0'). reflexivity.
            }
          }
        unfold size, size'.
        assert (Hcstr': forall b n, nth_error (ind_ctors Eind) n = Some b -> #|cstr_args b| = cstr_arity b). 
        { intros b m' Hx; assert (declared_constructor Σ (i, m') mind Eind b).
          { split; eauto. }
            erewrite <- ErasureCorrectness.declared_constructor_arity; eauto.
            eapply PCUICWeakeningEnvTyp.on_declared_constructor in H2 as [? [? ?]].
            eapply All2_In in onConstructors as [[univs onConstructor]].
            2: { eapply nth_error_In. eapply Hx. }
            eapply on_lets_in_type in onConstructor.
            now apply is_assumption_context_length.
        }         
        clear -Hcstr'. revert Hcstr' k'.  generalize (ind_ctors Eind). clear.
        induction l; eauto; cbn; intros.  
        cbn. destruct k'; cbn; eauto. pose proof (Hcstr' a 0 eq_refl).
        destruct a; cbn in *. rewrite H. destruct cstr_arity0; cbn; [| f_equal].
        eapply IHl.
        {intros; eapply Hcstr' with (n := S n); eauto. }  
        eapply IHl.
        {intros; eapply Hcstr' with (n := S n); eauto. }
        Unshelve. all:eauto.
  Qed. 

  Lemma realize_adt_value_fo {funext:Funext} {P : Pointer} {H : CompatiblePtr P P}  {HP : @Heap P} `{@CompatibleHeap P P _ _ _} 
    `{WcbvFlags} (cf:=config.extraction_checker_flags) `{EWellformed.EEnvFlags}
    univ retro univ_decl kn mind
    (Hparam : ind_params mind = [])
    (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
    (Hmono : ind_universes mind = Monomorphic_ctx)
    (Hfin : ind_finite mind == Finite )
    (Hheap_refl : forall h, R_heap h h)
    (empty_heap : heap):
    let Σ : global_env_ext_map := (build_global_env_map (mk_global_env univ [(kn , InductiveDecl mind)] retro), univ_decl) in
    forall 
      (HfoΣ : is_true (forallb (@firstorder_oneind (firstorder_env Σ) mind) (ind_bodies mind))) 
      (Hfo : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind)))
      (Hnparam : forall (i : kername) (mdecl : mutual_inductive_body),
      lookup_env Σ i = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0),
    let adt := RocqType_to_camlType mind Hparam Hfo in
    pcuic_good_for_extraction Σ ->
    forall (wfΣ : PCUICTyping.wf_ext Σ) (expΣ : PCUICEtaExpand.expanded_global_env Σ.1),
    with_constructor_as_block = true ->
    forall v ind Eind, 
    ind < List.length (snd adt) ->
    lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
    forall n, 
    realize_ADT_gen _ _ [] [] adt n [] All_nil ind v ->
    realize_value _ _ [] (to_list (realize_ADT_gen P HP [] [] adt n [] All_nil ) #|ind_bodies mind|) [] (Rel ind) v.
  Proof.
    intros ? ? ? ? ? ? wfΣ ? ? ? ? ? Hind Hlookup n Hadt. 
    pose proof (Heval := ex_intro _ n Hadt : realize_ADT P HP [] [] adt [] All_nil ind v).
    pose proof (camlValue_to_RocqValue (funext:=funext) univ retro univ_decl kn mind Hheap_refl 
                Hparam Hindices Hmono Hfin empty_heap HfoΣ Hfo Hnparam H3 wfΣ 
                expΣ H4 v ind Eind Hind Hlookup Heval) as [t [Hexp [wt [Hirred Heval']]]]; eauto.
    clear Heval; rename Heval' into Heval.  
    intros h. specialize (Heval h). eexists; exists h.
    split; eauto. intros h1 h2 v' Heval'. 
    rewrite to_list_nth. { unfold adt in Hind. cbn in Hind. now rewrite RocqType_to_camlType'_length in Hind. }
    unshelve eapply isPure_heap_irr in Heval'. 
    1: exact h.
    2: eapply compile_pure.
    2: { intros ? ? []. } 
    2: econstructor.
    unshelve eapply eval_det in Heval' as [_ Hrel]; try eapply Heval; eauto. 
    3: econstructor.
    2: { intros ? ? ? []. }
    unshelve eapply isPure_value_vrel_eq in Hrel; eauto.
    2: { unshelve eapply isPure_heap; try apply Heval; try econstructor. apply compile_pure.
          intros ? ? []. }
    now subst.
  Qed.

  Lemma firstn_length_firstn {A} (l : list A) n l' : n <= #|l| -> firstn n (firstn n l ++ l') = firstn n l.
  Proof.
    induction l in n |- *; simpl; auto.
    destruct n=> /=; auto. inversion 1. 
    destruct n=> /=; auto. intros.
    assert (n<=#|l|) by lia. now rewrite IHl.
  Qed.

Fixpoint Forall_exists T A P l
  (H : Forall (fun (t : T) => exists a : A, P t a) l) : exists l' : list A, Forall2 (fun t a => P t a) l l'.
Proof. 
destruct H.
- exists []. econstructor.
- destruct H as [p H].
  refine (let '(ex_intro l' X) := 
          Forall_exists T A P _ H0 in _).
  exists (p::l'). econstructor; eauto.
Qed. 

Lemma to_list_nth_def {A} (f : nat -> A) (size : nat) n d : 
  n >= size ->  
  nth n (to_list f size) d = d.
Proof.
  intro. apply nth_overflow. rewrite to_list_length. lia.
Qed. 

Lemma realize_term_mono {P : Pointer} {HP : @Heap P}
  (local_adt local_adt' : nat -> value -> Prop) T t k :
  (forall k v, local_adt k v -> local_adt' k v) ->
  ~~ isArrow T ->
  realize_term P HP [] (to_list local_adt k) [] T t ->
  realize_term P HP [] (to_list local_adt' k) [] T t.
Proof.
  revert T t k.
  refine (camlType_rect _ _ _ _); intros; simpl in *. 
  - inversion H2. 
  - case_eq (n <? k).
      * intro e'. apply Nat.leb_le in e'.
        rewrite to_list_nth; [lia|]. rewrite to_list_nth in H1; [lia|].
        intros h h' v. now specialize (H1 h h' v).
      * intro e'. apply Nat.ltb_ge in e'. 
        rewrite to_list_nth_def; eauto. 
        rewrite to_list_nth_def in H1; eauto. 
  - inversion H1.
Qed.

Lemma realize_ADT_mono {P : Pointer} {HP : @Heap P} n :
  forall adt ind v m (params:=[]) (paramRel:=All_nil)
  (Harrow : forall lind larg T , In lind adt ->
  In larg lind -> In T larg -> ~~ isArrow T),
  n <= m -> realize_ADT_gen_fix _ _ [] [] adt n params paramRel ind v
  -> realize_ADT_gen_fix _ _ [] [] adt m params paramRel ind v.
Proof. 
  induction n; intros ? ? ? ? ? ? ?; destruct m; intros e Hn.
  1,2: cbn in *; inversion Hn.
  1: solve [inversion e]. 
  assert (n <= m) by lia.
  cbn in *. 
  case_eq (ind <? #|adt|). 2: intro He; rewrite He in Hn; inversion Hn.
  intro He; rewrite He in Hn. eapply Nat.leb_le in He. 
  destruct Hn; [left; eauto | right].
  set (nth ind _ _) in *.  
  rewrite Existsi_spec. rewrite Existsi_spec in H0.
  destruct H0 as [k [T [? [? [[? [? ?]] ?]]]]].
  repeat eexists; eauto.
  epose proof (nth_In adt [] He).
  assert (In T y).
  { eapply nth_error_In in H4. now eapply filter_In in H4. }
  pose proof (fun A => Harrow _ _ A H5 H6).
  assert (Forall2 (fun A _ => ~~isArrow A) T x).
  { clear - H7 H3. revert x H3. induction T; intros; inversion H3; econstructor; eauto; subst.
    eapply H7. now left. eapply IHT; eauto. intros; eapply H7. cbn. now right. }
  eapply Forall2_and in H3; try apply H8. clear H7 H8.
  eapply Forall2_impl; try eapply H3.
  intros. intro h. cbn in H7. destruct H7 as [? H7].
  specialize (H7 h) as [t [h' [? ?]]]. exists t, h'; split; eauto.
  eapply realize_term_mono; try apply H9; eauto.
Qed.

Lemma RocqType_to_camlType_fo_irr Σb Σb' mind Hparam 
  (Hfo : is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind)))
  (Hfo' : is_true (forallb (@firstorder_oneind Σb' mind) (ind_bodies mind))) :       
  RocqType_to_camlType' mind Hparam Hfo = RocqType_to_camlType' mind Hparam Hfo'.
Proof.  
  destruct mind; cbn in *. 
  revert Hfo Hfo'.
  enough (forall ind_bodies1
  (Hfo : forallb
            (@firstorder_oneind Σb
               {|
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_finite := ind_finite0;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_npars := ind_npars0;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_params := ind_params0;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_bodies := ind_bodies1;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_universes := ind_universes0;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_variance := ind_variance0
               |}) ind_bodies0)
  (Hfo' : forallb
            (@firstorder_oneind Σb'
               {|
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_finite := ind_finite0;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_npars := ind_npars0;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_params := ind_params0;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_bodies := ind_bodies1;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_universes := ind_universes0;
                 PCUICExpandLetsCorrectness.T.PCUICEnvironment.ind_variance := ind_variance0
               |}) ind_bodies0),
RocqType_to_camlType_fix ind_bodies0 ind_finite0 ind_params0 ind_npars0 ind_universes0 ind_variance0 Hparam
  ind_bodies1 Hfo =
RocqType_to_camlType_fix ind_bodies0 ind_finite0 ind_params0 ind_npars0 ind_universes0 ind_variance0 Hparam
  ind_bodies1 Hfo').
  { intros; eauto. }
  
  induction ind_bodies0; cbn; intros; eauto.
  repeat destruct andb_and; cbn in *. destruct (a0 _). destruct (a1 _). clear a0 a1. 
  f_equal; eauto.
  destruct a; cbn in *.
  repeat destruct andb_and; cbn in *. destruct (a _). destruct (a0 _). clear. 
  induction ind_ctors0; cbn; eauto. destruct a. 
  repeat destruct andb_and; cbn in *. destruct (a _). destruct (a0 _). clear a a0.
  f_equal; eauto. revert i1 i3. clear. 
  set (l := rev _). clearbody l. generalize 0. induction l; cbn; intros; eauto.
  destruct a. repeat destruct andb_and; cbn in *. destruct (a _). destruct (a0 _).
  f_equal; eauto. clear. revert i2 i5. unfold firstorder_type, RocqType_to_camlType_oneind_type.
  set (PCUICAstUtils.decompose_app decl_type). clearbody p. destruct p.
  cbn; intros. destruct t; eauto. now destruct ind.
  Qed. 

Lemma filter_firstn_eq A n f (l:list A) a : 
  nth_error l n = Some a -> 
  is_true (f a) ->
  nth_error (filter f l) #|filter f (firstn n l)| = Some a.
Proof.
  revert l a. 
  induction n; intros l a eq Hf; destruct l; cbn in *; inversion eq.
  - subst. now rewrite Hf.
  - destruct (f a0) eqn:E; cbn in *.
    + now specialize (IHn _ _ eq Hf).         
    + now specialize (IHn _ _ eq Hf).
  Qed. 

Lemma subst_instance_empty_ctx (u:context) :
  test_context (closedu 0) u ->
  subst_instance [] u = u.
Proof.
  induction u; cbn; eauto. f_equal; eauto.
  destruct a. unfold map_decl; f_equal; cbn.
  - destruct decl_body; eauto; cbn.
    * move/andP => [clu]. rewrite /test_decl //= => /andP[clt clty].
      rewrite !PCUICUnivSubst.closedu_subst_instance //.
      f_equal. now apply IHu.
    * move/andP => [clu clty].
      rewrite !PCUICUnivSubst.closedu_subst_instance //.
      f_equal. now apply IHu.
Qed.

Import PCUICLiftSubst PCUICClosed.

Lemma assumption_context_rev Γ : assumption_context Γ -> assumption_context (rev Γ).
Proof.
  induction 1; cbn; try constructor.
  eapply assumption_context_app_inv; auto. repeat constructor.
Qed.

Lemma firstorder_type_closedn Σb l k T :
  ~ (isApp T) -> 
  firstorder_type (Σb := Σb) #|ind_bodies l| k T -> 
  closedn (#|ind_bodies l| + k) T.
Proof. 
  intro nApp; destruct T; try solve [inversion 1]; cbn in *; eauto.
  now destruct nApp.
Qed. 

Lemma closed_firstorder_type Σb x k tele : 
  assumption_context (rev tele) ->
  Forall (fun decl : context_decl => ~ isApp (decl_type decl)) tele ->
  alli (fun (k : nat) '{| decl_type := t |} => @firstorder_type Σb #|ind_bodies x| k t) k tele ->
  closedn_ctx (#|ind_bodies x| + k) (rev tele).
Proof.
  induction tele in k |- *; cbn; auto.
  destruct a as [na [b|] ty]; cbn.
  - move/PCUICSigmaCalculus.assumption_context_app => [asstele ass].
    depelim ass.
  - move/PCUICSigmaCalculus.assumption_context_app => [asstele ass].
    intros happ; depelim happ.
    move/andP => [hty hr]. rewrite test_context_k_app //= /test_decl /=.
    rtoProp; intuition auto.
    eapply firstorder_type_closedn; eauto.
    rewrite -Nat.add_assoc. eapply IHtele => //. now rewrite Nat.add_1_r.
Qed.

Definition no_primitive_flags :=
  {| EWellformed.has_primint := false;
     EWellformed.has_primfloat := false;
     EWellformed.has_primstring := false;
     EWellformed.has_primarray := false |}.

Lemma closed_decls_closed_ctx ctx : forallb (closed_decl 0) ctx -> closed_ctx ctx.
Proof.
  induction ctx; cbn; auto.
  move/andP=> [] cla clctx. apply /andP. split; eauto.
  eapply closed_decl_upwards; tea. lia.
Qed.

Lemma RocqValue_to_CamlValue {funext : Funext} {P : Pointer} {H : CompatiblePtr P P} 
  (cf := extraction_checker_flags) (etf := EWellformed.all_term_flags) 
  (efl := EInlineProjections.switch_no_params EWellformed.all_env_flags) 
  {has_rel : EWellformed.has_tRel} {has_box : EWellformed.has_tBox} {primFlag : EWellformed.EPrimitiveFlags}
  {HP : @Heap P} `{@CompatibleHeap P P _ _ _} `{WcbvFlags} `{EWellformed.EEnvFlags}
  univ retro univ_decl kn mind
  (Hheap_refl : forall h, R_heap h h)
  (Hparam : ind_params mind = [])
  (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
  (Hind : ind_finite mind == Finite )
  (Hmono : ind_universes mind = Monomorphic_ctx)
  (Σ0 := mk_global_env univ [(kn , InductiveDecl mind)] retro)
  (Hgood : pcuic_good_for_extraction Σ0)
  (Hfo_nil : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind))) :
  let adt := RocqType_to_camlType mind Hparam Hfo_nil in
  let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl) in
  with_constructor_as_block = true ->
  forall t ind Eind, 
(*  ind < List.length (snd adt) -> *)
  lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
  forall (wfΣ : PCUICTyping.wf_ext Σ)
  (Hnparam : forall (i : kername) (mdecl : mutual_inductive_body),
     lookup_env Σ i = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0)
  (expΣ : PCUICEtaExpand.expanded_global_env Σ)
  (expt : PCUICEtaExpand.expanded Σ [] t)
  (wt : ∥ Σ ;;; [] |- t : tInd (mkInd kn ind) []∥),
  realize_term P HP [] []
                    [(kn, realize_ADT P HP [] [] adt)] (Adt kn ind []) 
                    (compile_pipeline Σ t wfΣ expΣ expt (_ ; wt)).
Proof.
  intros ? ? ? ? ? ? Hlookup ? ? ? ? ?. cbn. rewrite ReflectEq.eqb_refl.
  intros ? ? ? Heval_compile.
  pose (H4 := Normalisation).   
  assert (Hfo : is_true (forallb (@firstorder_oneind (firstorder_env (Σ0 , univ_decl)) mind) (ind_bodies mind))).
  { assert (@firstorder_mutind (firstorder_env (Σ0 , univ_decl)) mind).
    { eapply (firstorder_mutind_ext (Σ':=(mk_global_env univ [] retro ,univ_decl))). 3: rewrite andb_and; split; eauto.
      2: eauto. 2: now destruct mind, ind_finite0. repeat econstructor. rewrite app_nil_r. reflexivity. }
    unfold firstorder_mutind in H5. now rewrite andb_and in H5. }
  assert (Hax: PCUICClassification.axiom_free Σ).
  { intros ? ? X. now inversion X. }
  assert (Hindlt : ind < #|(RocqType_to_camlType mind Hparam Hfo).2|).
  { rewrite RocqType_to_camlType'_length. unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen in Hlookup.
    destruct (lookup_env _ _); [|inversion Hlookup]. destruct g; [inversion Hlookup|].
    eapply nth_error_Some_length; eauto. cbn in Hlookup. 
    case_eq (nth_error (ind_bodies m) ind); [intros ? e | intro e] ; rewrite e in Hlookup; inversion Hlookup; subst. 
    rewrite e. reflexivity. }  
  destruct wt as [wt].
  set (i := {| inductive_mind := kn; inductive_ind := ind |}) in *.
  assert (fo : firstorder_ind Σ (firstorder_env Σ) i).
  {  unfold firstorder_ind; cbn. rewrite ReflectEq.eqb_refl.
  unfold firstorder_mutind. rewrite andb_and. split; eauto. 
  now destruct ind_finite. }
  
  unshelve epose proof (PCUICNormalization.wcbv_normalization wfΣ _ wt) as [val Heval]; eauto.
  unshelve epose proof (wval := PCUICClassification.subject_reduction_eval wt Heval).
  (* epose proof (PCUICClassification.wcbveval_red _ _ _ wt Heval). *)
  unshelve epose proof (Heval' := verified_malfunction_pipeline_theorem_gen P HP Σ wfΣ expΣ
  t expt val i [] [] fo Hnparam Normalisation (sq wt) _ _ _ _); eauto.
  2:unshelve eapply Malfunction_ind_env_empty; eauto.
  assert ((compile_malfunction_pipeline expΣ expt (sq wt)).2 =
    compile_pipeline _ t _ expΣ expt (_ ; sq wt)).
  { Transparent compile_pipeline. reflexivity. Opaque verified_named_erasure_pipeline. }
  rewrite H5 in Heval'. clear H5. 
  unshelve epose proof (Hfo' := verified_named_erasure_pipeline_fo  P HP Σ wfΣ expΣ
  t expt val i [] [] fo Normalisation (sq wt) _ _); eauto.
  assert (Hval_fo : firstorder_value Σ [] val).
  { eapply firstorder_value_spec with (args := []); eauto. 
    now eapply PCUICWcbvEval.eval_to_value. } 
  Opaque verified_named_erasure_pipeline.
  rewrite -/ Σ in Heval', Hfo'. cbn in Heval'. sq. 
  assert (Hindval : isConstruct_ind val = i).
  { pose proof (Hsub := PCUICClassification.subject_reduction_eval wt Heval).  
    eapply PCUICClassification.ind_whnf_classification with (indargs := []) in Hsub; eauto.
    2: { intro Hcof. cbn in Hcof. 
          unfold check_recursivity_kind in Hcof. cbn in Hcof. rewrite ReflectEq.eqb_refl in Hcof.
          clear - Hcof Hind. now destruct ind_finite. }
    2: { eapply PCUICClassification.eval_whne; eauto. eapply (PCUICClosedTyp.subject_closed (Γ :=[])); eauto. }
    pose proof (Hdecomp := PCUICAstUtils.mkApps_decompose_app val).
    clear Heval'. rewrite Hdecomp in wval.
    unfold PCUICAstUtils.isConstruct_app in Hsub. unfold isConstruct_ind.
    destruct (PCUICAstUtils.decompose_app val).1; inversion Hsub.
    unshelve eapply PCUICInductiveInversion.Construct_Ind_ind_eq' with (args' := []) in wval; eauto.
    repeat destruct wval as [? wval]. repeat destruct p.
    subst. reflexivity. } 
  rewrite (compile_value_mf_eq _ _ _ _ _ _ _ _ _ _ _ (sq wt)) in Heval'; eauto. 

  unshelve epose proof (Hlookup_Σ := verified_named_erasure_pipeline_lookup_env_in' _ _ _ wfΣ expΣ _ expt val
    i []
    [] fo Normalisation (sq wt) (sq Heval) Hax kn); eauto.
  
  set (Σval := (Transform.transform verified_named_erasure_pipeline (Σ, val) _).1) in *. 
  clearbody Σval. 
  symmetry in Hindval.

  specialize (Heval' h). sq. cbn in Heval_compile.

  eapply eval_det in Heval'; try exact Heval_compile; eauto.
  2: { intros ? ? ? []. }
  2: { econstructor. }
  destruct Heval' as [_ Heval'].

  epose proof (compile_pure Σ t). 
  eapply isPure_heap in H5 as [Hpure _]; eauto. 
  2: { intros ? ? []. }
  2: { intro. econstructor. }
  
  unshelve eapply isPure_value_vrel_eq in Heval'; eauto.
  clear wt t expt Heval Hlookup Eind Heval_compile Hpure Hindlt fo.
  change ind with (inductive_ind i).
  rewrite Hindval in wval. rewrite Hindval. 
  
  clear Hindval i ind.   
  revert adt wval Hfo'. subst. 

  unfold realize_ADT. enough 
  ( exists n, 
      Σ;;; [] |- val : tInd (isConstruct_ind val) [] ->
      ErasureCorrectness.firstorder_evalue_block Σval (ErasureCorrectness.compile_value_box (PCUICExpandLets.trans_global_env Σ) val []) ->
      realize_ADT_gen P HP [] [] (RocqType_to_camlType mind Hparam Hfo_nil) n [] All_nil (inductive_ind (isConstruct_ind val))
      (CompileCorrect.compile_value Σval (compile_named_value Σ val))).
  { destruct H5 as [n ?]. intros. now exists n. }

  unshelve eapply (firstorder_value_inds Σ [] (fun val => _) _ val Hval_fo). clear val Hval_fo.
  intros ? ? ? ? ? ? wtv Hargs_fo Hrec _. 

  eapply Forall_exists in Hrec as [ns Hrec]. exists (S (list_max ns)); intros wval Hfo_blocks.
  assert (u = [] /\ pandi = []).
  {
    unfold isConstruct_ind in wval. rewrite PCUICAstUtils.decompose_app_mkApps in wval; eauto.
    cbn in wval.
    unshelve epose proof (PCUICSafeLemmata.validity_wf _ _ (sq wtv)).
    destruct H5 as [? Hty].
    eapply PCUICValidity.inversion_mkApps in Hty as (? & Hty & ?).
    eapply PCUICInversion.inversion_Ind in Hty as (? & ? & ? & ? & ? & ?); eauto.
    eapply PCUICInductives.declared_inductive_type in d as Dd.
    rename d into d0.
    cbn in d0. unfold Σ0 in d0. destruct d0.
    cbn in H5. destruct H5; try tauto. invs H5.
    rewrite Hmono in c. cbn in c. destruct u; cbn in *; try lia. split; auto.
    rewrite Dd in w.
    rewrite Hparam in w.
    eapply nth_error_forall in H6.
    2: eauto. cbn in H6. rewrite H6 in w. cbn in w.
    invs t. reflexivity.
    exfalso.
    eapply PCUICConversion.ws_cumul_pb_Sort_Prod_inv.
    etransitivity; eassumption.
  }
  destruct H5; subst. assert (Hindlt: inductive_ind i <? #|RocqType_to_camlType' mind Hparam Hfo_nil|).
  {
    rewrite RocqType_to_camlType'_length. 
    eapply PCUICInductiveInversion.Construct_Ind_ind_eq' with (args' := []) in wval; eauto.
    repeat destruct wval as [? wval]. repeat destruct p.
    subst. simpl in *.
    destruct d as [[dx dx0] d]. cbn in dx, dx0, d. 
    revert dx dx0; intros. destruct dx as [dx|dx]; inversion dx. subst.
    apply leb_correct. eapply nth_error_Some_length; eauto.
  }
  cbn. unfold isConstruct_ind. 
  epose proof (Hdecomp := PCUICAstUtils.decompose_app_mkApps (tConstruct i n ui) args).
  forward Hdecomp; eauto.
  rewrite Hdecomp Hindlt. 
  
  set (tv := mkApps (tConstruct i n ui) args) in *. 

  unfold tv in wval.  
  eapply PCUICInductiveInversion.Construct_Ind_ind_eq' with (args' := []) in wval; eauto.
  repeat destruct wval as [? wval]. repeat destruct p.
  subst. simpl in *.
  destruct d as [[dx dx0] d]. cbn in dx, dx0, d. 
  destruct dx as [dx | dx]; inversion dx. symmetry in H6. subst. clear dx.
  rewrite Hparam in s. inversion s. inversion inst_subslet0. subst. 
  clear x4 x5 s1 s2 s spine_dom_wf inst_ctx_subst inst_subslet c c0. 
  erewrite Hnparam in s0. 2: cbn ; now erewrite ReflectEq.eqb_refl.
  rewrite Hparam in s0. cbn in s0. rewrite skipn_0 in s0.
  eapply PCUICSpine.spine_subst_ctx_inst in s0.  

  inversion Hfo_blocks as [? ? ? Hlookup' HForall_fo Heq]. clear Hfo_blocks.
  unfold tv, compile_named_value in Heq.  erewrite compile_value_box_mkApps in Heq. cbn in Heq.
  unfold ErasureCorrectness.pcuic_lookup_inductive_pars, EGlobalEnv.lookup_constructor_pars_args, 
  EGlobalEnv.lookup_constructor, EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *. 
  cbn in Hlookup'.
  set (EGlobalEnv.lookup_env _ _) in Hlookup'.  
  case_eq o. 2: { intro X0. rewrite X0 in Hlookup'. inversion Hlookup'. }
  intros g Hg; rewrite Hg in Hlookup'. 
  destruct g. { inversion Hlookup'. }   
  cbn in *. rewrite ReflectEq.eqb_refl in Heq; inversion Heq.
  subst. clear Heq. unfold o in Hg. cbn in *. 
  pose proof (Hdecl := Hg).
  eapply Hlookup_Σ in Hg as [decl' [Hlookup_decl Hdecl']]. rewrite ReflectEq.eqb_refl in Hlookup_decl. cbn in Hdecl'. 
  destruct decl'; [inversion Hdecl'|].   
  inversion Hlookup_decl. subst. clear Hlookup_decl.
  cbn in Hlookup'. rewrite map_mapi nth_error_mapi in Hlookup'.

  rewrite RocqType_to_camlType'_length.
  assert (Hind' : inductive_ind i <? #|ind_bodies x|). 
  { now rewrite RocqType_to_camlType'_length in Hindlt. }
  case_eq (nth_error (ind_bodies x) (inductive_ind i)).
  2:{ intro Hnone. rewrite Hnone in Hlookup'. inversion Hlookup'. }
  intros indbody Hindbody. rewrite Hindbody in Hlookup'.
  assert (x0 = indbody). { now clear -dx0 Hindbody. } subst.

  assert (Hcstr_gen: forall b n, nth_error (ind_ctors indbody) n = Some b -> 
    is_assumption_context (cstr_args b) /\
    test_context (closedu 0) (cstr_args b) /\
    forallb (closed_decl 0) (subst_context (inds (inductive_mind i) [] (ind_bodies x)) 0 (cstr_args b)) /\
    #|cstr_args b| = cstr_arity b /\
    Forall (fun decl => ~ (isApp (decl_type decl))) (cstr_args b)
  ). 
  { intros cstr m Hx; assert (declared_constructor Σ (i, m) x indbody cstr).
    { split; eauto. split; eauto. simpl. now left. }
    eapply PCUICWeakeningEnvTyp.on_declared_constructor in H5 as [? [? ?]].
    eapply All2_In in onConstructors as [[univs onConstructor]].
      2: { now eapply nth_error_In. } 
    have isa: is_assumption_context (cstr_args cstr).
    { now eapply on_lets_in_type in onConstructor. }
    split => //.
    split; revgoals.
    assert (happ : Forall (fun decl : context_decl => ~ isApp (decl_type decl)) (cstr_args cstr)).
    { clear -cf wfΣ Hfo Hindbody Hx.
      eapply All_Forall, firstorder_con_notApp.
      eapply forallb_nth_error in Hfo. 
      erewrite Hindbody in Hfo; cbn in Hfo.
      move/andP: Hfo => [hf _].
      eapply forallb_nth_error in hf. 
      erewrite Hx in hf; cbn in hf; tea. }
    split; [|split] => //.
    { clear -isa Hfo Hindbody Hx Hparam happ.
      eapply forallb_nth_error in Hfo. 
      erewrite Hindbody in Hfo; cbn in Hfo.
      move/andP: Hfo => [hf _].
      eapply forallb_nth_error in hf. 
      erewrite Hx in hf; cbn in hf; tea.
      rewrite /firstorder_con in hf.
      rewrite rev_app_distr alli_app in hf.
      move/andP: hf => [] _.
      rewrite Hparam /= => hargs.
      eapply alli_Alli, Alli_rev_All_fold in hargs. cbn in hargs.
      induction hargs. trivial.
      rewrite subst_context_snoc /=.
      apply /andP. split. depelim happ; cbn in isa; destruct d as [na [b|] ty]; cbn in isa; eauto.
      rewrite /test_decl /= Nat.add_0_r.
      eapply firstorder_type_closed_gen => //; tea.
      cbn.
      depelim happ. cbn in isa. destruct d as [na [def|] ty]; cbn in isa; eauto. }
    destruct onConstructor.
    { eapply is_assumption_context_length in isa. congruence. }
    
    destruct onConstructor.
    rewrite Hmono in on_cargs.
    clear -isa on_cargs wfΣ.
    induction (cstr_args cstr) in univs, on_cargs, isa |- *; cbn; auto.
    cbn in on_cargs.
    destruct a => //. destruct decl_body => //.
    destruct univs => //. destruct on_cargs as [onca hty].
    rewrite (IHc univs) //=; cbn.
    hnf in hty. destruct hty as [onb [s [onty eq]]]. cbn in *. destruct eq as [eqs _]; try subst s.
    eapply typing_wf_universes in onty => //. 2:apply wfΣ.
    move/andP: onty => [hdecl _]. unshelve eapply wf_universes_closedu in hdecl => //; tea. eapply wfΣ.
    red. cbn. intro. csets. }
  assert (Hcstr: forall x n, nth_error (ind_ctors indbody) n = Some x -> #|cstr_args x| = cstr_arity x). 
  { now intros b m hx; eapply Hcstr_gen in hx as [hctx []]. }
  cbn in Hlookup'. repeat rewrite nth_error_map in Hlookup'. 
  rewrite d in Hlookup'. cbn in Hlookup'.
  destruct args. 
  - left. cbn in *. unfold ErasureCorrectness.pcuic_lookup_inductive_pars. cbn. rewrite ReflectEq.eqb_refl. cbn. 
    unfold Compile.lookup_constructor_args, EGlobalEnv.lookup_constructor, EGlobalEnv.lookup_inductive, 
    EGlobalEnv.lookup_minductive. cbn. rewrite Hdecl. cbn.   
    rewrite nth_error_map nth_error_mapi.  rewrite Hindbody. cbn. erewrite Hnparam. 
    2: now erewrite ReflectEq.eqb_refl. rewrite skipn_0. cbn. 
    assert (forall l, 
      (forall x n, nth_error l n = Some x -> #|cstr_args x| = cstr_arity x) ->
      #|filter (fun x : nat => match x with | 0 => true | S _ => false end)
    (map EAst.cstr_nargs
    (map (fun cdecl : constructor_body => {| Extract.E.cstr_name := cstr_name cdecl; Extract.E.cstr_nargs := cstr_arity cdecl |})
    (map (PCUICExpandLets.trans_constructor_body (inductive_ind i) x) l)))| = 
    #|filter (fun x : nat => match x with | 0 => true | S _ => false end) (map cstr_nargs l)|).
    {
      induction l; intros Hl; [eauto|cbn in *]. 
      assert (cstr_arity a = #|cstr_args a|). { symmetry; now eapply (Hl _ 0). }
      destruct a; cbn in *.   
      rewrite <- H5. destruct cstr_arity0; cbn; [f_equal |]; eapply IHl. 
      all: intros; now eapply (Hl _ (S n0)). 
    }
    repeat rewrite firstn_map. erewrite H5; eauto.
    2: { intros. eapply (Hcstr _ n0). now eapply MRList.nth_error_firstn. }
    rewrite -firstn_map. clear H5. 
    unshelve erewrite filter_length_nil. 5:eauto. 4:eauto. eauto.
    assert (RocqType_to_camlType' x Hparam Hfo = RocqType_to_camlType' x Hparam Hfo_nil) by apply RocqType_to_camlType_fo_irr.
    rewrite -H5. clear H5.  
    unshelve erewrite RocqType_to_camlType'_nth.
    4: eauto. 3: { now apply Nat.leb_le. }
    { eapply nth_error_forallb; eauto. } 
    pose proof (Hx1 := d).
    unshelve eapply RocqType_to_camlType_oneind_nth' in d as [l' [d ?]]; eauto.  
    2: eapply nth_error_forallb; eauto. 
    pose proof (Hd := PCUICReduction.nth_error_firstn_skipn d).
    rewrite Hd.
    set (RocqType_to_camlType_oneind _ _ _ _) in *.
    rewrite firstn_length_firstn. { eapply nth_error_Some_length in d. lia. } 
    assert (l' = []). 
    { apply length_zero_iff_nil. inversion Hlookup'. rewrite H5. 
      erewrite Hnparam in H7. 2: now erewrite ReflectEq.eqb_refl.
      rewrite skipn_0 in H7. erewrite Hcstr; eauto. }  
    set (k := #|_|). set (f := fun x : list camlType => _). set (ll := _ ++ _).
    epose proof (filter_firstn' _ k f ll) as [? [_ [? [? [? [? ?]]]]]].
    { unfold k, f, ll. rewrite filter_app. cbn. rewrite H6. rewrite length_app. cbn. lia. }
    apply Existsi_spec. repeat eexists; cbn; try lia.
    unfold k, f, ll. rewrite filter_app. cbn. subst. rewrite length_app. cbn. lia.
    rewrite Nat.sub_0_r. eauto. 

  - set (args' := t :: args) in *. unfold tv.
    right. cbn in Hlookup'.  erewrite Hnparam, skipn_0 in Hlookup'.
    2: now erewrite ReflectEq.eqb_refl. cbn in Hlookup'.
    unfold compile_named_value. erewrite compile_value_box_mkApps. cbn.
    unfold ErasureCorrectness.pcuic_lookup_inductive_pars. cbn. rewrite ReflectEq.eqb_refl. cbn. 
    unfold Compile.lookup_constructor_args, EGlobalEnv.lookup_constructor,
    EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive. cbn. rewrite Hdecl. cbn.   
    rewrite nth_error_map nth_error_mapi. rewrite Hindbody. cbn. erewrite Hnparam, skipn_0.
    2: now erewrite ReflectEq.eqb_refl. cbn. 
    assert (RocqType_to_camlType' x Hparam Hfo = RocqType_to_camlType' x Hparam Hfo_nil) by apply RocqType_to_camlType_fo_irr.
    rewrite -H5. clear H5.
    unshelve erewrite RocqType_to_camlType'_nth.
    4: eauto. 3: { now apply Nat.leb_le. }
    { eapply nth_error_forallb; eauto. }
    pose proof (Hx1 := d).

    unshelve eapply RocqType_to_camlType_oneind_nth' in d as [l' [d ?]]; eauto.  
    2: eapply nth_error_forallb; eauto.
    
    assert (forall l, 
    (forall x n, nth_error l n = Some x -> #|cstr_args x| = cstr_arity x) ->
    #|filter (fun x : nat => match x with | 0 => false | S _ => true end)
    (map EAst.cstr_nargs
    (map (fun cdecl : constructor_body => {| Extract.E.cstr_name := cstr_name cdecl; Extract.E.cstr_nargs := cstr_arity cdecl |})
    (map (PCUICExpandLets.trans_constructor_body (inductive_ind i) x) l)))| = 
    #|filter (fun x : nat => match x with | 0 => false | S _ => true end) (map cstr_nargs l)|).
    {
      induction l; intros Hl; [eauto|cbn in *]. 
      assert (cstr_arity a = #|cstr_args a|). { symmetry; now eapply (Hl _ 0). }
      destruct a; cbn in *. rewrite <- H6. destruct cstr_arity0; cbn; [|f_equal]; eapply IHl. 
      all: intros; now eapply (Hl _ (S n0)).
    }
    repeat rewrite firstn_map. erewrite H6.
    2: { intros. eapply (Hcstr _ n0). now eapply MRList.nth_error_firstn. }      
    rewrite -firstn_map. clear H6. 
    unshelve erewrite filter_length_not_nil. 4,5,7:eauto.

    unshelve erewrite RocqType_to_camlType'_nth.
    4: eauto. 3: { now apply Nat.leb_le. }
    { eapply nth_error_forallb; eauto. }

    pose proof (Hd := PCUICReduction.nth_error_firstn_skipn d).
    rewrite Hd.

    set (RocqType_to_camlType_oneind _ _ _ _) in *.
    rewrite firstn_length_firstn. { eapply nth_error_Some_length in d. lia. }
    set (k := #| _ |). set (f := fun x : list camlType => _) in *. set (ll := _ ++ _) in *.
    destruct l'. { 
      inversion Hlookup'. 
      erewrite Hcstr in H5; eauto. 
      rewrite - H5 in H7. inversion H7. } 
    apply Existsi_spec. repeat eexists; cbn; try lia.
    { unfold k, f, ll. rewrite filter_app. cbn. rewrite length_app. cbn. lia. }
    2: { rewrite Nat.sub_0_r. rewrite <- Hd. now eapply filter_firstn_eq. }
    clear k ll Hd f H5. cbn.
    revert Hrec. intros. repeat rewrite map_map. rewrite - (map_cons _ t args).
    rewrite Forall2_map_right.  fold args'.
    assert (realize_ADT_gen_fix P HP [] [] (RocqType_to_camlType' x Hparam Hfo) (list_max ns) [] All_nil = 
    realize_ADT_gen P HP [] [] (RocqType_to_camlType x Hparam Hfo) (list_max ns) [] All_nil) by reflexivity.
    rewrite H5. clear H5. 
    revert s0 dx0; intros.
    assert (Forall (fun v =>  ∥Σ;;; [] |- v : tInd (isConstruct_ind v) []∥) args').
    {
      eapply typing_tConstruct_fo in Hargs_fo. eapply Forall_impl; eauto.
      cbn; intros ? [? [? ?]]. sq.
      enough (x0 = nil /\ x2 = nil) as [-> ->] by assumption.
      unshelve epose proof (PCUICSafeLemmata.validity_wf _ _ _).
      4:{ sq. eassumption. }
      destruct H6 as [? Hty].
      eapply PCUICValidity.inversion_mkApps in Hty as (? & Hty & ?).
      eapply PCUICInversion.inversion_Ind in Hty as (? & ? & ? & ? & ? & ?); eauto.
      eapply PCUICInductives.declared_inductive_type in d0 as Dd.
      cbn in d0. unfold Σ0 in d0. destruct d0.
      cbn in H6. destruct H6; try tauto. invs H6.
      destruct i. cbn in H9. subst.
      rewrite Hmono in c0. cbn in c0. destruct x0; cbn in *; try lia. split; auto.
      rewrite Dd in w.
      rewrite Hparam in w.
      eapply nth_error_forall in H7.
      2: eauto. cbn in H7. rewrite H7 in w. cbn in w.
      invs t0. reflexivity.
      exfalso.
      eapply PCUICConversion.ws_cumul_pb_Sort_Prod_inv.
      etransitivity; eassumption.
    }
    assert (Forall2 (fun T v => T = (Rel (inductive_ind (isConstruct_ind v)))) (c ::l') args').
    { unfold l in d. clear wtv Hrec. revert dx0; intros.
      eapply RocqType_to_camlType_oneind_nth_ctors in d as [Hfo_x d].
      destruct i; cbn in *. 
      apply RocqType_to_camlType_ind_ctors_nth in d as [a' [d [? d']]].
      rewrite Hx1 in d. noconf d. rewrite d'. clear d'.
      revert x0; rewrite Hparam app_nil_r; intro. rewrite PCUICLiftSubst.subst0_context in s0.
      rewrite - PCUICSpine.subst_telescope_subst_context in s0.
      assert (ui = []).
      {
        revert c1. intros. unfold Σ in c1. unfold Σ0 in c1.
        cbn in c1. red in c1. red in c1. cbn in c1.
        unfold lookup_env in c1. cbn in c1.
        unfold lookup_inductive_gen, lookup_minductive_gen in c1. cbn in c1.
        rewrite eq_kername_refl in c1. rewrite dx0 in c1.
        unfold compare_universe in c1. cbn in c1. red in c1.
        destruct destArity as []; cbn in *.
        destruct p; cbn in *.
        destruct Nat.leb.
        destruct ind_variance.  inversion c1.
        red in H6. inversion H6. reflexivity.
        inversion H6. reflexivity.
        inversion c1. reflexivity.
        inversion c1. reflexivity.
        inversion c1. reflexivity.
      } subst. cbn in s0.
      specialize (Hcstr_gen _ _ Hx1) as [assargs [cluargs [hclosed [lenargs argsapp]]]].
      rewrite subst_instance_empty_ctx // in s0.
      eapply Prelim.is_assumption_context_spec in assargs.
      eapply assumption_context_rev in assargs.
      eapply Forall_rev in argsapp.
      pose proof Hfo_nil.
      eapply forallb_nth_error in H6. erewrite dx0 in H6. cbn in H6.
      move/andP: H6 => [] hfo _. eapply forallb_nth_error in hfo.
      erewrite Hx1 in hfo. cbn in hfo. unfold firstorder_con in hfo.
      rewrite rev_app_distr alli_app in hfo. move/andP: hfo => [] _ hargs.
      cbn in hargs. rewrite length_rev in hargs. rewrite Hparam //= in hargs.
      rewrite -[cstr_args x1]List.rev_involutive in hclosed.
      (* eapply alli_Alli in hargs. *)
      (* eapply Alli_rev_All_fold in hargs. cbn in hargs. *)
      generalize hclosed hargs x0 s0.
      generalize 0 at 2 3 4 5 6.
      generalize args' assargs argsapp H5.
      clear -Hx1 dx0 wfΣ.
      set (l0 := rev _).
      induction l0; intros.
      1:{ inversion s0. subst. constructor. }
      destruct a; cbn -[subst_telescope] in *.
      destruct decl_body; cbn -[subst_telescope] in *; [now depelim assargs|].
      set (decl := {| decl_name := _ |}) in s0.
      assert ((decl :: l0) = List.rev (List.rev l0 ++ [decl])). 
      { rewrite rev_app_distr. cbn. now rewrite rev_involutive. }
      rewrite H in s0.
      rewrite PCUICSpine.subst_telescope_subst_context in s0.
      rewrite subst_context_app rev_app_distr in s0.
      rewrite /decl {1}/rev //= in s0.
      depelim s0. cbn in t0.
      destruct andb_and. destruct a. clear a i0.
      econstructor. 
        + inversion H5; subst. sq.
          destruct decl_type; cbn in i1; try solve [inversion i1]; cbn.
          * cbn in *. eapply andb_and in i1 as [? ?]. rewrite H0 H1 /= in x0 t0.
            eapply leb_complete in H0, H1. rewrite nth_error_inds in t0; [lia| cbn in t0].
            f_equal. 
            eapply (PCUICPrincipality.principal_type_ind (args:=[]) (args':=[])) in H2; eauto.
            destruct H2 as [_ e]. now rewrite - e. 
          * cbn in i1. move/andP: x0 => [] fo.
            depelim argsapp. now cbn in H.
          * destruct ind. now cbn in *. 
        + depelim H5. eapply IHl0; eauto.
          - now depelim assargs.
          - now depelim argsapp. 
          - rewrite subst_context_app in hclosed.
            rewrite forallb_app in hclosed.
            move/andP: hclosed => []. len. rewrite //=.
          - now move/andP: hargs => [].
          - rewrite -PCUICSpine.subst_telescope_subst_context rev_involutive in s0.
            set (sinds := subst_telescope (inds _ _ _) _ _) in *.
            enough (subst_telescope [i] 0 sinds = sinds). now rewrite H1 in s0.
            assert (closedn_ctx 0 (rev sinds)).
            rewrite subst_context_app in hclosed.
            rewrite forallb_app in hclosed.
            move/andP: hclosed => []. len. cbn.
            rewrite PCUICSpine.subst_context_subst_telescope.
            intros clr _. rewrite /sinds. now eapply closed_decls_closed_ctx.
            apply PCUICExpandLetsCorrectness.rev_inj.
            rewrite -PCUICSpine.subst_context_subst_telescope.
            rewrite PCUICSpine.closed_k_ctx_subst //. }
    enough 
    (Forall
      (fun (y : term) =>
      ∥Σ;;; [] |- y : tInd (isConstruct_ind y) []∥ ->
      realize_value P HP []
        (to_list (realize_ADT_gen P HP [] [] (RocqType_to_camlType x Hparam Hfo) (list_max ns) [] All_nil)
          #|ind_bodies x|) [] (Rel (inductive_ind (isConstruct_ind y)))
        (CompileCorrect.compile_value Σval            
          (eval_fo (ErasureCorrectness.compile_value_box (PCUICExpandLets.trans_global_env Σ0) y [])))) args').
    {
      eapply Forall_mix in H7; try apply H5. clear H5.  
      eapply Forall2_Forall_mix; [| apply H7]. eapply Forall2_impl; eauto. 
      cbn; intros. destruct H8; subst; eauto.
    }
    eapply Forall2_sym in Hrec. 
    assert (Forall
    (fun (y : term) =>
      ErasureCorrectness.firstorder_evalue_block
        Σval
        (ErasureCorrectness.compile_value_box (PCUICExpandLets.trans_global_env Σ0) y []) ->
      realize_ADT_gen P HP [] [] (RocqType_to_camlType x Hparam Hfo_nil) (list_max ns) [] All_nil
        (inductive_ind (isConstruct_ind y))
        (CompileCorrect.compile_value Σval (compile_named_value Σ y))) args').
    { clear - H5 Hrec. 
      unfold RocqType_to_camlType. cbn. set (list_max _).  
      assert (list_max ns <= n) by lia. clearbody n.
      revert n H. induction Hrec; simpl; econstructor. 
      - intros. inversion H5. subst. destruct H4.   
        eapply realize_ADT_mono; try eapply H; eauto; [|lia]. 
        eapply RocqType_to_camlType'_fo. 
      - inversion H5. subst. eapply IHHrec; eauto. lia. }
    clear Hrec; rename H7 into Hrec. revert HForall_fo; intro.
    erewrite Hnparam , skipn_0 in HForall_fo. 2: now erewrite ReflectEq.eqb_refl.
    apply Forall_map_inv in HForall_fo.
    eapply Forall_mix in Hrec; try apply HForall_fo.
    eapply Forall_mix in Hrec; try apply H5. clear HForall_fo H5.    
    eapply Forall_impl; eauto. clear Hrec. intros ? [HForall_fo Hrec]. 
    assert (RocqType_to_camlType x Hparam Hfo = RocqType_to_camlType x Hparam Hfo_nil).
    { unfold RocqType_to_camlType; f_equal. apply RocqType_to_camlType_fo_irr. }
    rewrite H5; clear H5.
    assert (Hind_bodies :inductive_ind (isConstruct_ind a) < #|ind_bodies x|).
    { sq. eapply PCUICValidity.validity in HForall_fo as [_ [? [Hty _]]].
      eapply PCUICInversion.inversion_Ind in Hty as [? [? [? [? [? ?]]]]]; eauto.
    destruct d0. eapply nth_error_Some_length in H7. 
    assert (x = x2). { destruct H5; inversion H5; eauto. }
    now subst. }
    case_eq (nth_error (ind_bodies x) (inductive_ind (isConstruct_ind a))).
    2: { intro HNone. 
        eapply nth_error_Some in HNone; eauto. }
    intros Eind' He [wa].  
    unshelve eapply realize_adt_value_fo; cbn; eauto.
    now rewrite RocqType_to_camlType'_length.
    unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen. cbn. 
    rewrite ReflectEq.eqb_refl. now rewrite He.
    apply Hrec; eauto. now destruct Hrec.
  Qed.
    

  Lemma RocqValue_to_CamlValue' {funext : Funext} {P : Pointer} {H : CompatiblePtr P P} (cf := extraction_checker_flags)
  (etf := EWellformed.all_term_flags) (efl := EInlineProjections.switch_no_params EWellformed.all_env_flags)  {has_rel : EWellformed.has_tRel} {has_box : EWellformed.has_tBox}  
  {HP : @Heap P} `{@CompatibleHeap P P _ _ _} `{WcbvFlags} `{EWellformed.EEnvFlags}
  univ retro univ_decl kn mind
  (Hheap_refl : forall h, R_heap h h)
  (Hparam : ind_params mind = [])
  (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
  (Hind : ind_finite mind == Finite )
  (Hmono : ind_universes mind = Monomorphic_ctx)
  (Σ0 := mk_global_env univ [(kn , InductiveDecl mind)] retro)
  (Hgood : pcuic_good_for_extraction Σ0)
  (Hfo_nil : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind))) :
  let adt := RocqType_to_camlType mind Hparam Hfo_nil in
  let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl) in
  with_constructor_as_block = true ->
  forall t ind Eind, 
(*  ind < List.length (snd adt) -> *)
  lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
  forall (wt : ∥Σ ;;; [] |- t : tInd (mkInd kn ind) []∥)
  (Hnparam : forall (i : kername) (mdecl : mutual_inductive_body),
     lookup_env Σ i = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0)
  wfΣ (expΣ : PCUICEtaExpand.expanded_global_env Σ)
  (expt : PCUICEtaExpand.expanded Σ [] t),
  forall h v, R_heap h h ->
    eval [] empty_locals h (compile_pipeline Σ t wfΣ expΣ expt (_ ; wt)) h v
    -> realize_ADT _ _ [] [] adt [] All_nil ind v.
  Proof.
    intros ? ? ? ? ? ? Hlookup wt ? ? ? ? ? ? ? Heval. 
    unshelve epose proof (Hreal := RocqValue_to_CamlValue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); eauto.
    eapply etf. 
    cbn in Hreal. rewrite ReflectEq.eqb_refl in Hreal; eauto.
  Qed. 
    
From Malfunction Require Import CompileCorrect Pipeline. 

Lemma verified_named_erasure_pipeline_irrel `{Heap} p precond precond' : 
  Transform.transform verified_named_erasure_pipeline p precond = Transform.transform verified_named_erasure_pipeline p precond'.
  assert (precond = precond') by apply ProofIrrelevance.proof_irrelevance. now subst.
Qed.

Lemma compile_pipeline_eq {H : Pointer} {H0 : Heap} {Σ} {t wfΣ expΣ expt pre} : 
  compile_pipeline Σ t wfΣ expΣ expt pre = 
  (compile_malfunction_pipeline expΣ expt pre.π2 (Normalisation:=Normalisation)).2.
Proof. reflexivity. Qed.

Lemma compile_malfunction_pipeline_eq {H : Pointer} {H0 : Heap} {Σ : global_env_ext_map} {t wfΣ expΣ expt} {pre : sigT (fun T => ∥ Σ ;;; [] |- t : T ∥)} {Normalisation} : 
  compile_malfunction_pipeline (T:=pre.π1) expΣ expt pre.π2 (Normalisation:=Normalisation) = 
  Transform.transform verified_malfunction_pipeline (Σ, t) (precond Σ t pre.π1 wfΣ expΣ expt pre.π2 Normalisation).
Proof. reflexivity. Qed.

Opaque compile_pipeline compile_malfunction_pipeline.

Lemma compile_compose {funext:Funext} {P:Pointer} {H:Heap} {HP : @CompatiblePtr P P} (efl := extraction_env_flags)
  {HH : @CompatibleHeap _ _ _ H H} 
  (Hvrel_refl : forall v, vrel v v)
  (Hheap_refl : forall h, R_heap h h)
  `{WcbvFlags} (cf:=config.extraction_checker_flags) 
  h h' t u' u v w A B univ univ_decl kn mind retro na
  (Σ0 := mk_global_env univ [(kn , InductiveDecl mind)] retro)
  (Hgood : pcuic_good_for_extraction Σ0)
  (Hfo : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind))):
  let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl) in
  forall
  (Hax : PCUICClassification.axiom_free Σ) 
  wfΣ expΣ expt (wt : ∥Σ ;;; [] |- t : tProd na A B∥) expu (wu : ∥Σ ;;; [] |- u : A∥),
  ∥Extract.nisErasable Σ [] t∥ -> 
  ∥Extract.nisErasable Σ [] (tApp t u)∥ -> 
  eval [] empty_locals h (compile_pipeline Σ u wfΣ expΣ expu (_ ; wu)) h v ->
  eval [] empty_locals h u' h' v ->
  eval [] empty_locals h (Mapply (compile_pipeline Σ t wfΣ expΣ expt (_ ; wt),[u'])) h' w ->
  exists exptu wtu w' ,
      vrel w w' /\ 
      eval [] empty_locals h (compile_pipeline Σ (tApp t u) wfΣ expΣ exptu (B {0 := u}; wtu)) h w'.
Proof.
  intros ? ? ? ? ? ? ? ? Herase_t Herase Hu Hu' Happ.
  assert (exptu : PCUICEtaExpand.expanded Σ.1 [] (tApp t u)).
  { now eapply PCUICEtaExpand.expanded_tApp. }
  assert (wtu : ∥ Σ;;; [] |- tApp t u : B {0 := u} ∥).
  { clear Hu Hu' Happ. sq.  eapply PCUICValidity.type_App'; eauto. }
  exists exptu, wtu.
  rewrite compile_pipeline_eq compile_malfunction_pipeline_eq. 
  set (precond _ _ _ _ _ _ _ _).
  pose proof (compile_malfunction_pipeline_app _ _ _ _ _ p Herase expt) as [pre' [pre'' Happeq]].
  rewrite Happeq. clear Happeq.   
  inversion Happ; subst. 
  - epose proof (compile_pure _ t).
    eapply isPure_heap in H1 as [Hfpure heq]; eauto.
    2: { intros ? ? []. }
    2: { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto.  }
    symmetry in heq; subst. pose proof (Hu_copy := Hu).
    eapply isPure_heap in Hu as [Hvpure _]; try eapply compile_pure; intros; cbn in *; eauto.
    eapply eval_det in Hu' as [? ?]; eauto. 3: econstructor.
    2: intros ? ? ? Hempty; inversion Hempty.
    destruct Hfpure as [? Hepure]. eapply isPure_heap_irr with (h'':=h) in H8; eauto.
    2: { intros ? ? []. } 
    2: { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto. 
         eapply isPure_value_vrel'; eauto. }
    eapply eval_sim with (iglobals := []) in H8 as [[h'' [w' [? [? ?]]]]]; eauto.
    2: { eapply vrel_add; eauto. intro. eauto. }
    exists w'. split; eauto. eapply Mapply_u_eval. { eapply compile_app_not_nil. }
    eapply eval_app_sing.
     3: eapply isPure_heap_irr; eauto.
     3: { intros ? ? []. }
     3: { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto. }
    unfold Transform.run, time.
    rewrite compile_pipeline_eq compile_malfunction_pipeline_eq in H3.
    unfold verified_malfunction_pipeline in H3.
    revert H3. destruct_compose. intros. cbn in H9. erewrite verified_named_erasure_pipeline_irrel.  exact H9.
    rewrite compile_pipeline_eq compile_malfunction_pipeline_eq /verified_malfunction_pipeline in Hu_copy.
    revert Hu_copy. destruct_compose. intros. cbn in Hu_copy.
    erewrite verified_named_erasure_pipeline_irrel. exact Hu_copy. 
  - epose proof (compile_pure _ t).
    eapply isPure_heap in H1 as [Hfpure heq]; eauto.
    2: { intros ? ? []. }
    2: { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto. }
    symmetry in heq; subst. pose proof (Hu_copy := Hu).
    eapply isPure_heap in Hu as [Hvpure _]; try eapply compile_pure; intros; cbn in *; eauto.
    eapply eval_det in Hu' as [? ?]; eauto. 3: econstructor.
    2: intros ? ? ? Hempty; inversion Hempty.
    destruct Hfpure as [? Hepure]. 
    assert (isPure e).
    { rewrite nth_nth_error in H6. 
      eapply (nth_error_forall (n := n)) in Hepure; cbn in *; eauto.
      2: destruct nth_error; inversion H6; subst; eauto.
      eauto. }
    eapply isPure_heap_irr with (h'':=h) in H9; eauto.
    2: { intros ? ? []. }
    2: { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto. 
         eapply isPure_value_vrel'; eauto.
         eapply isPure_add_self; eauto. }
    eapply eval_sim with (iglobals := []) in H9 as [[h'' [w' [? [? ?]]]]]; eauto.
    2: { eapply vrel_add; eauto. intro. eauto. }
    sq. exists w'. split; eauto. 
    eapply Mapply_u_eval. { eapply compile_app_not_nil. }
    eapply eval_app_sing_rec. 3: eauto. 
     3: eapply isPure_heap_irr; eauto.
     3: { intros ? ? []. }
     3: { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto. 
          eapply isPure_add_self; eauto. }
    unfold Transform.run, time.
    rewrite compile_pipeline_eq compile_malfunction_pipeline_eq /verified_malfunction_pipeline in H3.
    revert H3. destruct_compose. intros. cbn in H11. erewrite verified_named_erasure_pipeline_irrel. exact H11.
    rewrite compile_pipeline_eq compile_malfunction_pipeline_eq /verified_malfunction_pipeline in Hu_copy.
    revert Hu_copy. destruct_compose. intros. cbn in Hu_copy. erewrite verified_named_erasure_pipeline_irrel. exact Hu_copy. 
  - pose Normalisation. unshelve erewrite compile_function in H7. 17: exact Herase_t. 
    6,7,8,9:eauto. 7,10:eauto. 4: unshelve eapply Malfunction_ind_env_empty.
    7:eauto. all:eauto. inversion H7. intros ? ? ? [].
Qed.
  
From MetaRocq.PCUIC Require Import PCUICWellScopedCumulativity. 

Lemma Prod_ind_irred `{checker_flags} Σ Γ f na kn ind ind' X :
  let PiType := tProd na (tInd (mkInd kn ind) []) (tInd (mkInd kn ind') []) in
  wf_ext Σ ->
  Σ ;;; Γ |- f : PiType ->
  Σ ;;; Γ ⊢ PiType ⇝ X ->
  PiType = X.
Proof.
  intros ? ? Hf Hred. 
  eapply PCUICConversion.invert_red_prod in Hred as [A' [B' [? [? ?]]]]; subst.
  unfold PiType. f_equal. 
  - eapply PCUICReduction.red_rect'; eauto. intros; subst.
    eapply PCUICNormal.red1_mkApps_tInd_inv with (v:=[]) in X1 as [? [? ?]]; subst.
    inversion o.
  - eapply PCUICReduction.red_rect'; eauto. 2: eapply c. intros; subst.
    eapply PCUICNormal.red1_mkApps_tInd_inv with (v:=[]) in X1 as [? [? ?]]; subst.
    inversion o.
Qed. 

Lemma Prod_ind_principal `{checker_flags} Σ Γ f na kn ind ind' :
  let PiType := tProd na (tInd (mkInd kn ind) []) (tInd (mkInd kn ind') []) in
  wf_ext Σ ->
  Σ ;;; Γ |- f : PiType ->
  forall B, Σ ;;; Γ |- f : B -> Σ ;;; Γ ⊢ PiType ≤ B.
Proof. 
  intros ? ? Hf B HB.
  pose proof (HB' := HB); eapply PCUICPrincipality.principal_type in HB as [Pf Hprinc]; eauto.
  pose proof (Hprinc' := Hprinc); specialize (Hprinc _ Hf) as [? ?].
  assert (Σ ;;; Γ ⊢ Pf = PiType).
  { 
    eapply ws_cumul_pb_alt_closed in w as [? [? [[? ?] ?]]].
    eapply Prod_ind_irred in c; eauto.
    subst.
    eapply ws_cumul_pb_alt_closed. exists x; exists PiType. repeat split; eauto.
    inversion c0; subst; clear c0; econstructor; eauto.
    inversion X1; subst; clear X1; econstructor; eauto. 
    unfold PCUICEquality.cmp_global_instance_gen, PCUICEquality.cmp_opt_variance in *. cbn in *.
    destruct lookup_inductive_gen; eauto. destruct p. destruct destArity; eauto.
    destruct p. destruct context_assumptions; eauto. cbn in *. destruct ind_variance; eauto.
    destruct H3; [ left | right ]; eauto. 
    inversion H0; econstructor. 
    }
  specialize (Hprinc' _ HB') as [? ?].
  etransitivity; eauto. eapply PCUICContextConversion.ws_cumul_pb_eq_le; symmetry; eauto.
Qed.  

Lemma invert_red_it_mkProd {cf : checker_flags} {Σ : global_env_ext} {wfΣ : PCUICTyping.wf_ext Σ} {Γ ctx s s'} : 
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx (tSort s) ⇝ tSort s' -> s = s'.
Proof.
  induction ctx using PCUICInduction.ctx_length_rev_ind; cbn; eauto.
  - intros hs. eapply PCUICConversion.invert_red_sort in hs. now noconf hs.
  - rewrite it_mkProd_or_LetIn_app. cbn. destruct d as [na [b|] ty]; cbn.
    * intros hlet.
      eapply PCUICConversion.invert_red_letin in hlet as [[? [? [? []]]]|]; try congruence.
      rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn //= in c. eapply H; tea. len.
    * intros hp. eapply PCUICConversion.invert_red_prod in hp as [? [? []]]; congruence.
Qed.

Lemma invert_ind_sort {cf : checker_flags} {Σ} (wfΣ : wf_ext Σ) ind mdecl idecl u s : 
  Σ ;;; [] |- tInd ind u : tSort s -> 
  declared_inductive Σ ind mdecl idecl ->
  leq_sort Σ (subst_instance u (ind_sort idecl)) s.
Proof.
  intros hind hd.
  eapply PCUICInversion.inversion_Ind in hind as [mdecl' [idecl' [wf [decli [cu hleq]]]]]; eauto.
  pose proof (PCUICWeakeningEnvTyp.on_declared_inductive hd) as [].
  pose proof wfΣ as [wfΣ'].
  eapply (declared_inductive_to_gen (wfΣ := wfΣ')) in hd, decli; eauto.
  eapply (PCUICGlobalEnv.declared_inductive_inj hd) in decli as [-> ->].
  destruct o0. rewrite ind_arity_eq in hleq.
  eapply PCUICConversion.ws_cumul_pb_Sort_r_inv in hleq as [s' []].
  rewrite -it_mkProd_or_LetIn_app PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn in c. eapply invert_red_it_mkProd in c.
  subst s'. now red in c0.
Qed.

Lemma interoperability_firstorder_function {funext:Funext} {P:Pointer} {H:Heap} {HP : @CompatiblePtr P P}
  {HH : @CompatibleHeap _ _ _ H H} 
  (Hvrel_refl : forall v, vrel v v)
  (Hheap_refl : forall h, R_heap h h) `{WcbvFlags} (efl := extraction_env_flags) (cf:=config.extraction_checker_flags)
    univ retro univ_decl kn mind 
  (Hparam : ind_params mind = [])
  (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
  (Hfinite : ind_finite mind == Finite)
  (Hmono : ind_universes mind = Monomorphic_ctx)
  (Σ0 := mk_global_env univ [(kn , InductiveDecl mind)] retro)
  (Hgood : pcuic_good_for_extraction Σ0)
  (Hfo : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind))) 
  (Hfo_ext : is_true (forallb (@firstorder_oneind [(kn, @firstorder_mutind [] mind)] mind) (ind_bodies mind))) ind ind' Eind Eind' f na l:
  let adt := RocqType_to_camlType mind Hparam Hfo in
  let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl) in
  let global_adt := add_ADT _ _ [] [] kn adt in 
  forall   (Hnparam : forall (i : kername) (mdecl : mutual_inductive_body),
  lookup_env Σ i = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0),
  pcuic_good_for_extraction Σ ->
  ind_sort Eind = Sort.sType l ->
  ind_sort Eind' = Sort.sType l ->
  forall (wfΣ : PCUICTyping.wf_ext (Σ,univ_decl))
  (expΣ : PCUICEtaExpand.expanded_global_env Σ)
  (expf : PCUICEtaExpand.expanded Σ [] f)
  (wf : ∥ Σ ;;; [] |- f : tProd na (tInd (mkInd kn ind) []) (tInd (mkInd kn ind') []) ∥),
  with_constructor_as_block = true ->
  ind < List.length (snd adt) ->
  ind' < List.length (snd adt) ->
  lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
  lookup_inductive Σ (mkInd kn ind') = Some (mind, Eind') ->
  realize_term _ _ [] []
        global_adt (Arrow (Adt kn ind []) (Adt kn ind' [])) 
        (compile_pipeline Σ f wfΣ expΣ expf (_;wf)).
Proof.
  intros ? ? ? ? Hextract Hind_sort Hind_sort' ? ? ? ? ? ? ? Hlookup Hlookup'. intros. simpl. 
  rewrite ReflectEq.eqb_refl. unfold to_realize_term. cbn. 
  pose (wfΣ_ext := wfΣ). destruct wfΣ as [wfΣ ?].
  intros t Ht. unfold to_realize_term in *. intros h h' v Heval.
  pose proof (Hlookup'' := Hlookup).
  pose proof (Hlookup''' := Hlookup').
  unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen in Hlookup, Hlookup'. cbn in Hlookup, Hlookup'.
  rewrite ReflectEq.eqb_refl in Hlookup, Hlookup'.
  assert (HEind : nth_error (ind_bodies mind) ind = Some Eind).
  { destruct (nth_error (ind_bodies mind) ind); now inversion Hlookup. }
  assert (Htype_ind : (Σ, univ_decl);;; []
  |- tInd {| inductive_mind := kn; inductive_ind := ind |}
       [] : (tSort (ind_sort Eind))@[[]]).
  {  unshelve epose proof (type_Ind (Σ,univ_decl) [] (mkInd kn ind) [] mind Eind _ _ _).
  *** econstructor.
  *** unfold declared_constructor, declared_inductive. subst. now cbn.
  *** unfold consistent_instance_ext, consistent_instance; cbn.
     now rewrite Hmono.
  *** unfold ind_type in X. destruct Eind; cbn in *.
      unfold PCUICTyping.wf in wfΣ. inversion wfΣ as [_ wfΣ'].
      cbn in wfΣ'. inversion wfΣ'. clear X0. inversion X1. inversion on_global_decl_d.
      eapply Alli_nth_error in onInductives; eauto. cbn in onInductives.
      inversion onInductives. cbn in *.
      eapply nth_error_forall in Hindices; eauto. cbn in Hindices. rewrite Hindices in ind_arity_eq.                       
      cbn in ind_arity_eq. rewrite Hparam in ind_arity_eq. cbn in ind_arity_eq.
      now rewrite ind_arity_eq in X. }
  assert (HEind' : nth_error (ind_bodies mind) ind' = Some Eind').
  { destruct (nth_error (ind_bodies mind) ind'); now inversion Hlookup'. }
  destruct wf.
  assert (Htype_ind' : (Σ, univ_decl);;; []
  |- tInd {| inductive_mind := kn; inductive_ind := ind' |}
        [] : (tSort (ind_sort Eind'))@[[]]).
  {  unshelve epose proof (type_Ind (Σ,univ_decl) [] (mkInd kn ind') [] mind Eind' _ _ _).
  *** econstructor.
  *** unfold declared_constructor, declared_inductive. subst. now cbn.
  *** unfold consistent_instance_ext, consistent_instance; cbn.
      now rewrite Hmono.
  *** unfold ind_type in X. destruct Eind'; cbn in *.
      unfold PCUICTyping.wf in wfΣ. inversion wfΣ as [_ wfΣ'].
      cbn in wfΣ'. inversion wfΣ'. clear X0. inversion X1. inversion on_global_decl_d.
      eapply Alli_nth_error in onInductives; eauto. cbn in onInductives.
      inversion onInductives. cbn in *.
      eapply nth_error_forall in Hindices; eauto. cbn in Hindices. rewrite Hindices in ind_arity_eq.                       
      cbn in ind_arity_eq. rewrite Hparam in ind_arity_eq. cbn in ind_arity_eq.
      now rewrite ind_arity_eq in X. } 
  assert (Htype_ind'' : (Σ, univ_decl);;;
  [],,
  vass na
    (tInd {| inductive_mind := kn; inductive_ind := ind |}
       [])
  |- tInd {| inductive_mind := kn; inductive_ind := ind' |}
       [] : tSort (subst_instance_sort [] (ind_sort Eind'))).
  { eapply (PCUICWeakeningTyp.weakening  _ _ ([vass na (tInd {| inductive_mind := kn; inductive_ind := ind |} [])])) in Htype_ind'; cbn in Htype_ind'; eauto.
    constructor. constructor. cbn. pose proof t0 as t1. eapply PCUICValidity.validity in t1 as [? [s [t1 _]]]. cbn in o0, t1.
    eapply PCUICInversion.inversion_Prod in t1 as [s1 [s2 []]].
    hnf in l0. hnf. cbn. cbn in l0. (destruct l0 as [_ [s' [? [-> ]]]] || destruct l0 as [_ [s' [? ->]]]). split => //. now exists s'. eauto.
    }
  assert (Herase: ∥ Extract.nisErasable (Σ, univ_decl) [] f ∥).
  { sq.  unfold Extract.nisErasable. eexists; eexists. split; eauto.
    - clear Heval. sq. eapply PCUICNormal.nf_tProd; eapply PCUICNormal.nf_tind.
    - eapply type_Prod; eauto. unfold lift_typing0, lift_sorting; cbn. split; eauto.
    - now rewrite Hind_sort Hind_sort'. 
  }
  assert (Hax: PCUICClassification.axiom_free Σ).
    { intros ? ? X. now inversion X. }    
  inversion Heval; subst.
  - specialize (Ht _ _ _ H8).
    unshelve eapply camlValue_to_RocqValue in Ht. 20:eauto. all:eauto; cbn.
    destruct Ht as [t_coq [? [Ht_typ [Hirred Ht_eval]]]]. specialize (Ht_eval h2). 
    eapply isPure_heap in H6; try eapply compile_pure; intros; cbn; eauto. cbn in H6.
    destruct H6 as [[? ? ] ?]. eapply isPure_heap in H11 as [? ?]; eauto.
    2:{ intros ? ? []. }
    2:{ unfold Ident.Map.add; intro. destruct (Ident.eqb s x); eauto.
      eapply isPure_heap in Ht_eval; try eapply compile_pure; intros; cbn; eauto. now destruct Ht_eval.
      inversion H7. } 
    subst. eapply compile_compose in H8 as [? [? [? [? ?]]]]; eauto.
    3: { eapply isPure_heap_irr, Ht_eval. try eapply compile_pure; intros; cbn; eauto.
          intros _ _ []. now intros. }
    3: { inversion H4. }
    2: { destruct Ht_typ. sq. red. do 2 eexists. split; eauto.
      - assert (wtu : Σ;;; [] |- tApp f t_coq : (tInd {| inductive_mind := kn; inductive_ind := ind' |} []) {0 := t_coq}).
        { eapply PCUICValidity.type_App'; eauto. }
        cbn in wtu. eauto. 
      - eapply PCUICNormal.nf_tind.
      - now cbn.
      - now rewrite Hind_sort'.
    }
    assert (v = x3). { unshelve eapply isPure_value_vrel_eq; eauto. }
    subst. sq. unfold adt. eapply RocqValue_to_CamlValue' with (t := tApp f t_coq). all:eauto.
  - specialize (Ht _ _ _ H7).
    unshelve eapply camlValue_to_RocqValue in Ht. 20:eauto. all: eauto; cbn.
    destruct Ht as [t_coq [Hexpand_t [Ht_typ [Hirred Ht_eval]]]]. specialize (Ht_eval h2).
    eapply isPure_heap in H6; try eapply compile_pure; intros; cbn; eauto.
    2:{ inversion H4. }
    destruct H6 as [? ?]. rewrite nth_nth_error in H9. 
    case_eq (nth_error mfix n); intros; [|rewrite H6 in H9; inversion H9].
    pose proof (H4_copy := H4). destruct H4.  
    eapply (nth_error_forall (n:=n)) in H8; eauto. 
    rewrite H6 in H9. subst.
    eapply isPure_heap in H12 as [? ?]; eauto.
    2: { intros ? ? []. }
    2: { unfold Ident.Map.add; intro; destruct (Ident.eqb s y); eauto.
         eapply isPure_heap in Ht_eval; try eapply compile_pure; intros; cbn; eauto. 
         now destruct Ht_eval as [? _]. inversion H5. eapply isPure_add_self; eauto.
         now destruct H4_copy. }
    cbn in *. subst. eapply compile_compose in H7 as [? [? [? [? ?]]]]; eauto.
    2: { destruct Ht_typ. sq. red. do 2 eexists. split; eauto.
    - assert (wtu : Σ;;; [] |- tApp f t_coq : (tInd {| inductive_mind := kn; inductive_ind := ind' |} []) {0 := t_coq}).
      { eapply PCUICValidity.type_App'; eauto. }
      cbn in wtu. eauto. 
    - eapply PCUICNormal.nf_tind.
    - now cbn.
    - now rewrite Hind_sort'. } 
    2: { eapply isPure_heap_irr,  Ht_eval; try eapply compile_pure; intros; cbn; eauto. inversion H9. }
    assert (v = x1). { unshelve eapply isPure_value_vrel_eq; eauto. }
    subst. unshelve eapply RocqValue_to_CamlValue'; try exact H9; eauto.
  - pose Normalisation. unshelve erewrite compile_function in H10. 
    17: exact Herase. 
    6,7,8,9:eauto. 7,10:eauto. 4: unshelve eapply Malfunction_ind_env_empty.
    7:eauto. all:eauto. inversion H10. intros ? ? ? [].
  Unshelve. all: eauto.
Qed.

(* Print Assumptions interoperability_firstorder_function. *)