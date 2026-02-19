From Stdlib Require Import ssreflect ssrbool Eqdep_dec.
From Equations Require Import Equations. 
From MetaRocq.Utils Require Import All_Forall MRSquash MRList.
From MetaRocq.Common Require Import Transform config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICFirstorder PCUICCasesHelper BDStrengthening PCUICCumulativity.
From MetaRocq.Erasure Require Import EWcbvEval EWcbvEvalNamed.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.

From Malfunction Require Import Malfunction Interpreter SemanticsSpec utils_array Compile.

From Stdlib Require Import ZArith Array.PArray List String Floats Lia Bool.
Import ListNotations.
From MetaRocq.Utils Require Import bytestring.

Unset Elimination Schemes. 

Inductive camlType : Set :=
    Arrow : camlType -> camlType -> camlType
  | Rel : nat -> camlType
  | Adt : kername -> 
            (* number of the ADT in the mutual definition *) nat -> 
            (* list of parameters *) list camlType -> 
            camlType.

Definition camlType_rect :
forall P : camlType -> Type,
       (forall c : camlType,
        P c -> forall c0 : camlType, P c0 -> P (Arrow c c0)) ->
       (forall n : nat, P (Rel n)) ->
       (forall (k : kername) i (l : list camlType), All P l -> P (Adt k i l)) ->
       forall c : camlType, P c. 
Proof. 
  intros P X X0 X1. fix f 1. intros c; destruct c.
  - eapply X; eauto.   
  - eapply X0; eauto. 
  - eapply X1; eauto. induction l; econstructor; eauto. 
Defined.
       
Set Elimination Schemes. 

Notation "A → B" := (Arrow A B) (at level 50). 

Definition isArrow T := match T with Arrow _ _ => true | _ => false end.

Definition ADT : Set := 
  (* number of parameters *)
  nat * list (
    list (list camlType) (* list of constructors for each ADT *)).

Inductive Existsi {A : Type} (P : nat -> A -> Prop) (n : nat) 
  : list A -> Prop :=
	  Existsi_cons_hd : forall x l, P n x -> Existsi P n (x :: l)
  | Existsi_cons_tl : forall (x : A) (l : list A),
                     Existsi P (S n) l -> Existsi P n (x :: l).

Lemma Existsi_spec A (P : nat -> A -> Prop) n (l:list A) : Existsi P n l <-> 
  exists k x, n <= k /\ k < n + List.length l /\ P k x /\ nth_error l (k-n) = Some x.
Proof.
  split. 
  { induction 1.
    - exists n; exists x. cbn; repeat split; eauto. lia.
      now rewrite Nat.sub_diag.   
    - destruct IHExistsi as [k [a [Hk [Hk' [HP Ha]]]]].
      exists k; exists a. repeat split; eauto; cbn; try lia.
      assert (k - n = S (k - S n)) by lia.
      now rewrite H0. 
  }
  { revert n. induction l; intros n [k [? [? [? [? ?]]]]]. 
    - rewrite nth_error_nil in H2. inversion H2.
    - case_eq (k =? n); intro Hk. 
      + eapply Nat.eqb_eq in Hk. econstructor. assert (k - n = 0) by lia.
        rewrite H3 in H2. cbn in H2. now inversion H2.
      + eapply Nat.eqb_neq in Hk. econstructor 2.
        eapply IHl. exists k, x. cbn in H0. repeat split; eauto; try lia.
        assert (k - n = S (k -S n)) by lia. now rewrite H3 in H2. 
  }
Defined. 

Section Realizability.

  Variable _Ptr:Pointer. 
  Variable _Heap:Heap.

  Definition realize_adt_type := 
      forall (params: list camlType), All (fun _ => value -> Prop) params -> 
              ((* number of the ADT in the mutual definition *) nat -> value -> Prop).

  Variable globals : list (Ident.t * value).
  
  Definition global_adt_decl := list (kername * realize_adt_type).

  Open Scope bs. 

  Close Scope bs. 

  Section Values. 

    Variable local_adt : list (value -> Prop).
    Variable global_adt : global_adt_decl.

    Definition to_realize_term (realize_val : value -> Prop) 
      : t -> Prop := fun t => forall h h' v, 
      eval _ _ globals empty_locals h t h' v -> realize_val v.

    Definition to_realize_value (realize_term : t -> Prop) 
      : value -> Prop := fun v => forall h, exists t h', 
        eval _ _ globals empty_locals h t h' v /\ realize_term t.

    Definition realize_term (A:camlType) : t -> Prop.
    Proof.
      refine (camlType_rect _ _ _ _ A); clear A.
      - intros A PA B PB.
        exact (fun f => forall t, PA t -> PB (Mapply(f,[t]))).
      - intros n. 
        exact (to_realize_term (List.nth n local_adt (fun _ => False))).
      - intros kn n params PAll.
        case (find (fun '(kn',_) => eq_kername kn kn') global_adt).
        + intros [_ Hrel]. 
          refine (to_realize_term (Hrel params _ n)).
          induction PAll; econstructor; eauto. eapply to_realize_value; eassumption.
        + intros; exact False. 
    Defined.

    Definition realize_value (A:camlType) : value -> Prop :=
      to_realize_value (realize_term A).

  End Values. 
  MetaRocq Quote Recursively Definition tnat := nat.

  Fixpoint realize_ADT_gen_fix (global_adt : global_adt_decl) 
    (adt : list (list (list camlType))) (step : nat) : realize_adt_type.
  Proof.
    destruct step; [compute; intros; exact False|].
    intros params paramRel ind. 
    destruct (Nat.ltb ind (List.length adt)); [|intros; exact False].
    pose proof (constr_list := List.nth ind adt []). 
    refine (fun v => _\/_).
    - pose (constr_noarg := filter 
      (fun x => match x with [] => true 
            | _ => false end) constr_list).
      refine (Existsi (fun index Ts => v = value_Int (Int , Z.of_nat index)) 0 constr_noarg).
    - pose (constr_arg := filter 
      (fun x => match x with [] => false 
          | _ => true end) constr_list).
      refine (Existsi (fun index Ts => 
          exists vs, v = Block (int_of_nat index, vs) /\ _) 0 constr_arg). 
      refine (Forall2 (realize_value _ global_adt) Ts vs).
      refine (_ ++ _).
      + (* parameters *)
        clear -paramRel. induction paramRel; [exact []| ].
        refine (p :: IHparamRel).
      + (* recursive calls *)
        exact (to_list (realize_ADT_gen_fix global_adt adt step params paramRel) (List.length adt)).
  Defined.   

  Definition realize_ADT_gen (global_adt : global_adt_decl) 
    : ADT -> nat -> realize_adt_type :=
    fun '(n , adt) step params =>
      if (Nat.eqb n (List.length params)) 
      then realize_ADT_gen_fix global_adt adt step params
      else fun _ _ _ => False.

  Definition realize_ADT (global_adt : global_adt_decl) : ADT -> realize_adt_type :=
    fun adt params paramRel ind v => exists n, realize_ADT_gen global_adt adt n params paramRel ind v.

  Definition add_ADT (global_adt : global_adt_decl) (kn : kername) (adt : ADT) :  global_adt_decl := 
    (kn, realize_ADT global_adt adt) :: global_adt.

End Realizability.


  Definition empty_heap : CanonicalHeap.(heapGen) (@SemanticsSpec.value CanonicalPointer) :=
    (int_of_nat 0 , fun _ => []).

  Lemma lookup_inductive_env Σ kn Emind Eind ind :
    EGlobalEnv.lookup_inductive Σ (mkInd kn ind) = Some (Emind,Eind) ->
    EGlobalEnv.lookup_env Σ kn = Some (EAst.InductiveDecl Emind).
  Proof.
    induction Σ; cbn; intros.
    - inversion H.
    - destruct (ReflectEq.eqb kn (fst a)); cbn in *.
      + f_equal. destruct (snd a); cbn in *; [inversion H|].
        destruct (nth_error (EAst.ind_bodies m) ind); now inversion H.  
      + apply IHΣ; eauto.
  Qed.

  Fixpoint zip {A B} (l:list A) (l':list B) : list (A * B) :=
  match l , l' with 
  | [] , [] => []
  | a::l , b::l' => ((a,b) :: zip l l')
  | _ , _ => [] 
  end. 

  Fixpoint zipAll {A B} (l:list A) (l':All B l) : list ({a:A & B a}) :=
    match l' with 
      All_nil => []
    | @All_cons _ _ a l b l' => (existT _ a b :: zipAll l l')
    end.
        
  Lemma zip_length {A B} (l:list A) (l':list B) : 
    #|l| = #|l'| ->  #|zip l l'| = #|l|.
  Proof. 
    revert l'; induction l; destruct l'; cbn; eauto.
    intro Heq; inversion Heq. rewrite IHl; eauto.
  Qed.   
 
  Lemma zipAll_length {A B} (l:list A) (l':All B l) : 
    #|zipAll l l'| = #|l|.
  Proof. 
    induction l'; cbn ; f_equal; eauto.
  Qed. 

  Lemma zip_fst {A B} (l:list A) (l':list B) : 
    #|l| = #|l'| -> map fst (zip l l') = l.
  Proof.
    revert l'; induction l; destruct l'; cbn; eauto.
    - inversion 1.
    - intro Heq; inversion Heq. rewrite IHl; eauto.
  Qed.

  Lemma zipAll_fst {A B C} (l:list A) (l': All B l) (f : A -> C): 
    map (fun x => f (@projT1 _ _ x)) (zipAll l l') = map f l.
  Proof.
    induction l'; cbn; f_equal; eauto.
  Qed.         

  Lemma zip_snd {A B} (l:list A) (l':list B) : 
    #|l| = #|l'| -> map snd (zip l l') = l'.
  Proof. 
    revert l'; induction l; destruct l'; cbn; eauto.
    - inversion 1.  
    - intro Heq; inversion Heq. rewrite IHl; eauto.
  Qed.   
  
  (* Lemma zipAll_snd {A B} (l:list A) (l':All B l) : 
     map (@projT2 _ _) (zip l l') = l'.
  revert l'; induction l; destruct l'; cbn; eauto.
  - inversion 1.  
  - intro Heq; inversion Heq. rewrite IHl; eauto.
  Qed.   *)

  Fixpoint Forall2_exists T U A P l l'
  (H: Forall2 (fun (t : T) (u : U) => exists a : A, P t u a) l l')  
  : exists l'' : list A, Forall2 (fun tu a => P (fst tu) (snd tu) a) (zip l l') l''.
  Proof. 
    destruct H.
    - exists []. econstructor.
    - destruct H as [p H].
      refine (let '(ex_intro l' X) := 
              Forall2_exists T U A P _ _ H0 in _).
      exists (p::l'). econstructor; eauto.
  Qed.  

  Fixpoint Forall2_exists_dep T U (A : T -> Prop) P l l'
    (H: Forall2 (fun (t : T) (u : U) => exists a : A t, P t u a) l l')  
    : exists l'' : All A l, Forall2 (fun tu a => P (projT1 tu) a (projT2 tu)) (zipAll l l'') l'.
  Proof. 
    destruct H.
    - exists All_nil. econstructor.
    - destruct H as [p H].
      refine (let '(ex_intro l' X) := 
              Forall2_exists_dep T U A P _ _ H0 in _).
      exists (All_cons p l'). econstructor; eauto. 
  Qed. 

  Lemma Forall2_acc_cst (X A B : Type) (R : X -> A -> X -> B -> Prop) x l l' :
    Forall2 (fun a b => R x a x b) l l' -> Forall2_acc R x l x l'.
  Proof.
    induction 1; econstructor; eauto.
  Qed.

  Lemma Forall2_sym :
  forall A B (P : A -> B -> Prop) l l',
    Forall2 P l l' ->
    Forall2 (fun x y => P y x) l' l.
  Proof.
  intros A B P l l' h.
  induction h.
  - constructor.
  - constructor. all: auto.
  Qed.
  
 Lemma Forall_Forall2_and_inv {A B : Type} 
  {R : A -> B -> Prop} {P : A -> Prop} l l':
    Forall2 (fun (x : A) (y : B) => P x /\ R x y ) l l' ->
    Forall2 R l l' /\ Forall P l.
  Proof. 
    induction 1; repeat econstructor; now eauto.
  Qed.

  Lemma Forall2_forall {A B X: Type} 
    {R : A -> B -> X -> Prop} l l':
  Forall2 (fun a b => forall x, R a b x) l l' ->
  forall x, Forall2 (fun a b => R a b x) l l'.
  Proof.
    induction 1; econstructor; eauto.
  Qed.

  Definition cstr_nargs : constructor_body -> nat := fun c => #| cstr_args c|.

  Lemma Forall2_map_left {A B C} (P : A -> B -> Prop) (f : C -> A) (l : list C) (l' : list B) :
    Forall2 P (map f l) l' <-> Forall2 (fun x y => P (f x) y) l l'.
  Proof.
    split; intros.
    + eapply Forall2_map_inv. now rewrite map_id.
    + rewrite -(map_id l'). now eapply Forall2_map.
  Qed.

  Lemma Forall2_map_eq {A B C} (f : C -> A) (g : B -> A) (l : list C) (l' : list B) :
    Forall2 (fun x y => f x = g y) l l' -> map f l = map g l'.
  Proof.
    induction 1; eauto; cbn. f_equal; eauto. 
  Qed.

  Definition lookup_constructor_args Σ ind : option (list nat) 
    := match lookup_inductive Σ ind with
    | Some (_, idecl) => Some (map cstr_nargs (ind_ctors idecl))
   | None => None
    end.

Inductive Forall2i {A B : Type} (R : nat -> A -> B -> Prop) (n : nat)
  : list A -> list B -> Prop :=
| Forall2i_nil : Forall2i R n [] []
| Forall2i_cons :
    forall x y l r,
      R n x y ->
      Forall2i R (S n) l r ->
      Forall2i R n (x :: l) (y :: r).
Arguments Forall2i_nil {_ _ _ _}.
Arguments Forall2i_cons {_ _ _ _ _ _ _ _}.

Derive Signature NoConfusionHom for All2i.

Lemma Forall2_Forall_mix {A B} {P : B -> Prop} {Q : A -> B -> Prop}
   {l : list A} {l' : list B} :
  Forall2 (fun x y => (P y -> Q x y)) l l' -> Forall P l' -> Forall2 Q l l'.
Proof.
  induction 1; simpl; intros; constructor; inversion H1; eauto.
Qed.

  Lemma Forall2_and_inv {A B : Type} (R R' : A -> B -> Prop) (l : list A) (l' : list B) :
    Forall2 (fun (x : A) (y : B) => R x y /\ R' x y) l l'
    -> Forall2 R l l' /\ Forall2 R' l l'.
  Proof.
    induction 1; split; eauto; econstructor; destruct H; now destruct IHForall2.
  Qed.

  Section Pure.

  Variable Σ : list Ident.t.

  Fixpoint isPure (t : t) :=
    match t with
    | Mvar x => true
    | Mlambda (ids, x) => isPure x
    | Mapply (x, args) => isPure x && forallb isPure args
    | Mlet (binds, x) => forallb isPure_binding binds && isPure x
    | Mnum x => true
    | Mstring x => false (* strings are interpreted using vectors *)
    | Mglobal id => true
    | Mswitch (x, sels) => isPure x && forallb (fun '(_, x) => isPure x) sels
    | Mnumop1 (op, num, x) => isPure x
    | Mnumop2 (op, num, x1, x2) => isPure x1 && isPure x2
    | Mconvert (from, to, x) => isPure x
    | Mblock (tag, xs) => forallb isPure xs
    | Mfield (i, x) => isPure x
    | _ => false
    end
  with isPure_binding (b : binding) :=
         match b with
         | Unnamed x => isPure x
         | Named (id, x) => isPure x
         | Recursive recs => forallb (fun '(id,x) => isPure x) recs
         end.

  Definition isPure_rec_value `{Pointer} (v : rec_value) :=
    match v with 
    | RFunc (_ , t) => is_true (isPure t)
    | Bad_recursive_value => True
    | _ => False
    end. 

  Fixpoint isPure_value `{Pointer} (v : value) {struct v} :=
    match v with
    | Block (_,vs) => Forall (fun p => p) (map isPure_value vs)
    | Func (locals,_,t) => (forall s, isPure_value (locals s)) /\ is_true (isPure t)    
    | RClos (locals,self,mfix,t) => (forall s, isPure_value (locals s)) /\ Forall isPure_rec_value mfix
    | value_Int _ => True
    | Float _ => True
    | fail _ => True
    | _ => False
    end.

End Pure.

Definition Funext := forall A B (f g: A -> B), (forall x, f x = g x) -> f = g. 

Lemma isPure_value_vrel_eq {funext:Funext} {P : Pointer} `{@CompatiblePtr P P} v v' : 
  isPure_value v -> vrel v v' -> v = v'.
Proof.
  intros Hpure Hrel. induction Hrel; cbn in *; try solve [inversion Hpure]; eauto; repeat f_equal.
  - induction H1; f_equal; inversion Hpure; subst; eauto.
    eapply IHForall2; eauto. inversion H0; eauto. 
  - destruct Hpure. apply funext; eauto.
  - destruct Hpure. apply funext; eauto.
  - destruct Hpure. clear -H4 H2. induction H2; f_equal; eauto.
    + inversion H4; subst; clear H4. destruct H0 as [? [? ?]]. destruct x. 
      * destruct p. symmetry;  destruct (H0 t t0); eauto.
      * inversion H5.
      * symmetry; eapply H3; eauto.
    + inversion H4; eauto.
Qed. 

Lemma isPure_value_vrel_eq' {funext:Funext} {P : Pointer} `{@CompatiblePtr P P} v v' : 
  isPure_value v' -> vrel v v' -> v = v'.
Proof.
  intros Hpure Hrel. induction Hrel; cbn in *; try solve [inversion Hpure]; eauto; repeat f_equal.
  - induction H1; f_equal; inversion Hpure; subst; eauto.
    eapply IHForall2; eauto. inversion H0; eauto. 
  - destruct Hpure. apply funext; eauto.
  - destruct Hpure. apply funext; eauto.
  - destruct Hpure. clear -H4 H2. induction H2; f_equal; eauto.
    + inversion H4; subst; clear H4. destruct H0 as [? [? ?]]. destruct y. 
      * destruct p. destruct (H0 t t0); eauto.
      * inversion H5.
      * eapply H3; eauto.
    + inversion H4; eauto.
Qed. 

Lemma isPure_value_vrel {P P' : Pointer} `{@CompatiblePtr P P'} v v' : 
  isPure_value v -> vrel v v' -> isPure_value v'.
Proof.
  intros Hpure Hrel. induction Hrel; cbn in *; try solve [inversion Hpure]; eauto. 
  - induction H1; econstructor; inversion Hpure; subst; eauto.
    eapply IHForall2; eauto. inversion H0; eauto.      
  - destruct Hpure; split; eauto.
  - destruct Hpure; split; eauto. revert H4. clear -H2.  
    induction H2; econstructor; inversion H4; subst; eauto.
    clear - H0 H5. destruct H0 as [? [? ?]]. destruct y; cbn; eauto. 
    + destruct p. destruct (H0 t t0). rewrite (H4 eq_refl) in H5. eauto.
    + destruct x; try inversion H5. destruct p0. destruct (H0 t t0).
      specialize (H3 eq_refl). inversion H3.
      destruct H2. specialize (H2 eq_refl). inversion H2.
Qed.

Lemma isPure_value_vrel' {P P' : Pointer} `{@CompatiblePtr P P'} v v' : 
  isPure_value v' -> vrel v v' -> isPure_value v.
Proof.
  intros Hpure Hrel. induction Hrel; cbn in *; try solve [inversion Hpure]; eauto. 
  - induction H1; econstructor; inversion Hpure; subst; eauto.
    eapply IHForall2; eauto. inversion H0; eauto.      
  - destruct Hpure; split; eauto.
  - destruct Hpure; split; eauto. revert H4. clear -H2.  
    induction H2; econstructor; inversion H4; subst; eauto.
    clear - H0 H5. destruct H0 as [? [? ?]]. destruct y; cbn; eauto. 
    + destruct p. destruct (H0 t t0). rewrite (H4 eq_refl). eauto.
    + destruct x; try inversion H5.
    + destruct H2. rewrite (H3 eq_refl); eauto.   
Qed.

From Malfunction Require Import CompileCorrect Pipeline PipelineCorrect.

Lemma isPure_add_self `{Heap} locals mfix self s :
  (forall s : Ident.t, isPure_value (locals s)) ->
  Forall isPure_rec_value mfix ->
  isPure_value (add_self self mfix locals s).
Proof.
  intros Hlocals Hmfix. unfold add_self, add_recs, List.mapi.
  generalize 0 as i. generalize self at 1. 
  induction self; cbn; eauto.
  unfold Ident.Map.add. destruct (Ident.eqb s a); cbn; eauto.
Qed.

Lemma isPure_heap `{Heap} `{WcbvFlags} Σ locals h h' t v :
  is_true (isPure t) ->
  (forall nm v, In (nm, v) Σ -> isPure_value v) ->
  (forall s, isPure_value (locals s)) -> 
  eval Σ locals h t h' v -> isPure_value v /\ h = h'.
Proof.
  rename H into HP. rename H0 into HH. rename H1 into HWF. 
  intros Hpure HΣ Hlocals. induction 1; try solve [inversion Hpure]; cbn in Hpure;
  repeat rewrite MRProd.andb_and in Hpure; try solve [cbn; repeat split; eauto]; eauto. 
  - cbn in *. destruct Hpure as [? [? ?]].
    try (destruct IHeval1; eauto);
     try (destruct IHeval2; eauto); try (destruct IHeval3; eauto); try now eauto.
    destruct H5. intros s. unfold Ident.Map.add. destruct (Ident.eqb s x); eauto.
  - destruct Hpure as [? [? ?]].
    try (destruct IHeval1; eauto);
     try (destruct IHeval2; eauto); try (destruct IHeval3; eauto); try now eauto.
    destruct H6. pose proof (proj1 (Forall_nth _ _) H10 n Bad_recursive_value). rewrite H1 in H11.
    eapply H11. case_eq (Nat.ltb n #|mfix|); try rewrite Nat.ltb_lt; eauto.
    rewrite Nat.ltb_ge. intro neq.  rewrite nth_overflow in H1; eauto. inversion H1.  
    destruct H6. intros s. unfold Ident.Map.add. destruct (Ident.eqb s y); eauto.
    eapply isPure_add_self; eauto. 
  - cbn in *. destruct Hpure as [? [? ?]]; try (destruct IHeval1; eauto); now eauto.
  - destruct Hpure as [? [? [? ?]]]. repeat rewrite MRProd.andb_and in IHeval.
    destruct IHeval ; eauto.
  - cbn in *. destruct Hpure as [[? ?] ?]; try (destruct IHeval1; eauto); try (destruct IHeval2; eauto); now eauto.  
  - cbn in *. destruct Hpure as [[? ?] ?]; try (destruct IHeval1; eauto); try (destruct IHeval2; eauto); try now eauto.
    intros s. unfold Ident.Map.add. destruct (Ident.eqb s x); eauto.
  - cbn in *. destruct Hpure as [[? ?] ?]; try (destruct IHeval; eauto); try now eauto.
    intros s. rewrite H. eapply isPure_add_self; eauto. unfold rfunc, RFunc_build.
    eapply forallb_Forall in H1. clear -H1. induction recs; eauto; cbn. destruct a; cbn in *. inversion H1; subst.
    econstructor; eauto. destruct t0; cbn; eauto. destruct p. cbn in H2. destruct l; cbn ; eauto.
    destruct l; cbn ; eauto.
  - cbn in *. destruct Hpure as [? ?]; try (destruct IHeval1; eauto); try (destruct IHeval2; eauto); try now eauto.
    induction cases; cbn in *. inversion H0. repeat rewrite MRProd.andb_and in H3. destruct H3.   
    destruct a. destruct (existsb _ _); [inversion H0; subst; eauto|]. now eapply IHcases.
  - cbn in *. clear H. induction H0; [now eauto|]. repeat rewrite MRProd.andb_and in Hpure.
    destruct Hpure. destruct IHForall2_acc; eauto. cbn. destruct H as [? H]; eauto. destruct H as [? H]; eauto. cbn; split; now eauto.
  - cbn in *. destruct IHeval; eauto. split; eauto. eapply Forall_nth; eauto. now eapply Forall_map_inv in H2.
  - cbn in *. now eauto.
  - cbn in *. destruct IHeval; eauto.
  - cbn. destruct Hpure. destruct IHeval1; eauto. destruct IHeval2; eauto. now destruct op.
  - cbn; now eauto.   
  - cbn; destruct Hpure. destruct IHeval1; eauto. destruct IHeval2; now eauto.
  - cbn; destruct Hpure. destruct IHeval1; eauto. destruct IHeval2; now eauto.
  - cbn; destruct IHeval; eauto. 
  - cbn. destruct IHeval; eauto.
  - cbn. destruct IHeval; eauto.
Qed.            

Lemma isPure_heap_irr `{Heap} `{WcbvFlags} h h' Σ locals t v :
  is_true (isPure t) ->
  (forall nm v, In (nm, v) Σ -> isPure_value v) ->
  (forall s, isPure_value (locals s)) -> 
  eval Σ locals h t h' v -> forall h'', eval Σ locals h'' t h'' v.
Proof.
  rename H into HP; rename H0 into H; rename H1 into H0. 
  intros Hpure HΣ Hlocals. induction 1; try solve [inversion Hpure]; cbn in Hpure;
  repeat rewrite MRProd.andb_and in Hpure; try solve [cbn; destruct Hpure; econstructor; eauto]; 
  try solve [cbn; econstructor; eauto].
  - intro. destruct Hpure as [? [? ?]]. econstructor 3; eauto.
    eapply isPure_heap in H1_, H1_0; eauto. destruct H1_ as [[Hlocals' He] _].  
    eapply IHeval3; eauto. intros s. unfold Ident.Map.add. destruct (Ident.eqb s x); now eauto.
  - intro. destruct Hpure as [? [? ?]]. econstructor 4; eauto.
    eapply isPure_heap in H1_, H1_0; eauto. destruct H1_ as [[Hlocals' He] _].
    pose proof (proj1 (Forall_nth _ _) He n Bad_recursive_value).
    rewrite H1 in H5. cbn in H5. eapply IHeval3.
    case_eq (Nat.ltb n #|mfix|); try rewrite Nat.ltb_lt; eauto.
    rewrite Nat.ltb_ge. intro neq. rewrite nth_overflow in H1; eauto. inversion H1.  
    destruct H1_0. intros s. unfold Ident.Map.add. destruct (Ident.eqb s y); eauto.
    eapply isPure_add_self; eauto. 
  - intro. destruct Hpure as [? [? ?]]. econstructor 6; eauto.
    eapply IHeval; eauto. cbn. now repeat rewrite MRProd.andb_and.
  - intro. destruct Hpure as [[? ?] ?]. econstructor; eauto. eapply IHeval2; eauto. 
    cbn. now repeat rewrite MRProd.andb_and.
  - intro. destruct Hpure as [[? ?] ?]. econstructor; eauto. eapply IHeval2; eauto. 
    cbn. now repeat rewrite MRProd.andb_and. 
    intros s. unfold Ident.Map.add. destruct (Ident.eqb s x); eauto. eapply isPure_heap in H1_; now eauto. 
  - intro. destruct Hpure as [[? ?] ?]. econstructor; eauto. rewrite H1 in IHeval. eapply IHeval; eauto; cbn.
    now repeat rewrite MRProd.andb_and. intro s. eapply isPure_add_self; eauto.
    unfold rfunc, RFunc_build.
    eapply forallb_Forall in H3. clear -H3. induction recs; eauto; cbn. destruct a; cbn in *. inversion H3; subst.
    econstructor; eauto. destruct t0; cbn; eauto. destruct p. cbn in H2. destruct l; cbn ; eauto.
    destruct l; cbn ; eauto. 
  - destruct Hpure. econstructor; eauto. eapply IHeval2; eauto.   
    induction cases; cbn in *. inversion H1. repeat rewrite MRProd.andb_and in H3. destruct H3.   
    destruct a. destruct (existsb _ _); [inversion H1; subst; eauto|]. now eapply IHcases.
  - econstructor; eauto. clear H1. induction H2; [econstructor; eauto|].
    cbn in Hpure. rewrite MRProd.andb_and in Hpure. destruct Hpure. econstructor; eauto. destruct H1; eauto. 
Qed.

Class CompatibleHeap {P P' : Pointer} {H : CompatiblePtr P P'} 
                     {HP : @Heap P} {HP' : @Heap P'} :=  
  { R_heap : (@heap _ HP) -> (@heap _ HP') -> Prop;
    fresh_compat : forall h ptr iptr h' ih ih', 
      R_heap h ih -> fresh h ptr h' -> fresh ih iptr ih' -> 
      R_ptr ptr iptr /\ R_heap h' ih';
    fresh_sim : forall h ptr h' ih, 
      R_heap h ih -> fresh h ptr h' ->
      {ih' & {iptr & fresh ih iptr ih' /\ R_ptr ptr iptr /\ R_heap h' ih'}};
    update_compat : forall h ih ih' ptr ptr' h' (v:list (@value P)) v', 
      R_heap h ih -> update h ptr v h' -> update ih ptr' v' ih' -> 
      R_ptr ptr ptr' -> Forall2 vrel v v' ->
      R_heap h' ih';
    update_sim : forall h ih ptr ptr' h' (v:list (@value P)) v', 
      R_heap h ih -> update h ptr v h' -> R_ptr ptr ptr' -> Forall2 vrel v v' ->
      {ih' & update ih ptr' v' ih' /\ R_heap h' ih'};
    deref_compat : forall h ih ptr ptr' vals vals', 
      R_heap h ih -> deref h ptr vals -> deref ih ptr' vals' -> 
      R_ptr ptr ptr' -> Forall2 vrel vals vals';
    deref_sim : forall h ih ptr ptr' vals, 
      R_heap h ih -> deref h ptr vals -> 
      R_ptr ptr ptr' -> 
      {vals' & deref ih ptr' vals' /\ Forall2 vrel vals vals'}
   }.

Lemma find_match_vrel `{CompatibleHeap}
   scr scr' cases e :
   vrel scr scr' ->
   find_match scr cases = Some e ->
   find_match scr' cases = Some e.
Proof. 
  induction cases as [ | a cases IHcases ]; cbn [SemanticsSpec.find_match]; intros rel Eq.
  - inversion Eq.
  - destruct a.
    destruct existsb eqn:E.
    * inversion Eq. erewrite existsb_ext. 
      2:{ intros. symmetry. eapply cond_correct. eauto.  }
      now rewrite E. 
    * erewrite existsb_ext.
      2:{ intros. symmetry. eapply cond_correct. eauto. }
      rewrite E. eauto.
Qed.

Lemma eval_det {P : Pointer} {H : CompatiblePtr P P} 
               {HP : @Heap P} `{@CompatibleHeap P P _ _ _} 
  globals locals ilocals iglobals e h h' ih ih' v iv :
  (forall nm val val', In (nm, val) globals -> In (nm, val') iglobals -> 
    vrel val val') ->
  vrel_locals locals ilocals ->
  R_heap h ih ->
  eval globals locals h e h' v -> 
  eval iglobals ilocals ih e ih' iv ->
  R_heap h' ih' /\ vrel v iv.
Proof. 
  rename H into _CPtr; rename H0 into _CHeap. 
  intros Hglob Hloc Hheap Heval. revert ih' iv. 
  induction Heval as [ (* lambda_sing *) locals h x e
                 | (* lambda *) locals h x ids e H
                 | (* app_sing *) locals h1 h2 h3 h4 x locals' e e2 v2 e1 v H IHeval1 H0 IHeval2 H1 IHeval3
                 | (* app_sing_Rec *) locals h1 h2 h3 h4 mfix n y e locals' self e2 v2 e1 v H IHeval1 H0 IHeval2 Hnth H1 IHeval3
                 | (* app_fail *) locals h h' e2 e v Heval IHeval Heq
                 | (* app *) locals h h' e3 e2 e1 v vals tag IHeval 
                 | (* var *) 
                 | (* let_body *) | (* let_unnamed *) | (* let_named *) | (* let_rec *)
                 | (* switch *) 
                 | (* block *)  
                 | (* field *) locals h h' idx b vals tag H IHeval | | | | | | 
                 | | | | | | | | | | | | | | | | | | | ]
    in ih, Hheap, ilocals, Hloc |- *.
  (* eval_lambda_sing *) 
  - inversion 1; subst. 
    + split; eauto. econstructor. intros; eauto.      
    + inversion H6.
  (* eval_lambda *)
  - inversion 1; subst.
    + inversion H.
    + split; eauto. econstructor. intros; eauto.
  (* eval_app_sing *)
  - inversion 1; subst. 
    + eapply IHeval1 in H5 as [? ?]; eauto.
      eapply IHeval2 in H7 as [? ?]; eauto.
      inversion H4. subst.  
      eapply IHeval3 in H10 as [? ?]; eauto. 
      intro. eapply vrel_add; eauto. 
    + eapply IHeval1 in H5 as [? ?]; eauto. inversion H4. 
    + eapply IHeval1 in H6 as [? ?]; eauto. inversion H4; subst.
      inversion H9.  
  (* eval_app_sing_rec *)
  - inversion 1; subst.
    + eapply IHeval1 in H5 as [? ?]; eauto. inversion H4. 
    + eapply IHeval1 in H5 as [? ?]; eauto.
      eapply IHeval2 in H6 as [? ?]; eauto.
      inversion H4. subst. pose proof (H18':=H18). 
      eapply (Forall2_nth _ _ _ mfix mfix0 n0 Bad_recursive_value Bad_recursive_value) 
        in H18 as [? ?]; [|now split]. 
      eapply H7 in H8.
      rewrite Hnth in H8; inversion H8; subst.    
      eapply IHeval3 in H11 as [? ?]; eauto. 
      intro. eapply vrel_add; eauto. eapply vrel_locals_add_self; eauto.  
    + eapply IHeval1 in H6 as [? ?]; eauto. inversion H4; subst.
      inversion H9.
  (* eval_app_fail *)
  - inversion 1; subst.
    + eapply IHeval in H2 as [? ?]; eauto. inversion H1; subst. inversion Heq. 
    + eapply IHeval in H2 as [? ?]; eauto. inversion H1; subst. inversion Heq. 
    + eapply IHeval in H3 as [? ?]; eauto. split; eauto. econstructor.
  (* eval_app *)
  - inversion 1; subst. eapply IHeval in H7; eauto.
  (* eval_var *)
  - inversion 1; subst. split; eauto.
  (* eval_let_body *)
  - inversion 1; subst. eapply IHHeval in H2; eauto.
  (* eval_let_unnamed *)
  - inversion 1; subst. eapply IHHeval1 in H6 as [? ?]; eauto.
  (* eval_let_named *)
  - inversion 1; subst. eapply IHHeval1 in H7 as [? ?]; eauto. eapply IHHeval2 in H8; eauto. 
    intro. eapply vrel_add; eauto. 
  (* eval_let_rec *)
  - inversion 1; subst. eapply IHHeval in H7 as [? ?]; eauto. intro. 
    apply vrel_locals_add_self; eauto; unfold rfunc, rfunc0; intros. 
    clear. induction recs; intros; cbn; econstructor; eauto. repeat split.
    1-2: intro H; destruct a, t0; try solve [inversion H]; destruct p;
         destruct l; [inversion H|]; cbn in *; eauto.
    1: { intros. destruct a, t0; try solve [inversion H]; destruct p.
         destruct l; [inversion H|]; cbn in *; eauto.
         destruct l; [inversion H|]. inversion H. }
    1-2: intro H; destruct a, t0; cbn; eauto.
  (* eval_switch *)
  - inversion 1; subst. eapply IHHeval1 in H3 as [? ?]; eauto. eapply find_match_vrel in H; eauto.
    rewrite H5 in H; inversion H; subst. eapply IHHeval2 in H8; eauto.
  (* eval_block *)
  - inversion 1; subst. clear H1. 
    enough (R_heap h' ih' /\ Forall2 vrel vals vals0).
    { destruct H1; split; eauto; econstructor; eauto. }
    generalize dependent ih. revert ih'. generalize dependent vals0. induction H0; intros; inversion H5; subst; clear H5.
    + split; eauto.
    + cbn in *. destruct H0 as [? H0]. eapply H0 in H6 as [? ?]; eauto. edestruct IHForall2_acc. 
      3: exact H3. 3: exact H10. 1-2: lia. split; eauto. 
  (* eval_field *)    
  - inversion 1; subst.
    + eapply IHeval in H5 as [? ?]; eauto. split; eauto. inversion H4; subst. eapply Forall2_nth; eauto. econstructor.
    + eapply IHeval in H6 as [? ?]; eauto. split; eauto. inversion H4; subst. inversion H9.
  (* eval_field_fail *)    
  - inversion 1; subst. 
    + eapply IHHeval in H3 as [? ?]; eauto. split; eauto. inversion H2; subst. inversion H.
    + eapply IHHeval in H4 as [? ?]; eauto. split; eauto. econstructor.
  (* eval *)  
  - inversion 1; subst. 
    pose proof (fresh_compat _ _ _ _ _ _ Hheap H H3) as [? ?].
    eapply update_compat in H5; eauto; try split; repeat econstructor; eauto.   
  (* eval_force_done *)  
  - inversion 1; subst.
    + eapply IHHeval in H5 as [? ?]; eauto. split; eauto. inversion H4; subst. eapply deref_compat in H6; eauto.
      eapply Forall2_nth; eauto. econstructor.
    + eapply IHHeval in H5 as [? ?]; eauto. inversion H4; subst. eapply deref_compat in H6; eauto.
      unshelve epose proof (Forall2_nth _ _ _ _ _ 0 (fail "") (fail "") H6 _); [econstructor|].
      inversion H5; subst; try rewrite <- H14 in H8; try inversion H8.    
      all: try rewrite <- H15 in H8; try inversion H8. rewrite <- H14 in H2. inversion H2.
    + eapply IHHeval in H5 as [? ?]; eauto. inversion H4; subst. inversion H7.
  (* eval_force *)  
  - inversion 1; subst.
    + eapply IHHeval1 in H6 as [? ?]; eauto. inversion H6; subst. eapply deref_compat in H12; eauto.
      unshelve epose proof (Forall2_nth _ _ _ _ _ 0 (fail "") (fail "") H12 _); [econstructor|].
      inversion H9; subst. all: try rewrite <- H10 in H1; try inversion H1.    
      all: try rewrite <- H13 in H1; try inversion H1. rewrite <- H14 in H11. inversion H11.
    + eapply IHHeval1 in H6 as [? ?]; eauto. inversion H6; subst. pose proof (Hptr:=H15). eapply deref_compat in H15; eauto.
      eapply IHHeval2 in H11 as [? ?]; eauto. eapply update_compat in H13; try exact Hptr; eauto. 
      repeat econstructor; eauto.  
      unshelve epose proof (Forall2_nth _ _ _ _ _ 1 (fail "") (fail "") H15 _); [econstructor|].
      rewrite H2 H10 in H14. inversion H14; subst; eauto.    
      unshelve epose proof (Forall2_nth _ _ _ _ _ 1 (fail "") (fail "") H15 _); [econstructor|].
      rewrite H2 H10 in H12. inversion H12; subst; eauto.  
    + eapply IHHeval1 in H6 as [? ?]; eauto. inversion H6; subst. inversion H8.
  (* eval_force_fail *)  
  - inversion 1; subst.
    + eapply IHHeval in H2 as [? ?]; eauto. inversion H2; subst. inversion H.
    + eapply IHHeval in H2 as [? ?]; eauto. inversion H2; subst. inversion H.
    + eapply IHHeval in H2 as [? ?]; eauto. split; eauto; constructor.
  (* eval_global *)  
  - inversion 1; subst. split; eauto.
  (* eval_num_int *)
  - inversion 1; subst. split; eauto; econstructor. 
  (* eval_num_bigint *)
  - inversion 1; subst. split; eauto; econstructor. 
  (* eval_num_float *)
  - inversion 1; subst. split; eauto; econstructor. 
  (* eval_string *)
  - inversion 1; subst. eapply fresh_compat in H5 as [? ?]; eauto.
    eapply update_compat in H7; eauto. split; try econstructor; eauto.
    apply Forall2_init; eauto; econstructor.
  (* eval_numop1 *)
  - inversion 1; subst.
    eapply IHHeval in H6 as [? ?]; eauto. split; eauto. destruct op;
    unfold n; erewrite as_ty_vrel; eauto; eapply truncate_vrel. 
  (* eval_numop2 *)
  - inversion 1; subst.
    eapply IHHeval1 in H7 as [? ?]; eauto. eapply IHHeval2 in H8 as [? ?]; eauto.
    split; eauto. destruct op; destruct b; cbn.
    all : erewrite as_ty_vrel; eauto; erewrite (as_ty_vrel _ v2); eauto ; try eapply truncate_vrel; econstructor.
  (* eval_numop1_neg *)
  - inversion 1; subst.
    eapply IHHeval in H2 as [? ?]; eauto. split; eauto. erewrite as_float_vrel; eauto; econstructor.
  (* eval_numop1_float_fail *)
  - inversion 1; subst. split; eauto; econstructor.
  (* eval__float_fail *)
  - inversion 1; subst. split; eauto; econstructor.
  (* eval__float *)
  - inversion 1; subst. 
    eapply IHHeval1 in H6 as [? ?]; eauto. eapply IHHeval2 in H7 as [? ?]; eauto. split; eauto. unfold v1'0, v2'0, v1', v2'. 
    cbn. erewrite as_float_vrel; eauto. erewrite (as_float_vrel v2); eauto. econstructor.
  (* eval__embed_float *)  
  - inversion 1; subst. 
    eapply IHHeval1 in H6 as [? ?]; eauto. eapply IHHeval2 in H7 as [? ?]; eauto. split; eauto.
    unfold res, res0. cbn. unfold v1'0, v2'0, v1', v2'. 
    erewrite as_float_vrel; eauto. erewrite (as_float_vrel v2); eauto. econstructor.
  (* eval_convert_int *)
  - inversion 1; subst. 
    eapply IHHeval in H6 as [? ?]; eauto. split; eauto. erewrite as_ty_vrel; eauto ; eapply truncate_vrel. 
  (* eval_convert_float *)
  - inversion 1; subst. 
    eapply IHHeval in H5 as [? ?]; eauto. split; eauto. erewrite as_ty_vrel; eauto; econstructor.
  (* eval_convert_float_float *) 
  - inversion 1; subst. 
    eapply IHHeval in H2 as [? ?]; eauto. split; eauto. erewrite as_float_vrel; eauto; econstructor.
  (* eval_vecnew_array *)
  - inversion 1; subst. 
    eapply IHHeval1 in H6 as [? ?]; eauto. eapply IHHeval2 in H9 as [? ?]; eauto.
    eapply fresh_compat in H11 as [? ?]; eauto. eapply update_compat in H14; eauto. 
    + split; eauto. econstructor; eauto.
    + inversion H5; subst; clear H5. eapply Forall2_init; eauto.      
  (* eval_vecnew_bytevec *)
  - inversion 1; subst. 
    eapply IHHeval1 in H7 as [? ?]; eauto. eapply IHHeval2 in H10 as [? ?]; eauto.
    eapply fresh_compat in H13 as [? ?]; eauto. inversion H10; inversion H6; subst. eapply update_compat in H16; eauto. 
    + split; eauto. destruct (_&&_); econstructor; eauto.
    + eapply Forall2_init; eauto.
  (* eval_vecget *)
  - inversion 1; subst.
    eapply IHHeval1 in H5 as [? ?]; eauto. eapply IHHeval2 in H8 as [? ?]; eauto.
    split; eauto. inversion H2; subst; clear H2.  destruct idx', idx'0; inversion H4; try econstructor; eauto; subst. 
    destruct ty0; try econstructor; eauto. destruct (vector_type_eqb _ _); try econstructor.
    eapply deref_compat in H9; eauto. erewrite Forall2_length; eauto. destruct (_ && _); try econstructor.
    apply Forall2_nth; eauto; econstructor.
  (* eval_vecset *)
  - inversion 1; subst.
    eapply IHHeval1 in H6 as [? ?]; eauto. eapply IHHeval2 in H8 as [? ?]; eauto. eapply IHHeval3 in H11 as [? ?]; eauto.
    inversion H5; subst; clear H5. inversion H3; subst; clear H3.  
    eapply deref_compat in H12; eauto. eapply update_compat in H13; eauto. erewrite Forall2_length; eauto. 
    destruct (vector_type_eqb _ _). 2: split; eauto; econstructor.
    2: { clear - H12 H7. set (Z.to_nat _). clearbody n; revert n. induction H12; cbn; try econstructor. destruct n; econstructor; eauto. }
    destruct (_&&_); [|split; try econstructor; eauto].
    destruct ty; [split; try econstructor; eauto|]. destruct v, v0; inversion H7; split; eauto; try econstructor.
    destruct ty; eauto. destruct (_&&_); eauto.     
    destruct ty; try econstructor. destruct (_&&_); econstructor. 
  (* eval_vec_length *)     
  - inversion 1; subst.
    eapply IHHeval in H4 as [? ?]; eauto. split; eauto. inversion H2; subst; clear H2.
    destruct (vector_type_eqb _ _); try econstructor; eauto. eapply deref_compat in H7; eauto.
    erewrite Forall2_length; eauto. econstructor.
Qed.      

Lemma eval_sim {P : Pointer} {H : CompatiblePtr P P} 
               {HP : @Heap P} `{@CompatibleHeap P P _ _ _} 
  globals locals ilocals iglobals e h h' ih v :
  (forall nm val, In (nm, val) globals -> {val' & In (nm, val') iglobals /\ vrel val val'}) ->
  vrel_locals locals ilocals ->
  R_heap h ih ->
  eval globals locals h e h' v -> 
  ∥{ ih' & { iv & eval iglobals ilocals ih e ih' iv /\  R_heap h' ih' /\ vrel v iv}}∥.
  rename H into _CPtr; rename H0 into _CHeap. 
  intros Hglob Hloc Hheap Heval.
  induction Heval as [ (* lambda_sing *) locals h x e
                 | (* lambda *) locals h x ids e H
                 | (* app_sing *) locals h1 h2 h3 h4 x locals' e e2 v2 e1 v H IHeval1 H0 IHeval2 H1 IHeval3
                 | (* app_sing_Rec *) locals h1 h2 h3 h4 mfix n y e locals' self e2 v2 e1 v H IHeval1 H0 IHeval2 Hnth H1 IHeval3
                 | (* app_fail *) locals h h' e2 e v Heval IHeval Heq
                 | (* app *) locals h h' e3 e2 e1 v vals tag IHeval 
                 | (* var *) 
                 | (* let_body *) | (* let_unnamed *) | (* let_named *) | (* let_rec *)
                 | (* switch *) 
                 | (* block *)  
                 | (* field *) locals h h' idx b vals tag H IHeval | | | | | | 
                 | | | | | | | | | | | | | | | | | | | ]
    in ih, Hheap, ilocals, Hloc |- *.
  (* eval_lambda_sing *) 
  - sq. exists ih. exists (Func (ilocals, x , e)). repeat split; eauto; econstructor; eauto.  
  (* eval_lambda *)
  - sq. exists ih. exists (Func (ilocals, x, Mlambda (ids, e))). repeat split; eauto; econstructor; eauto.
  (* eval_app_sing *)
  - specialize (IHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. inversion H3; subst; clear H3. 
    specialize (IHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]].
    assert (Hloc' : vrel_locals (Ident.Map.add x v2 locals') (Ident.Map.add x iv2 locals'0)).
    { intro. eapply vrel_add; eauto. }
    specialize (IHeval3 _ _ Hloc' Hheap2) as [[ih3 [iv3 [? [Hheap3 ?]]]]]. sq.
    exists ih3. exists iv3; repeat split; eauto. econstructor; eauto.
  (* eval_app_sing_rec *)
  - specialize (IHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. inversion H3; subst; clear H3. 
    specialize (IHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]].
    assert (Hloc' : vrel_locals (Ident.Map.add y v2 (add_self self mfix locals')) (Ident.Map.add y iv2 (add_self self mfix' locals'0))).
    { intro. eapply vrel_add; eauto. eapply vrel_locals_add_self; eauto. }
    specialize (IHeval3 _ _ Hloc' Hheap2) as [[ih3 [iv3 [? [Hheap3 ?]]]]]. sq.
    exists ih3. exists iv3; repeat split; eauto. econstructor 4; eauto.
    eapply (Forall2_nth _ _ _ mfix mfix' n Bad_recursive_value Bad_recursive_value) 
        in H10 as [? ?]; [|now split]. 
    eapply H7; eauto. 
  (* eval_app_fail *)
  - specialize (IHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq. 
    exists ih1. eexists. repeat split; eauto. econstructor 5; eauto. inversion H0; subst; try econstructor; try inversion Heq. econstructor.
  (* eval_app *)
  - specialize (IHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq. 
    exists ih1. eexists. repeat split; eauto. econstructor 6; eauto.
  (* eval_var *)
  - sq. exists ih; eexists; repeat split; eauto. econstructor 7; eauto. 
  (* eval_let_body *)
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq.
    exists ih1; eexists; repeat split; eauto. econstructor 8; eauto. 
  (* eval_let_unnamed *)
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    specialize (IHHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]]. sq.
    exists ih2; eexists; repeat split; eauto. econstructor 9; eauto. 
  (* eval_let_named *)
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    assert (Hloc' : vrel_locals (Ident.Map.add x v1 locals) (Ident.Map.add x iv1 ilocals)).
    { intro. eapply vrel_add; eauto. }
    specialize (IHHeval2 _ _ Hloc' Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]]. sq.
    exists ih2; eexists; repeat split; eauto. econstructor 10; eauto. 
  (* eval_let_rec *)
  - assert (Hloc' : vrel_locals newlocals (add_self self rfunc ilocals)). 
    { intro. rewrite H. eapply vrel_locals_add_self; eauto.
      unfold rfunc. clear. induction recs; econstructor; eauto.
      split; intros; [|split; intros].
      - split; intro H; destruct a, t0; try solve [inversion H];
        destruct p; destruct l; try solve [inversion H]; cbn in *; eauto.
      - destruct a, t0; try solve [inversion H];
        destruct p; destruct l; try solve [inversion H]; cbn in *; eauto. 
        destruct l; inversion H. 
      - split; intro H; destruct a, t0; eauto. }
    specialize (IHHeval _ _ Hloc' Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq.
    exists ih1; eexists; repeat split; eauto. econstructor 11; eauto. 
  (* eval_switch *)
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    specialize (IHHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]]. sq.
    exists ih2; eexists; repeat split; eauto. econstructor 12; eauto. eapply find_match_vrel; eauto.
  (* eval_block *)
  - enough (∥ {ih' : heap & {ivals & Forall2_acc (eval iglobals ilocals) ih es ih' ivals /\ R_heap h' ih' /\ Forall2 vrel vals ivals}}∥).
    { sq. destruct H1 as [ih1 [iv1 [? [? ?]]]]. exists ih1; exists (Block (tag, iv1)). repeat split; try econstructor; eauto. erewrite <- Forall2_length; eauto. }
    revert ih Hheap. induction H0; intros.  
    + sq. exists ih; eexists; repeat split; eauto; try econstructor; eauto.
    + destruct H0. eapply H2 in Hheap as [[ih1 [iv1 [? [Hheap1 ?]]]]]; eauto.
      eapply IHForall2_acc in Hheap1 as [[? [? [? [? ?]]]]]. sq. repeat eexists; repeat split; eauto. 
      econstructor; eauto. cbn in H; lia. 
  (* eval_field *)    
  - specialize (IHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. 
    inversion H3; subst; clear H3. sq.  
    exists ih1. exists (nth (int_to_nat idx) vals' (fail "")). repeat split ; eauto.
    + econstructor 14; eauto. all: erewrite <- Forall2_length; eauto.
    + eapply Forall2_nth; eauto. econstructor. 
  (* eval_field_fail *)    
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq.  
    exists ih1. exists (fail "not a block"). repeat split ; eauto.
    + econstructor 15; eauto. inversion H1; subst; eauto.
    + econstructor.
  (* eval *)  
  - sq. eapply fresh_sim in H as [ih' [iptr [? [? ?]]]]; eauto. 
    eapply update_sim with (v':=[not_evaluated; Lazy (ilocals, e)]) in H0 as [ih'' [? ?]]; eauto. 
    + exists ih''. exists (Thunk iptr). repeat split; try econstructor; eauto. 
    + repeat econstructor; eauto.
  (* eval_force_done *)  
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. inversion H4; subst; clear H4.
    eapply deref_sim in H as [vals' [? ?]]; eauto. pose proof (H1_copy := H1).
    eapply (Forall2_nth _ _ _ vals vals' 0 (fail "") (fail "")) in H1; [|econstructor]. sq.   
    exists ih1. exists (nth 0 vals' (fail "")). repeat split; eauto; econstructor; eauto.
    + erewrite <- Forall2_length; eauto.
    + inversion H1; eauto. rewrite <- H5 in H2. inversion H2.
  (* eval_force *)  
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. inversion H5; subst; clear H5.
    eapply deref_sim in H as [vals' [? ?]]; eauto. pose proof (H5_copy := H5).
    eapply (Forall2_nth _ _ _ vals vals' 0 (fail "") (fail "")) in H5; [|econstructor]. pose proof (H5_copy' := H5_copy).
    eapply (Forall2_nth _ _ _ vals vals' 1 (fail "") (fail "")) in H5_copy; [|econstructor].
    rewrite H2 in H5_copy. inversion H5_copy; subst; clear H5_copy.   
    specialize (IHHeval2 _ _ H8 Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]]. 
    eapply update_sim with (v':=[iv2; Lazy (locals'0, e)]) in H3 as [ih3 [? ?]]; eauto.
    2: repeat econstructor; eauto. sq.   
    exists ih3. exists iv2. repeat split; eauto. econstructor 18; eauto.
    + erewrite <- Forall2_length; eauto. 
    + inversion H5; try rewrite <- H12 in H1; try rewrite <- H13 in H1; inversion H1; eauto.
  (* eval_force_fail *)  
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq.
    exists ih1. exists (fail "not a lazy value"). repeat split; try econstructor 19; try econstructor; eauto.
    inversion H1; try rewrite <- H3 in H; inversion H; eauto. 
  (* eval_global *)  
  - eapply Hglob in H as [v' [? ?]]. sq. 
    exists ih; exists v'. repeat split; try econstructor; eauto.  
  (* eval_num_int *)
  - sq. do 2 eexists; repeat split; eauto; econstructor.
  (* eval_num_bigint *)
  - sq. do 2 eexists; repeat split; eauto; econstructor.
  (* eval_num_float *)
  - sq. do 2 eexists; repeat split; eauto; econstructor.
  (* eval_string *)
  - sq. eapply fresh_sim in H0 as [ih' [iptr [? [? ?]]]]; eauto. 
    eapply update_sim with (v':=str) in H1 as [ih'' [? ?]]; eauto.
    + exists ih''. exists (Vec (Bytevec, iptr)). repeat split; try econstructor; eauto. 
    + eapply Forall2_init; intros; econstructor. 
  (* eval_numop1 *)
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq.
    do 2 eexists; repeat split; eauto; [ econstructor 25 ; eauto |]. 
    inversion H0; subst; econstructor.
  (* eval_numop2 *)
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    specialize (IHHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]]. sq.
    do 2 eexists; repeat split; eauto; [ econstructor 26 ; eauto |].
    destruct op; inversion H0; inversion H2; subst; try econstructor.
  (* eval_numop1_neg *)
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq.
    do 2 eexists; repeat split; eauto; [ econstructor 27 ; eauto |]. 
    inversion H0; subst; econstructor.
  (* eval_numop1_float_fail *)
  - sq. do 2 eexists; repeat split; eauto; [ econstructor 28 ; eauto |]. 
    econstructor.
  (* eval__float_fail *)
  - sq. do 2 eexists; repeat split; eauto; [ econstructor 29 ; eauto |]. 
    econstructor.
  (* eval__float *)
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    specialize (IHHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]]. sq.
    do 2 eexists; repeat split; eauto; [ econstructor 30 ; eauto |].
    destruct op; inversion H0; inversion H2; subst; try econstructor. 
  (* eval__embed_float *)  
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    specialize (IHHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]]. sq.
    do 2 eexists; repeat split; eauto; [ econstructor 31 ; eauto |].
    destruct op; inversion H0; inversion H2; subst; try econstructor. 
  (* eval_convert_int *)
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq.
    do 2 eexists; repeat split; eauto; [ econstructor 32 ; eauto |]. 
    inversion H0; subst; econstructor.
  (* eval_convert_float *)
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq.
    do 2 eexists; repeat split; eauto; [ econstructor 33 ; eauto |]. 
    inversion H0; subst; econstructor.
  (* eval_convert_float_float *) 
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]]. sq.
    do 2 eexists; repeat split; eauto; [ econstructor 34 ; eauto |]. 
    inversion H0; subst; econstructor. 
  (* eval_vecnew_array *)
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    specialize (IHHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]]. sq.
    eapply fresh_sim in H1 as [ih' [iptr [? [? ?]]]]; eauto. 
    eapply update_sim with (v':=(List.init (Z.to_nat len') (fun _ => iv2))) in H2 as [ih'' [? ?]]; eauto. 
    do 2 eexists; repeat split; eauto; [ econstructor 35 ; eauto |].
    + inversion H4; subst; eauto.
    + econstructor; eauto.
    + apply Forall2_init; eauto.
  (* eval_vecnew_bytevec *)
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    specialize (IHHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]].
    inversion H5; subst; clear H5. inversion H7; subst; clear H7. sq.  
    eapply fresh_sim in H2 as [ih' [iptr [? [? ?]]]]; eauto.
    eapply update_sim with (v':=(List.init (Z.to_nat len') (fun _ => (value_Int (Int, k))))) in H3 as [ih'' [? ?]]; eauto. 
    do 2 eexists; repeat split; eauto; [ econstructor 36 ; eauto |].
    + destruct (_&&_); econstructor; eauto. 
    + apply Forall2_init; intros; econstructor.
  (* eval_vecget *)
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    specialize (IHHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]].
    inversion H1; subst; clear H1.  
    eapply deref_sim in H as [vals' [? ?]]; eauto. sq. 
    do 2 eexists; repeat split; eauto; [ econstructor 37 ; eauto |].
    inversion H3; subst; try econstructor.
    destruct ty0; try econstructor. destruct (vector_type_eqb _ _); try econstructor.
    erewrite Forall2_length; eauto. destruct (_&&_); try econstructor; eauto.
    eapply Forall2_nth; eauto. econstructor.
  (* eval_vecset *)
  - specialize (IHHeval1 _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    specialize (IHHeval2 _ _ Hloc Hheap1) as [[ih2 [iv2 [? [Hheap2 ?]]]]].
    specialize (IHHeval3 _ _ Hloc Hheap2) as [[ih3 [iv3 [? [Hheap3 ?]]]]].
    inversion H2; subst; clear H2. inversion H4; subst; clear H4.
    eapply deref_sim in H as [vals' [? ?]]; eauto. 
    eapply update_sim with (v':=List.set vals' (Z.to_nat i) iv3) in H0 as [ih'' [? ?]]; eauto. sq. 
    do 2 eexists; repeat split; [ econstructor 38 ; eauto | |].
    + destruct (vector_type_eqb _ _); eauto. erewrite Forall2_length; eauto. destruct (_&&_); try econstructor; eauto.
      destruct ty; try econstructor; eauto. inversion H6; eauto.
      destruct ty; try econstructor; eauto. destruct (_&&_); try econstructor; eauto.
    + destruct (vector_type_eqb _ _); try econstructor. erewrite Forall2_length; eauto. destruct (_&&_); try econstructor; eauto.
      destruct ty; try econstructor; eauto. inversion H6; try econstructor; eauto.
      destruct ty; try econstructor; eauto. destruct (_&&_); try econstructor; eauto. 
    + clear -H2 H6. generalize (Z.to_nat i). induction H2; cbn; try econstructor. destruct n; econstructor; eauto.
  (* eval_vec_length *)     
  - specialize (IHHeval _ _ Hloc Hheap) as [[ih1 [iv1 [? [Hheap1 ?]]]]].
    inversion H1; subst; clear H1.
    eapply deref_sim in H as [vals' [? ?]]; eauto. sq. 
    do 2 eexists; repeat split; eauto; [ econstructor 39 ; eauto |]. 
    destruct (vector_type_eqb _ _); try econstructor; eauto.
    erewrite Forall2_length; eauto. econstructor.
Qed.