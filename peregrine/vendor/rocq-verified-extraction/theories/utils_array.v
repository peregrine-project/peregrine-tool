From Stdlib Require Import ssreflect.

From MetaRocq.Utils Require Import MRList.

From Stdlib Require Import ZArith Array.PArray List Floats Lia.
Import ListNotations.

Require Import Malfunction.Malfunction.
From Stdlib Require Import Uint63.

From MetaRocq.PCUIC Require Import PCUICFirstorder.

Definition int_to_nat (i : int) : nat :=
  Z.to_nat (Int63.to_Z i).

Definition int_of_nat n := Uint63.of_Z (Stdlib.ZArith.BinInt.Z.of_nat n).

Lemma int_of_to_nat i :
  int_of_nat (int_to_nat i) = i.
Proof.
  unfold int_of_nat, int_to_nat.
  rewrite Z2Nat.id.
  1:eapply Int63.to_Z_bounded.
  now rewrite Int63.of_to_Z.
Qed.

Lemma int_to_of_nat i :
  (Z.of_nat i < Int63.wB)%Z ->
  int_to_nat (int_of_nat i) = i.
Proof.
  unfold int_of_nat, int_to_nat.
  intros ?.
  rewrite Int63.of_Z_spec.
  rewrite Z.mod_small. 1:lia.
  now rewrite Nat2Z.id.
Qed.

Lemma wb_max_length :
  int_to_nat max_length < Z.to_nat Int63.wB.
Proof.
  cbn. lia.
Qed.

Arguments Int63.wB : simpl never.
Arguments max_length : simpl never.

Ltac lia_max_length := 
  pose proof wb_max_length; unfold max_length in *; cbn in *; lia.

Module List. 
  Fixpoint mapi_ {A B} (f : nat -> A -> B) (l : list A) (n:nat) : list B :=
    match l with
      | [] => []
      | x :: l' =>  f n x :: mapi_ f l' (S n) 
    end.

  Definition mapi {A B} (f : nat -> A -> B) l := mapi_ f l 0. 

  Definition init {A} (size : nat) (f : nat -> A) : list A := map f (seq 0 size).

  Fixpoint set {A} (l : list A) (n : nat) (a:A) : list A 
   := match l , n with
     [] , _ =>  []
   | x :: l , 0 => a :: l
   | x :: l , S n => x :: set l n a
   end.

  Lemma length_set A (l : list  A) n a : 
   List.length (set l n a) = List.length l.
  Proof. 
   revert n. induction l; destruct n; cbn; eauto.
   now f_equal. 
  Qed.

  Lemma nth_set_same A (l : list A) n a d :
    (n < List.length l) -> nth n (set l n a) d = a.
  Proof. 
    revert n. induction l; destruct n; cbn ; intros; try solve [inversion H]; eauto. 
    apply IHl. now apply Nat.succ_lt_mono in H.
  Qed. 

  Lemma nth_set_other A (l : list A) n m a d : 
  n <> m -> nth m (set l n a) d = nth m l d.
  Proof. 
   revert n m; induction l; intros; cbn; eauto.
   destruct n; destruct m; cbn; try congruence.
   eapply IHl; now eauto.  
  Qed. 

End List. 

Definition Forall2Array {A B:Type} (R : A -> B -> Prop) 
  (l:list A) (a:array B) default := 
    List.length l = int_to_nat (PArray.length a) /\
    forall i:int, int_to_nat i < List.length l -> R (nth (int_to_nat i) l default ) a.[i].

Inductive
  Forall2_acc {X A B : Type} (R : X -> A -> X -> B -> Prop) : X -> list A -> X -> list B -> Prop :=
    Forall2_acc_nil : forall x, Forall2_acc R x [] x []
    | Forall2_acc_cons : forall (x y z : X) (a : A) (b : B) 
                            (l : list A) (l' : list B) ,
                     R x a y b -> Forall2_acc R y l z l' -> Forall2_acc R x (a :: l) z (b :: l').
    
Fixpoint map_acc {A B S: Type} (f : S -> A -> S * B) (s:S) (l : list A) : S * list B :=
  match l with
  | [] => (s , [])
  | a :: t => let (s',b) := f s a in 
              let (s'',bs) := map_acc f s' t in (s'', b :: bs)
  end.

Lemma Forall2_acc_map {S S' A B B'} (R : S -> S' -> Prop) (RB : B -> B' -> Prop)
        (f : S' -> A -> S' * B') (P : S -> A -> S -> B -> Prop) x x' y l1 l2 :
  Forall2_acc P x l1 y l2 ->
  (forall x x' a b y, R x x' -> P x a y b -> let (y' , b') := f x' a in R y y' /\ RB b b') ->
  R x x' -> 
  let (y' , l') := map_acc f x' l1 in R y y' /\ Forall2 RB l2 l'.
Proof.
  intros H H'. revert x'. induction H; cbn; intros x' Hx; f_equal; eauto.
  specialize (H' _ _ _ _ _ Hx H). destruct (f _ _ ) as (s',b').
  destruct H'. specialize (IHForall2_acc _ H1). destruct (map_acc _ _ _).
  destruct IHForall2_acc. split; eauto.  
Qed.

Lemma Forall2_acc_length {X A B R x l y l'} : @Forall2_acc X A B R x l y l' -> List.length l = List.length l'.
Proof. 
  induction 1; cbn; now eauto.
Qed.   

Lemma Forall2_length {A B P l l'} : @Forall2 A B P l l' -> List.length l = List.length l'.
Proof. 
  induction 1; cbn; now eauto.
Qed.
    
Fixpoint Array_of_List' {A} count (l : list A) (a : array A) :=
  match l with
  | [] => a
  | x :: l => Array_of_List' (S count) l (PArray.set a (int_of_nat count) x)
  end.

Definition Array_of_list {A} (def : A) (l : list A) :=
  Array_of_List' 0 l (PArray.make (int_of_nat (List.length l)) def).

Definition Array_init {A} (size : int) f :=
  let g := fun x => (f (int_of_nat x)) in
  @Array_of_list A (g 0) (map g (seq 0 (Z.to_nat (Int63.to_Z size)))).


Lemma Array_of_list'_get {A} s l (a : array A) i :
  i < s + List.length l ->
  (s + List.length l < Z.to_nat Int63.wB) ->
  s + List.length l <= int_to_nat (PArray.length a) ->
  PArray.get (Array_of_List' s l a) (int_of_nat i) =
    if (i <? s)%nat then
      a.[int_of_nat i]
    else
      nth (i - s) l (a.[int_of_nat i]).
Proof.
  intros Hl Hs Ha.
  induction l as [ | ? ? IHl] in s, i, a, Hl, Hs, Ha |- *.
  - destruct (Nat.ltb_spec i s).
    + cbn. reflexivity.
    + cbn. destruct (i - s); reflexivity.
  - rewrite IHl. 
    + cbn in Hl. lia.
    + cbn [Datatypes.length] in Hs. lia.
    + rewrite PArray.length_set. cbn [Datatypes.length] in Ha. lia.
    + fold (int_of_nat s). destruct (Nat.ltb_spec i s) as [H | H].
      * destruct (Nat.ltb_spec i (S s)) as [H0 | H0]; try lia.
        rewrite get_set_other.
        -- intros E. eapply (f_equal int_to_nat) in E.
           rewrite !int_to_of_nat in E.
           all:assert (H1 : s < Z.to_nat Int63.wB) by lia.
           all:eapply inj_lt in H1.
           all:rewrite Z2Nat.id in H1. all:lia. 
        -- reflexivity.
      * destruct (Nat.ltb_spec i (S s)); try lia.
        -- assert (i = s) by lia. subst.
           rewrite get_set_same.
           ++ eapply Int63.ltb_spec.
              1:eapply Z2Nat.inj_lt.
              1:eapply Int63.to_Z_bounded.
              1:eapply Int63.to_Z_bounded. 
              fold (int_to_nat (int_of_nat s)).
              rewrite int_to_of_nat. 1:lia.
              unfold int_to_nat in Ha. lia.
           ++ cbn. destruct s. 1:reflexivity.
              rewrite Nat.sub_diag. reflexivity.
        -- cbn. destruct (i - s) as [ | n] eqn:E.
           ++ lia.
           ++ assert (H1 : i - S s = n) by lia. rewrite H1.
              eapply nth_indep.
              cbn in Hl. lia.
Qed.

Lemma Array_of_list_get {A} (a : A) l i :
  (i < Z.to_nat Int63.wB) ->
  List.length l <= int_to_nat max_length ->
  i < List.length l ->
  (Array_of_list a l).[int_of_nat i] = nth i l a.
Proof.
  unfold Array_of_list. intros Hs Hl Hi.
  rewrite Array_of_list'_get.
  + assumption.
  + pose proof wb_max_length. move: Hl H. generalize (int_to_nat max_length). lia.
  + rewrite PArray.length_make.
    fold (int_of_nat (Datatypes.length l)).
    destruct (Int63.lebP (int_of_nat (Datatypes.length l)) max_length) as [ | n ].
    * rewrite int_to_of_nat.
      1:eapply Z2Nat.inj_lt. all: pose proof wb_max_length; lia.
    * destruct n.
      epose proof (int_to_of_nat (Datatypes.length l) _) as H.
      eapply Z2Nat.inj_le.
      1:eapply Int63.to_Z_bounded.
      1:eapply Int63.to_Z_bounded.
      unfold int_to_nat in H. rewrite H.
      unfold int_to_nat in Hl. exact Hl.
      Unshelve. all:try generalize wb_max_length; move: Hl; generalize (int_to_nat max_length); lia.
  + destruct (Nat.ltb_spec i 0).
    move: Hl. generalize (int_to_nat max_length); try lia.
    rewrite Nat.sub_0_r.
    eapply nth_indep. move: Hl; generalize (int_to_nat max_length); lia.
Qed.

Lemma Array_of_list_get_again {A : Set} i s (l : list A) a :
  i >= s + List.length l ->
  i < Z.to_nat Int63.wB ->
  (Array_of_List' s l a).[int_of_nat i]  = PArray.get a (int_of_nat i).
Proof.
  induction l as [ | ? l IHl ] in s, i, a |- *; intros Hi Ha.
  - cbn. reflexivity.
  - cbn. rewrite IHl. 
    + cbn in Hi. lia.
    + eauto.
    + rewrite get_set_other. 2:reflexivity.
      fold (int_of_nat s).
      intros H. eapply (f_equal int_to_nat) in H.
      rewrite !int_to_of_nat in H.
      * eapply inj_ge in Hi. cbn in Hi. 
        rewrite Nat2Z.inj_add in Hi. cbn; lia.
      * eapply inj_lt in Ha.
        rewrite Z2Nat.id in Ha; eauto.  
        unfold Int63.wB. cbn; lia.  
      * subst. cbn in Hi. lia.
Qed.

Ltac abs_max_length :=
  let e := fresh in set (e := int_to_nat max_length) in *; clearbody e.

Lemma Array_of_list_S A default n a (l:list A) : 
  n < Datatypes.length l ->
  S (Datatypes.length l) <= int_to_nat max_length ->
  (Array_of_list default (a :: l)).[int_of_nat (S n)] = 
  (Array_of_list default l).[int_of_nat n].
Proof.
  intros. pose proof wb_max_length.
  repeat rewrite Array_of_list_get; try (abs_max_length; cbn in *; lia).
  eauto.
Qed.

Lemma Array_of_list'_length A k (l:list A) a :
  PArray.length (Array_of_List' k l a) =
  PArray.length a.
Proof. 
  revert k a. induction l; [reflexivity|].
  intros; cbn. rewrite IHl. now rewrite PArray.length_set.
Qed.

Lemma Array_of_list_length A default (l:list A) :
  Datatypes.length l < int_to_nat max_length -> 
  int_to_nat (PArray.length (Array_of_list default l)) =
  List.length l.
Proof.
  unfold Array_of_list. rewrite Array_of_list'_length.
  pose proof (Hmax := wb_max_length).
  rewrite PArray.length_make. intro H. 
  assert (Hl: (int_of_nat (Datatypes.length l) ≤? max_length)%uint63 = true).
  { apply leb_spec. repeat rewrite Int63.of_Z_spec. rewrite Z.mod_small; [abs_max_length; cbn in *; lia |].
    clear Hmax. unfold max_length in *; cbn in *. lia. }
  rewrite Hl. apply int_to_of_nat. cbn in *; lia. 
Qed.

Lemma Forall2Array_init {A B:Type} (R : A -> B -> Prop) n f g
   default :
   n < int_to_nat max_length ->
   (forall k, k < n ->  R (f k) (g (int_of_nat k))) ->
   Forall2Array R (List.init n f) (Array_init (int_of_nat n) g) default.
Proof.
  intros Hmax HR. unfold Forall2Array.
  assert (HwB : (Z.of_nat n < Int63.wB)%Z).
  { clear -Hmax; lia_max_length. }
  rewrite Array_of_list_length. 
  { rewrite length_map length_seq. epose (int_to_of_nat n). 
    unfold int_to_nat in e. now rewrite e. }
  repeat rewrite length_map length_seq. split; [symmetry; apply int_to_of_nat|]; eauto.
  intros i Hi. pose (HR (int_to_nat i) Hi). 
  unfold Array_init. rewrite <- (int_of_to_nat i). 
  rewrite Array_of_list_get; abs_max_length; try lia.
  1-2: rewrite length_map length_seq; pose (e := int_to_of_nat n HwB);
       unfold int_to_nat in e; rewrite e; lia.
  rewrite int_of_to_nat. unfold List.init.  
  set (k := int_to_nat i) in *. clearbody k; clear i.
  rewrite map_nth. erewrite nth_indep. erewrite map_nth.
  pose (int_to_of_nat n HwB). 
  unfold int_to_nat in e. rewrite e. apply HR. rewrite seq_nth; lia.
  rewrite length_map length_seq; lia.
Qed. 


Lemma Forall2_init {A B:Type} (R : A -> B -> Prop) n f g :
   (forall k, k < n ->  R (f k) (g k)) ->
   Forall2 R (List.init n f) (List.init n g).
Proof.
  unfold List.init. intro Hfg. assert (0 + n <= n) by lia. revert H. generalize 0. generalize n at 1 3 4.   
  induction n0; cbn; intros; econstructor; eauto.
  - eapply Hfg. lia.
  - eapply IHn0. lia.
Qed. 

Lemma Forall2Array_cst {A B:Type} (R : A -> B -> Prop) n v v'
   default :
   n <= int_to_nat max_length ->
   R v v' ->
   Forall2Array R (List.init n (fun _ => v)) (make (int_of_nat n) v') default.
Proof. 
  intros Hmax HR. unfold Forall2Array.    
  repeat rewrite length_map length_seq PArray.length_make.
  case_eq (int_of_nat n ≤? max_length)%uint63.
  - split; [symmetry; apply int_to_of_nat|]; eauto.
    lia_max_length. 
    intros i Hi. rewrite get_make.
    set (k := int_to_nat i) in *. unfold List.init.
    clearbody k; clear i. erewrite nth_indep.
    erewrite map_nth. Unshelve. 3: exact 0.   exact HR.
    now rewrite length_map length_seq.
  - intro abs. pose (leb_spec (int_of_nat n) (max_length)). destruct i. 
    rewrite H0 in abs.
    rewrite Int63.of_Z_spec. 
    rewrite Z.mod_small; clear H H0; try lia_max_length.
    inversion abs.
Qed.     

Lemma filter_length {A} (l : list A) f :
  List.length (filter f l) <= List.length l.
Proof.
  induction l; cbn.
  - lia.
  - destruct (f a); cbn; lia.
Qed.

Fixpoint to_list {A} (f : nat -> A) (size : nat) : list A :=
  match size with 
  | O => []
  | S n => to_list f n ++ [f n]
  end. 

Lemma to_list_length {A} (f : nat -> A) (size : nat) : 
  List.length (to_list f size) = size.
Proof.
  induction size; cbn; eauto. rewrite length_app. cbn; lia.
Qed. 

Lemma to_list_nth {A} (f : nat -> A) (size : nat) n d : 
  n < size ->  
  nth n (to_list f size) d = f n.
Proof.
  induction size; [lia |]. cbn. 
  case_eq (Nat.eqb n size); intros.
  cbn. apply Nat.eqb_eq in H. rewrite H.
  erewrite app_nth2; rewrite to_list_length; [|cbn in *; lia].
  now rewrite Nat.sub_diag.
  eapply Nat.eqb_neq in H.
  erewrite app_nth1. apply IHsize. lia. rewrite to_list_length; lia.
Qed. 

Lemma filter_rev A (l:list A) f : filter f (rev l) = rev (filter f l).
Proof.
  induction l; cbn; eauto. rewrite filter_app IHl; cbn. 
  destruct (f a); cbn; eauto.
  apply app_nil_r.
Qed. 

Lemma filter_firstn A k f (l:list A) : 
  k < #| filter f l| -> 
  exists k', k' < #| l | /\ k = List.length (filter f (firstn k' l)) /\
  exists a, nth_error l k' = Some a /\ is_true (f a).
Proof.
  intros H.
  induction l using rev_ind.
  - cbn in *. lia.
  - rewrite filter_app in H. cbn in *. rewrite length_app in H.
    rewrite length_app.
    destruct (f x) eqn:E; cbn in *.
    + assert (k = #|filter f l| \/ k < #|filter f l|) as [Hl | Hl] by lia.
      * subst. exists (List.length l).
        repeat split; eauto; try lia.
        rewrite firstn_app_left; lia.
        exists x. split; eauto. rewrite nth_error_app2; try lia. 
        now rewrite Nat.sub_diag. 
      * eapply IHl in Hl as (k' & ? & ? & a & ? & ?); subst.
        assert (k' < List.length l).
        { pose proof (nth_error_Some l k') as [HH _]. rewrite H2 in HH. lia. }
        exists k'. repeat split; try lia.
        -- rewrite firstn_app. 
           assert (k' - List.length l = 0) as -> by lia.
          now rewrite firstn_O app_nil_r.
        -- exists a. 
           rewrite nth_error_app1; eauto.
    + rewrite <- plus_n_O in H. eapply IHl in H as (k' & ? & ? & a & ? & ?); subst.
      assert (k' < List.length l).
      { pose proof (nth_error_Some l k') as [HH _]. rewrite H1 in HH. lia. }
      exists k'. repeat split; try lia.
      -- rewrite firstn_app. 
         assert (k' - List.length l = 0) as -> by lia.
        now rewrite firstn_O app_nil_r.
      -- exists a. 
         rewrite nth_error_app1; eauto.
Qed.

Lemma filter_firstn' A k f (l:list A) : 
  k < #| filter f l| -> 
  exists k', k' < #| l | /\ k = List.length (filter f (firstn k' l)) /\
  exists a, nth_error l k' = Some a /\ nth_error (filter f l) k = Some a /\ is_true (f a).
Proof.
  intros. apply filter_firstn in H. destruct H as [? [? [? [? [? ?]]]]].
  repeat (eexists; repeat split; eauto).
  apply PCUICReduction.nth_error_firstn_skipn in H1.
  rewrite H1. repeat rewrite filter_app.
  cbn. rewrite H2. now apply nth_error_snoc.
Qed.

Lemma filter_nth_error A (f : A -> bool) (x : A) (l : list A) k: 
       nth_error (filter f l) k = Some x -> In x l /\ f x = true.
Proof.
  intros. apply nth_error_In in H.
  now apply filter_In in H.
Qed. 


