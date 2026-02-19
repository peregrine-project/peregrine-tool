From Stdlib Require Import Lia List Peano Nat.
From Stdlib Require Import Strings.String.
From CakeML Require Import ast.
From CakeML Require Import namespace.
From CakeML Require Import semanticPrimitives.
From CakeML Require Import functions.
From CakeML Require Import bigstep.
From CakeML Require Import smallstep.
From CakeML Require Import smallstep_rel.
Import ListNotations.

Lemma rw_rev_2_elt : forall A (l:list A) (e1:A) (e2:A), (rev l) = [e1;e2] <-> l = [e2;e1].
Proof.
	intros. split; intro.
	* now apply rev_inj.
	* now  rewrite H.
Qed.

Lemma rev_symm : forall A (l:list A) (l':list A), rev l = l' <-> l = rev l'.
Proof.
	intros.
	split; intro.
	- apply rev_inj. rewrite rev_involutive. auto.
	- apply rev_inj. rewrite rev_involutive. auto.
Qed.

Lemma rev_concat_1_elt : forall A (l:list A) e, rev l ++ [e] = rev (e::l).
Proof.
	easy.
Qed.

Lemma rev_3 : forall A e1 e2 es h (l:list A), rev(e1 :: rev (e2 :: es)) = h :: l -> l = es ++ [e1]/\h=e2.
Proof.
	intros.
	rewrite <- rev_concat_1_elt in H.
	rewrite rev_involutive in H.
	simpl in H.
	inversion H.
	easy.
Qed.

Lemma eq_not_mem : forall a l, NOT_MEM conN (fun x0 y : conN => negb (x0 =? y)%string) a l = true <-> ~ In a l.
Proof.
	intros.
	split; intro.
	- intro. unfold NOT_MEM in H. induction l; try easy. 
		inversion H0.
		+ apply andb_prop in H. destruct H. apply Bool.negb_true_iff in H. apply eqb_neq in H. easy. 
		+ apply andb_prop in H. destruct H. apply IHl; try easy.
	- unfold NOT_MEM. induction l; try easy.
	apply Bool.andb_true_iff. split.
		+ apply Bool.negb_true_iff. apply eqb_neq. 
		apply not_in_cons in H. destruct H; easy.
		+ apply IHl.
		apply not_in_cons in H. destruct H; easy.
Qed.

Lemma eq_not_mem_rel : forall a l, NOT_MEM_rel conN a l  <-> ~ In a l.
Proof.
	intros.
	split; intro.
	- induction H; try easy.
		simpl. intro. destruct H1; contradiction.
	- induction l; try constructor.
		+ unfold In in H. apply Decidable.not_or in H. destruct H; easy.
		+ apply IHl. unfold In in H. 
		apply Decidable.not_or in H. 
		destruct H; easy.
Qed.

Lemma eq_distinct_list : forall l, ALL_DISTINCT conN (fun x0 y : conN => negb (x0 =? y)%string) l = true <-> NoDup l.
Proof.
	intros.
	split; intro.
	- induction l; constructor.
		* unfold ALL_DISTINCT in H. 
			apply eq_not_mem. apply Bool.andb_true_iff in H. destruct H; easy.
		* apply IHl. apply Bool.andb_true_iff in H. destruct H; easy.
	- unfold ALL_DISTINCT. induction l; try easy.
	apply Bool.andb_true_iff. split.
		+ inversion H. apply eq_not_mem in H2. easy.
		+apply IHl. inversion H; easy.
Qed.

Lemma eq_distinct_list_rel : forall l, ALL_DISTINCT_rel conN l <-> NoDup l.
Proof.
	intros.
	split; intro.
	- induction H; try constructor.
		+ apply eq_not_mem_rel; easy.
		+ easy.
	- induction H; try constructor.
		+ apply eq_not_mem_rel; easy.
		+ easy.
Qed.

Lemma RTC_trans: forall type rel x y z, RTC type rel x y -> RTC type rel y z -> RTC type rel x z.
Proof.
	intros.
	generalize y.
	induction H; try easy.
	intro. 
	apply transitivity with y; try easy.
	apply IHRTC; try easy.
Qed.

Lemma eval_concat :  forall env env' env'' es1 es2 vs1 vs2, small_eval_list env es1 env' (Rval_l vs1)->(small_eval_list env es2 env'' (Rval_l vs2)) -> small_eval_list env (es1++es2) env'' (Rval_l (vs1++vs2)).
Proof.
	intros env env' env'' es1.
	induction es1.
	- intros. inversion H; subst. simpl; easy.
	- intros. inversion H; subst.
		apply small_eval_cons with env'0; try easy.
		apply IHes1; try easy. 
Qed.

Lemma eval_eq_env : forall env env' es vs,small_eval_list env es env' (Rval_l vs) -> env = env'.
Proof.
	intros env env' es.
	induction es.
	- intros. inversion H. auto.
	- intros. inversion H; subst. revert H5. generalize vs0. auto.
Qed.

Lemma eval_rev : forall env env' es vs, small_eval_list env es env' (Rval_l vs) -> small_eval_list env (rev es) env (Rval_l (rev vs)).
Proof.
	intros env  env' es.
	induction es; intros.
	- inversion H; subst.  try easy.
	- inversion H; subst. simpl. apply eval_concat with env; try easy.
		+ apply IHes; try easy.
		+ apply small_eval_cons with env'0; try easy.
		constructor.
Qed.



Lemma e_step_indep_c_step :
forall env env' e e' c c' c'',
    e_step_rel (env, e, c) (env', e', c'') ->
    e_step_rel (env, e, c++c') (env', e', c''++c').
Proof.
	intros.
	inversion H; try constructor; try easy.
Qed.

Lemma e_step_indep_c : forall env env' e e' c l, RTC small_state e_step_rel (env,e,c) (env',e',l) -> forall c', RTC small_state e_step_rel (env,e,c++c') (env',e',l++c').
Proof.
	intros env env' e e' c l H.
	set (u := (env, e, c : list ctxt)).
	set (v := (env', e', l : list ctxt)).
	assert (u = (env, e, c : list ctxt)) by trivial.
	assert (v = (env', e', l : list ctxt)) by trivial.
	rewrite <- H0 in H.
	rewrite <- H1 in H.
	revert H1 H0.
	generalize env.
	generalize e.
	generalize c.
	induction H. 
	+ intros.  
		destruct x. destruct p. inversion H1. inversion H0. rewrite <- H4.
		rewrite <- H2. rewrite <- H3. rewrite <- H5. rewrite <- H6. rewrite H7.  
		apply reflexivity.
	+ intros. destruct y. apply transitivity with (p, l0++c').
		rewrite H2 in H. destruct p. apply e_step_indep_c_step; try easy. 
		destruct p.
		apply IHRTC; try easy.
Qed.


Lemma eval_cons : forall env env'' e1 es e2 v1 vs v2 cn env' vs0, 
	small_eval_list env (e1::es++[e2]) env'' (Rval_l (v1::vs++[v2])) -> 
	do_con_check (c val env) cn (Datatypes.length ( es ++ [e1]) + 1 + (List.length vs0)) = true ->
	RTC small_state e_step_rel (env, Exp e1, []) (env', Val v1, []) ->
	RTC small_state e_step_rel (env, Exp e2,  [(Ccon cn vs0 tt (es++[e1]),env)]) (env', Val v1,[(Ccon cn (rev vs ++ [v2]++vs0) tt [],env)]).
Proof. 
	intros env env'' e1 es.
	induction es.
	- intros.
		inversion H; subst.
		assert (H7 := H8).
		apply eval_eq_env in H8.
		rewrite H8 in H7.
		apply eval_rev in H7.
		simpl in H7.
		rewrite rev_unit in H7.
		inversion H7; subst.
		inversion H11; subst.
		simpl.
		apply RTC_trans with (env'1, Val v2, [(Ccon cn vs0 tt [e1], env'')]).
		+ apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Ccon cn vs0 tt [e1], env'')]); easy.
		+ apply transitivity with (env'', Exp e1, [(Ccon cn (v2 :: vs0) tt [], env'')]).
			* constructor. 
				simpl in H0.
				simpl.
				assert (Datatypes.length vs0 + 1 + 1 + 0 = S (S (Datatypes.length vs0))) by lia.
				rewrite H4; easy.
			* apply RTC_trans with (env', Val v1, [(Ccon cn (v2 :: vs0) tt [], env'')]); try constructor.
				apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Ccon cn (v2 :: vs0) tt [], env'')]). easy.
	- intros.
		assert (H' := H).
		apply eval_eq_env in H'. rewrite <- H' in H.
		apply eval_rev in H.
		simpl in H.
		do 2 rewrite rev_unit in H.
		simpl in H.
		inversion H; subst.
		apply RTC_trans with (env'0, Val v2,[(Ccon cn vs0 tt ((a :: es) ++ [e1]), env'')]).
		+ apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Ccon cn vs0 tt ((a :: es) ++ [e1]), env'')]); easy.
		+ simpl.
			apply transitivity with (env'', Exp a,[(Ccon cn (v2::vs0) tt (es ++ [e1]), env'')]).
			* constructor. simpl in H0.
				assert (S (Datatypes.length (es ++ [e1]) + 1 + Datatypes.length vs0) = Datatypes.length vs0 + 1 + 1 + Datatypes.length (es ++ [e1])) by lia.
				rewrite <- H2; easy.
			* destruct vs.
				-- apply eval_rev in H8.
					do 3 rewrite rev_app_distr in H8.
					simpl in H8.
					inversion H8; subst.
					inversion H10.
				-- simpl. rewrite <- app_assoc. apply IHes with (vs0:=v2::vs0); try easy.
					++ apply small_eval_cons with env'; try easy.
						apply eval_rev in H8.
						simpl in H8.
						rewrite rev_app_distr in H8.
						rewrite rev_app_distr with (val) (rev vs ++[v]) [v1] in H8.
						inversion H8; subst.
						do 2 rewrite rev_app_distr in H10.
						rewrite <-  rev_involutive with exp (es++[a]).
						rewrite <-  rev_involutive with val (vs++[v]).
						apply eval_rev with env''.
						simpl in H10.
						inversion H10; subst.
						do 2 rewrite rev_app_distr.
						simpl.
						apply eval_rev in H12.
						do 2 rewrite rev_involutive in H12.
						apply small_eval_cons with env'2; try easy.
	
					++ simpl. simpl in H0. 
						assert (Datatypes.length (es ++ [e1]) + 1 + S (Datatypes.length vs0) = S (Datatypes.length (es ++ [e1]) + 1 + Datatypes.length vs0)) by lia.
						rewrite H2; easy.
Qed.
	

Lemma eval_list_length : forall env env' es vs, small_eval_list env es env' (Rval_l vs) -> List.length es = List.length vs.
Proof.
	intros env env' es.
	induction es; intros.
	+ inversion H;subst. easy.
	+ inversion H; subst.
		simpl.
		apply eq_S.
		apply IHes. 
		auto.
Qed.

Lemma do_opapp_2_elt : forall l env e, do_opapp l = Some (env,e) -> List.length l = 2.
Proof.
	intros.
	-destruct l; try easy.
		destruct l; try easy.
		+ inversion H. destruct v; try easy.
		+ destruct l; try easy.
		inversion H. destruct v; try easy.
Qed.

