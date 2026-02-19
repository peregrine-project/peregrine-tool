From Stdlib Require Import Lia List Peano Nat.
From Stdlib Require Import Strings.String.
From CakeML Require Import ast.
From CakeML Require Import namespace.
From CakeML Require Import semanticPrimitives.
From CakeML Require Import functions.
From CakeML Require Import bigstep.
From CakeML Require Import smallstep.
From CakeML Require Import smallstep_rel.
From CakeML Require Import helper_lemmas.
From CakeML Require Import invariants.
Import ListNotations.


Theorem eq_small_step : forall s1 s2,e_step_rel s1 s2 <-> e_step s1 = Estep s2.
Proof.
	intros. split; intro.
	- inversion H; simpl; try unfold push; try auto.
		+ rewrite H0. unfold return_def. reflexivity.
		+ rewrite rev_app_distr. simpl. rewrite rev_involutive. auto.
		+ rewrite H0, H1. unfold return_def. auto.
		+ unfold do_con_check in H0. unfold do_con_check.
			assert (rev [e] = [e]) by easy.
			rewrite <- H3. rewrite <- rev_app_distr. rewrite rev_involutive. simpl.  
			destruct n eqn:?; try easy.
			destruct ( nsLookup (nat * stamp) (c val env) i) eqn:?;try easy.
			destruct p eqn:?. simpl in H0. rewrite H0. easy.
		+  apply eq_distinct_list in H0. rewrite H0; easy.
		+  unfold application. rewrite H0. destruct o. simpl. auto.
		+ inversion H0. 
			* unfold ALL_DISTINCT. rewrite H1. easy.
			*  apply eq_distinct_list in H0. rewrite <- H4 in H0. rewrite H0.
				rewrite H1; easy.
		+  apply eq_distinct_list in H0. rewrite H0,H1. easy.
		+ rewrite H0; easy. 
		+ rewrite H0,H1. unfold return_def. easy.
		+ rewrite H0. easy.
		+ destruct c0 eqn:?.
			unfold not_handle in H0.
			destruct c eqn:?; try easy.
			destruct u; easy.
	-  destruct s1. destruct s2. inversion H. destruct p. induction e.
		+ destruct e.
			* inversion H1; constructor.
			* unfold push in H1. inversion H1; subst.
				constructor.
			* unfold push in H1. inversion H1; subst.
				constructor.
			* destruct (do_con_check (c val s) n (Datatypes.length es)) eqn:?; try easy.
				destruct (rev es) eqn:?.
				-- destruct (build_conv (c val s) n []) eqn:?; try easy.
					unfold return_def in H1. inversion H1. 
					apply rev_symm in Heql1; simpl in Heql1.
					rewrite Heql1 in *.
					apply e_step_Con_nil; try easy.
				-- apply rev_symm in Heql1; rewrite Heql1 in *.
					unfold push in H1. inversion H1.
					apply e_step_Con_cons; try easy.
			* destruct (nsLookup  val (v val s) n) eqn:?.
				-- inversion H1. rewrite <- H3. apply (e_step_var s l n v). exact Heqo.
				-- inversion H1.
			* destruct (rev es) eqn:?.
				-- simpl in H1. unfold application in H1. destruct op. simpl in H1. inversion H1.
				-- unfold push in H1. inversion H1. assert (es = rev (e::l1)). apply rev_inj. rewrite Heql1. rewrite rev_involutive. auto. rewrite H0. apply e_step_App.
			* unfold return_def in H1. inversion H1. apply e_step_Fun.
			* unfold push in H1. inversion H1. constructor.
			* unfold push in H1; inversion H1. constructor.
			* destruct (ALL_DISTINCT conN (fun x y : conN => negb (x =? y)%string) (map (fun '(x, _, _) => x) f)) eqn:?; try easy.
				inversion H1; subst.
				apply e_step_Letrec.
				apply eq_distinct_list; easy.
		+ unfold continue in H1. destruct l. 
			* inversion H.
			*  do 2 destruct c eqn:?. inversion Heqc0. destruct c0 eqn:?. destruct u. destruct e eqn:?.
				-- unfold application in H1. destruct o. destruct (getOpClass Opapp). destruct (do_opapp (v::v0)) eqn:?. 
					++ destruct p. inversion H1. apply e_step_val1. exact Heqo.
					++ inversion H1.
				--  unfold push in H1. inversion H1. apply e_step_val2.
				--  destruct u. 
					inversion H1; subst.
					constructor.
				-- destruct u. 
					destruct (can_pmatch_all (namespace.c val s0) (map fst ps) v) eqn:?; try easy.
					inversion H1; subst.
					apply e_step_Cmat_check; easy. 
				-- destruct u,ps eqn:?; try easy.
					++ inversion H1; subst. constructor.
					++ destruct p eqn:?.
						destruct (ALL_DISTINCT conN (fun x y : conN => negb (x =? y)%string) (pat_bindings p1 [])) eqn:?.
						destruct (pmatch (namespace.c val s0) p1 v []) eqn:?; subst; try easy.
						** inversion H1. 
							apply e_step_Cmat_NM; try easy.
							apply eq_distinct_list. easy. 
						** inversion H1; subst. 
							apply e_step_Cmat_M; try easy.
							apply eq_distinct_list; easy.
						** easy.
				-- destruct u,es eqn:?.
					++  destruct (do_con_check (namespace.c val s0) n (Datatypes.length vs + 1)) eqn:?; try easy.
						destruct (build_conv (namespace.c val s0) n (v :: vs)) eqn:?; try easy.
						unfold return_def in H1. inversion H1; subst.
						apply e_step_Ccon_nil; try easy.
					++ destruct (do_con_check (namespace.c val s0) n (Datatypes.length vs + 1+ 1 + Datatypes.length
					l1)) eqn:?; try easy.
						unfold push in H1. inversion H1; subst.
						apply e_step_Ccon_cons; try easy.
				-- destruct u. inversion H1; subst. constructor.
				-- destruct u. inversion H1; subst. constructor.
		+ destruct l; try easy.
			destruct c.
			destruct c eqn:?; try  (inversion H; constructor; unfold not_handle; easy).
			destruct u. inversion H1. constructor.
Qed.


Theorem big_to_small : forall env,(forall e bv, evaluate env e  bv -> exists env',RTC small_state e_step_rel (env,Exp e,[]) (env',to_small_result bv,[]))/\
						(forall es vs ,  evaluate_list env es vs -> exists env', small_eval_list env es env' vs)/\
						(forall v pes err_v bv  , evaluate_match env v pes err_v bv -> (exists env', small_eval_match env v pes env' err_v bv)).
Proof.
	intro env.
	apply evaluate_mutual_ind 
    with (P := fun env e bv H =>  exists env', RTC small_state e_step_rel (env, Exp e, []) (env', to_small_result bv , []))
        (P0 := fun env es vs H => exists env', small_eval_list env es env' vs)
		(P1 := fun env v pes err_v bv H => exists env', small_eval_match env v pes env' err_v bv).
	- intros env0 e v eval_e RTC_e.
		destruct RTC_e as [env' RTC_e].
		exists env0.
		apply transitivity with (env0, Exp e, [(Craise tt,env0)]); try constructor.
		apply RTC_trans with (env', to_small_result (Rval v), [(Craise tt,env0)]).
		+ apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Craise tt,env0)]); easy.
		+ apply transitivity with (env0, to_small_result (Rerr (Rraise v)), []); try constructor.
	- intros env0 e err eval_e RTC_e.
		destruct RTC_e as [env' RTC_e].
		exists env'.
		apply transitivity with (env0, Exp e, [(Craise tt, env0)]); try constructor.
		destruct err. simpl in *.
		apply RTC_trans with (env', Exn v,[(Craise tt, env0)]).
		+ apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Craise tt, env0)]); easy.
		+ apply transitivity with (env', Exn v, []); try constructor.
			simpl; easy.
	- intros env0 l.
		exists env0.
		simpl.
		apply transitivity with (env0, Val (Litv l), []); constructor.
	- intros env0 e v pes eval_e RTC_e.
		destruct RTC_e as [env' RTC_e].
		exists env0.
		apply transitivity with (env0, Exp e, [(Chandle tt pes, env0)]); try constructor.
		apply RTC_trans with (env', to_small_result (Rval v), [(Chandle tt pes, env0)]).
		+ apply e_step_indep_c with (c:=[])(l:=[])(c':= [(Chandle tt pes, env0)]); easy.
		+ apply transitivity with (env0, to_small_result (Rval v), []); try constructor.

	- intros env0 e pes v bv eval_e RTC_e eval_match_pes RTC_match_pes can_pmatch_pes.
		destruct RTC_match_pes as [env' RTC_match_pes].
		destruct RTC_e as [env'0 RTC_e].
		exists env'.
		apply transitivity with (env0, Exp e,[(Chandle tt pes, env0)]); try constructor.
		simpl in RTC_e.
		apply RTC_trans with (env'0, Exn v, [(Chandle tt pes, env0)]).
		+ apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Chandle tt pes, env0)]); easy.
		+ apply transitivity with (env'0, Val v,[(Cmat_check tt pes v, env0)] ); try constructor.
			
			apply transitivity with (env0, Val v, [(Cmat tt pes v, env0)]); try (constructor; easy).
			remember bv.
			set (v0 := v).
			assert (v0 = v) by easy.
			set (v1 := v).
			assert (v1 = v) by easy.
			rewrite <- H in RTC_match_pes at 1.
			rewrite <- H0 in RTC_match_pes at 1.
			revert H H0.
			induction RTC_match_pes.
			* intros. rewrite H1. apply transitivity with ({| v := nsAppend (alist_to_ns env') (namespace.v val env0); c := c val env0 |}, Exp e0, []); try easy.
				constructor; try easy.
				-- apply eq_distinct_list_rel; easy. 
			* intros. apply transitivity with (env0, Val va, [(Cmat tt pes va, env0)]); try constructor.
				-- apply eq_distinct_list_rel; easy.
				-- easy.
				-- apply IHRTC_match_pes; try easy.
					++ inversion eval_match_pes; try easy; subst.
						rewrite H10 in H0; inversion H0.
					++ unfold map in can_pmatch_pes.
					unfold can_pmatch_all in can_pmatch_pes.
					simpl in can_pmatch_pes.
					rewrite H1 in *.
					rewrite H0 in can_pmatch_pes.
					simpl in can_pmatch_pes.
					easy.
			* intros; subst. apply transitivity with (env0, Exn v,[]); try constructor.
	- intros env0 n v1 Look.
		exists env0. apply transitivity with (env0, Val v1, []).
		+ constructor; exact Look.
		+ apply reflexivity.
	
	- intros.
		exists env0. 
		apply transitivity with  (env0, Val (Closure env0 n e), []).
		+ apply e_step_Fun.
		+ apply reflexivity.
	
	- intros env0 op es bv vs env' e eval_rev_es small_eval_rev_es do_opapp_vs eval_e RTC_e op_class.
		destruct RTC_e as [env'0 RTC_e]; exists env'0.
		assert (do_opapp_vs' := do_opapp_vs).
		unfold do_opapp in do_opapp_vs.
		destruct (rev vs) eqn:?; try easy.
		destruct l; try easy.
		+ destruct v; easy.
		+ destruct l; try (destruct v; easy).
			apply rev_symm in Heql.
			simpl in Heql.
			rewrite Heql in *.
			destruct small_eval_rev_es as [env'1 small_eval_rev_es].
			apply eval_rev in small_eval_rev_es.
			simpl in small_eval_rev_es. rewrite rev_involutive in small_eval_rev_es.
			inversion small_eval_rev_es; subst. inversion H4; subst. inversion H6; subst.
			apply transitivity with (env0,Exp e1,[(Capp op [] tt [e0],env0)]).
			-- assert ( [e0;e1] = rev [e1;e0]) as rev_es; try easy.
				rewrite rev_es.
				apply e_step_App.
			-- apply RTC_trans with (env'3, Val v0, [(Capp op [] tt [e0],env0)]).
				++ apply e_step_indep_c with (c':=  [(Capp op [] tt [e0],env0)])( c:=[] )(l:=[]). easy.
				++ apply transitivity with (env0,Exp e0,[(Capp op [v0] tt [],env0)]). 
					apply e_step_val2.
					apply RTC_trans with (env'2 ,Val v,[(Capp op [v0] tt [],env0)]).
					** apply e_step_indep_c with (c':= [(Capp op [v0] tt [],env0)])( c:=[] )(l:=[]). easy.
					** apply transitivity with (env', Exp e ,[]).
						+++ apply e_step_val1. easy.
						+++ easy.
	- intros env0 op es0 err eval_es small_eval_es0.
		destruct small_eval_es0 as [env' small_eval].
		exists env'.
		clear eval_es.
		destruct (rev es0) as [|e es]eqn:?; try easy.
		apply rev_symm in Heql; rewrite Heql.
		apply transitivity with (env0,Exp e,[(Capp op [] tt es,env0)]); try constructor.
		inversion small_eval; subst.
		+ apply RTC_trans with  (env', Exn err0,[(Capp op [] tt es, env0)]).
			* apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Capp op [] tt es, env0)]); easy.
			* apply transitivity with (env', Exn err0, []); try constructor.
				simpl; easy.
		+ clear small_eval.
			destruct err.
			remember (Rerr_l (Rraise v0)).
			set (vs:=[]).
			revert H3.
			generalize vs e env'0 v.
			induction H4; try easy.
			* intros vs0 e1 env'1 v1 eval_e1.
				apply RTC_trans  with (env'1, Val v1,  [(Capp op vs0 tt (e0 :: es), env0)]).
				-- apply e_step_indep_c with (c:=[])(l:=[])(c':= [(Capp op vs0 tt (e0 :: es), env0)]); easy.
				-- apply transitivity with (env0, Exp e0, [(Capp op (v1::vs0) tt  es, env0)]); try constructor.
					apply RTC_trans with  (env', Exn err, [(Capp op (v1 :: vs0) tt es, env0)]).
					++ apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Capp op (v1 :: vs0) tt es, env0)]); easy.
					++ inversion Heql; subst.
						apply transitivity with (env', Exn v0, []); try constructor.
						simpl; easy.
			* intros vs0 e1 env'1 v2 eval_e1.
				apply RTC_trans  with (env'1, Val v2,  [(Capp op vs0 tt (e0 :: es), env0)]).
				-- apply e_step_indep_c with (c:=[])(l:=[])(c':= [(Capp op vs0 tt (e0 :: es), env0)]); easy.
				-- apply transitivity with (env0, Exp e0, [(Capp op (v2::vs0) tt  es, env0)]); try constructor.
					apply IHsmall_eval_list with env' v1; try easy.

	- intros env0 n e1 e2 va bv eval_e1 RTC_eval_e1 eval_e2 RTC_eval_e2.
		destruct RTC_eval_e2 as [env' RTC_eval_e2].
		destruct RTC_eval_e1 as [env'0 RTC_eval_e1].
		exists env'.
		apply transitivity with (env0, Exp e1,[(Clet n tt e2,env0)]); try constructor.
		apply RTC_trans with (env'0, Val va, [(Clet n tt e2,env0)]).
		+ apply e_step_indep_c with (c':=[(Clet n tt e2, env0)]) (c:=[]) (l:= []); easy.
		+ apply transitivity with ({| v := nsOptBind n va (v val env0); c := c val env0 |}, Exp e2,[]).
			* constructor.
			* easy.
	- intros env0 n e1 e2 err eval_e1 RTC_e1.
		destruct err.
		destruct RTC_e1 as [env' RTC_e1].
		exists env'.
		simpl; simpl in RTC_e1.
		apply transitivity with (env0, Exp e1, [(Clet n tt e2,env0)]); try constructor.
		apply RTC_trans with (env', Exn v,[(Clet n tt e2,env0)]).
		+ apply e_step_indep_c with (c:=[]) (l:=[]) (c':=[(Clet n tt e2,env0)]); easy.
		+ apply transitivity with (env', Exn v, []); try constructor.
			easy.
	- intros.
		destruct (rev es) eqn:?.
		+ apply rev_symm in Heql. simpl in Heql. rewrite Heql in *.
			simpl in e.
			inversion e1; subst.
			exists env0.
			apply transitivity with (env0,Val v,[]); try constructor;try easy.
		+ apply rev_symm in Heql. rewrite Heql in *.
			destruct (rev vs) eqn:?.
			* apply rev_symm in Heql0. simpl in Heql0. rewrite Heql0 in *.
				inversion e1.
			* destruct H as [env' H].
			inversion H; subst.
			inversion e1; subst.
			exists env0.
			destruct (rev l) eqn:?.
			--  apply rev_symm in Heql1. simpl in Heql1. rewrite Heql1 in *.
				apply transitivity with (env0,Exp e2,[(Ccon cn [] tt [],env0)]); try constructor; try easy.
				apply RTC_trans with (env'0, Val v1, [(Ccon cn [] tt [], env0)]).
				++ apply e_step_indep_c with (c':=[(Ccon cn [] tt [], env0)])(c:=[])(l:=[]); easy.
				++ apply transitivity with (env0, Val v, []); try constructor.
					** simpl. simpl in e. easy.
					** inversion H7; subst. inversion Heql0; subst. auto.
			-- apply rev_symm in Heql1. simpl in Heql1. 
				rewrite  Heql1 in *.
				assert (small_eval_list env0 (rev (rev l1 ++ [e3])) env' (Rval_l (rev vs0))).
				++ assert (eq_env := H5); apply eval_eq_env in eq_env.
				rewrite eq_env in *.
				apply eval_rev with env'; easy.
				++ simpl in H0.
					rewrite rev_concat_1_elt in H0. rewrite rev_involutive in H0.
					inversion H0; subst.
					apply RTC_trans with (env'1,Val v2,[(Ccon cn (vs++[v1]) tt [],env0)]).
					**   assert (vs = rev (rev vs)). rewrite rev_involutive; auto.
						rewrite H1.
						apply transitivity with (env0, Exp e2, [(Ccon cn [] tt (rev l1 ++ [e3]),env0)]); try (constructor; easy).
						apply eval_cons with env'; try easy.
						--- apply small_eval_cons with env'1; try easy.
							apply eval_concat with env'.
							+++ assert  (eq_env := H10); apply eval_eq_env in H10.
								rewrite H10 in *. apply eval_rev with env'; easy.
							+++ apply small_eval_cons with env'0; try easy.
								apply eval_eq_env in H10; rewrite H10. apply small_eval_nil.
						--- rewrite length_rev in e. simpl. simpl in e. assert ((Datatypes.length (rev l1 ++ [e3]) + 1 + 0) = (S (Datatypes.length (rev l1 ++ [e3])))) as eq_nat by lia.
							rewrite eq_nat; easy.
					** apply rev_symm in H6. subst.
						apply rev_3 in Heql0.
						destruct Heql0.
						subst.
						apply transitivity with (env0, Val v, []); try constructor.
						--- rewrite length_rev in e. simpl in e. 
							rewrite rev_concat_1_elt in e. rewrite length_rev in e.
							assert (List.length (e3::l1) =List.length (v2::vs)).
							+++ apply eval_list_length with env0 env'.
							rewrite rev_involutive in H0.
							easy.
							+++ simpl in H1. simpl in e.
								rewrite <- length_rev.
								rewrite rev_app_distr.
								simpl.
								rewrite length_rev.
								rewrite  H1 in e.
								rewrite PeanoNat.Nat.add_1_r.
								easy.
						--- easy.
	- intros env0 cn es err con_check eval_rev_es small_eval_rev_es. 
		destruct small_eval_rev_es as [env' small_eval_rev_es].
		exists env'.
		clear eval_rev_es.
		destruct (rev es) as [|e es0] eqn:?; try easy.
		apply rev_symm in Heql; rewrite Heql.
		apply transitivity with (env0, Exp e, [(Ccon cn [] tt es0,env0) ]); try constructor.
		+ rewrite <- Heql; easy.
		+ inversion small_eval_rev_es; subst.
			* apply RTC_trans with (env', Exn err0,[(Ccon cn [] tt es0,env0) ]).
				-- apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Ccon cn [] tt es0,env0) ]); easy.
				-- simpl. apply transitivity with (env', Exn err0, []); try constructor.
				simpl; easy.
			* clear small_eval_rev_es.
				destruct err.
				remember (Rerr_l (Rraise v0)).
				rewrite <- PeanoNat.Nat.add_0_r with (n :=(Datatypes.length (rev (e :: es0)))) in con_check.
				rewrite <- length_nil  with val in con_check.
				set (vs:=[]).
				assert (vs=([]:list val)) by auto.
				rewrite <- H in con_check.
				
				revert H3 con_check.
				
				
				generalize vs e env'0 v.
				induction H4; try easy.
				-- intros vs0 e1 env'1 v1 eval_e1 do_con.
					apply RTC_trans  with (env'1, Val v1,  [(Ccon cn vs0 tt (e0 :: es), env0)]).
					++ apply e_step_indep_c with (c:=[])(l:=[])(c':= [(Ccon cn vs0 tt (e0 :: es), env0)]); easy.
					++ apply transitivity with (env0, Exp e0, [(Ccon cn (v1::vs0) tt  es, env0)]); try constructor.
						** rewrite <- do_con. f_equal. rewrite length_rev. simpl; lia.
						** apply RTC_trans with  (env', Exn err, [(Ccon cn (v1 :: vs0) tt es, env0)]).
							--- apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Ccon cn (v1 :: vs0) tt es, env0)]); easy.
							--- inversion Heql; subst.
								apply transitivity with (env', Exn v0, []); try constructor.
								simpl; easy.
				-- intros vs0 e1 env'1 v2 eval_e1 do_con.
					apply RTC_trans  with (env'1, Val v2,  [(Ccon cn vs0 tt (e0 :: es), env0)]).
					++ apply e_step_indep_c with (c:=[])(l:=[])(c':= [(Ccon cn vs0 tt (e0 :: es), env0)]); easy.
					++ apply transitivity with (env0, Exp e0, [(Ccon cn (v2::vs0) tt  es, env0)]); try constructor.
						** rewrite <- do_con. f_equal. rewrite length_rev. simpl; lia.
						** apply IHsmall_eval_list with env' v1; try easy. rewrite <- do_con. 
						f_equal. do 2 rewrite length_rev. simpl. lia.
	- intros env0 e pes v bv eval_e RTC_e eval_pes small_eval_pes can_pmatch_pes.
		destruct RTC_e as [env'0 RTC_e].
		destruct small_eval_pes as [env' small_eval_pes].
		exists env'.
		apply transitivity with (env0, Exp e,[(Cmat_check tt pes bind_exn_v,env0)]); try constructor.
		apply RTC_trans with (env'0, Val v,[(Cmat_check tt pes bind_exn_v,env0)]).
		+ apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Cmat_check tt pes bind_exn_v, env0)]); easy.
		+ apply transitivity with (env0, Val v,[(Cmat tt pes bind_exn_v, env0)]); try (constructor; easy).
			remember v.
			induction small_eval_pes; intros; subst.
			* apply transitivity with ({| v := nsAppend (alist_to_ns env') (namespace.v val env0); c := c val env0 |}, Exp e0, []); try easy.
				constructor; try easy.
				apply eq_distinct_list_rel; easy.
			* apply transitivity with (env0, Val v, [(Cmat tt pes err_v, env0)]); try constructor.
				-- apply eq_distinct_list_rel; easy.
				-- easy.
				-- apply IHsmall_eval_pes; try easy.
					++ inversion eval_pes; try easy; subst.
						rewrite H8 in H0; inversion H0.
					++ unfold map in can_pmatch_pes.
				unfold can_pmatch_all in can_pmatch_pes.
				simpl in can_pmatch_pes.
				rewrite H0 in can_pmatch_pes.
				simpl in can_pmatch_pes.
				easy.
			* simpl.
				apply transitivity with (env0, Exn err_v,[]); try constructor.

	- intros env0 e pes err eval_e RTC_e.
		destruct RTC_e as [env' RTC_e].
		exists env'.
		apply transitivity with (env0, Exp e,[(Cmat_check tt pes bind_exn_v,env0)]); try constructor.
		apply RTC_trans with (env', to_small_result (Rerr err),[(Cmat_check tt pes bind_exn_v, env0)]).
		+ apply e_step_indep_c with (c:=[])(l:=[])(c':=[(Cmat_check tt pes bind_exn_v, env0)]); easy.
		+ destruct err; simpl. 
		apply transitivity with (env', Exn v, []); try constructor.
		simpl; easy.

	- intros env0 funs e bv ALL_DIST eval_e RTC_e.
	destruct RTC_e as [env' RTC_e].
		exists env'.
		apply transitivity with ({| v := build_rec_env funs env0 (v val env0); c := c val env0 |}, Exp e, []); try easy.
		apply e_step_Letrec.
		apply eq_distinct_list_rel; easy.
	- intro env0.
		exists env0. apply small_eval_nil.
	- intros env0 e es v vs eval_e RTC_e eval_es small_eval_vs.
		destruct RTC_e as [env' RTC_e].
		exists env0.
		apply small_eval_cons with env'; try easy.
		destruct small_eval_vs.
		assert (H':=H).
		apply eval_eq_env in H.
		rewrite <- H in H'. 
		auto.
	-intros env0 e es err eval_e RTC_e.
		destruct RTC_e as [env' RTC_E].
		exists env'.
		destruct err.
		apply small_eval_err; easy.
	- intros env0 e es v err eval_e RTC_e eval_es small_eval_es.
		destruct RTC_e as [env'0 RTC_E].
		destruct small_eval_es as [env' small_eval_es].
		destruct err.
		exists env'.
		apply small_eval_cons_err with env'0 v; try easy.
	- intros env0 e p pes va bv env' err_v all_dist pmatch_p_va eval_e RTC_e. 
	destruct RTC_e as [env'0 RTC_e].
		exists env'0.
	apply small_eval_match_M with (to_small_result bv) (env') ; try easy. 
	- intros. destruct H.
		exists x. 
		apply small_eval_match_NM; try easy.
	- intros env0 va err_v.
		exists env0.
		constructor.
Qed.


Lemma one_step_backward : 
	forall env e c env' e' c' bv, e_step_rel (env,e,c) (env',e',c') ->
	evaluate_state (env',e',c') bv ->
	evaluate_state (env,e,c) bv.
Proof.
	intros.
	induction H.
	- apply evaluate_state_exp with (Rval v1).
		* apply evaluate_Var. easy.
		* inversion H0. easy.
	- inversion H0; subst. apply evaluate_state_exp with (Rval (Litv l)); try easy.
		constructor.
	- apply evaluate_state_exp with (Rval (Closure env0 n e0)).
		* apply evaluate_Fun.
		* inversion H0. easy.
	- inversion H0; subst.
		inversion H5; subst.
		+ apply evaluate_state_exp with res0; try easy.
			inversion H7; subst.
			* constructor; try easy.
				rewrite rev_involutive.
				apply evaluate_cons_err2 with v; try easy.
			* apply evaluate_App with (v::vs) env'0 e1; try easy.
				-- rewrite rev_involutive. constructor; easy.
				-- destruct o; easy.
		+ apply evaluate_state_exp with (Rerr err); try easy.
			constructor.
			rewrite rev_involutive.
			constructor; easy.
	- inversion H0; subst.
		inversion H5; subst.
		+ inversion H7; subst.
			apply evaluate_state_exp with res0; try easy.
			inversion H8; subst; apply evaluate_Let with v; try easy.
		+ apply evaluate_state_exp with (Rerr err); try easy.
			constructor; easy.
	-  apply evaluate_state_exp with (Rval va).
		+ apply evaluate_Con with []; try easy. simpl. constructor.
		+ inversion H0. easy.

	-  inversion H0; subst. 
		inversion H6; subst.
		inversion H8; subst.
		+ apply evaluate_state_exp with (Rval v'); try easy.
			apply evaluate_Con with (v::vs'); try easy.
			rewrite rev_involutive.
			constructor; try easy.
		+ apply evaluate_state_exp with (Rerr err); try easy.
			constructor.
			* rewrite <- H10. f_equal. apply length_rev.
			* rewrite rev_involutive.
				apply evaluate_cons_err2 with v; easy.
		+ apply evaluate_state_exp with (Rerr err); try easy.
			constructor.
			* rewrite <- H; easy.
			* rewrite rev_involutive. constructor; easy.
	- inversion H0; subst.
		inversion H5; subst.
		+inversion H7; subst.
			apply evaluate_state_exp with res0; try easy.
			apply evaluate_Mat with v; try easy.
		+ apply evaluate_state_exp with (Rerr err); try easy.
			constructor; easy.
	-  inversion H0; subst.
		apply evaluate_state_exp with res; try easy.
		apply evaluate_Letrec; try easy.
		apply eq_distinct_list_rel; easy.
	- inversion H0; subst.
		inversion H5; subst.
		+apply evaluate_state_exp with res0; try easy.
			inversion H7; subst.
			apply evaluate_raise; easy.
		+ apply evaluate_state_exp with (Rerr err); try easy.
			constructor; easy.
	- inversion H0; subst.
		inversion H5; subst.
		+ apply evaluate_state_exp with res0; try easy.
			inversion H7; subst.
			constructor; easy.
		+ apply evaluate_state_exp with res1; try easy.
			apply evaluate_handle_err with v; try easy.
		+ simpl in H7. easy.
	- apply evaluate_state_val.
		inversion H0.
		apply evaluate_ctxts_cons with res; try easy.
		apply evaluate_ctxt_App with (env'') ([]) e0;try constructor;try easy.
		destruct o. easy.
	- apply evaluate_state_val.
		inversion H0. inversion H5. subst.
		apply evaluate_ctxts_cons with res0; try easy.
		inversion H11; subst.
		+ constructor. apply evaluate_cons_err2 with v0;easy.
		+ apply evaluate_ctxt_App with env'1 (v0::vs0) e1; try easy.
			* constructor; easy.
			* simpl (rev (v0 :: vs0) ++ [v] ++ vs). rewrite <- app_assoc. easy.
			* destruct o; easy.
		+ subst. apply evaluate_ctxts_cons with (Rerr err); try easy.
			constructor.
			constructor; easy.
	- apply evaluate_state_val.
		inversion H0; subst.
		apply evaluate_ctxts_cons with res; try easy.
		apply evaluate_ctxt_Let; easy.

	- inversion H0; subst.
		inversion H6; subst.
		inversion H8; subst.
		apply evaluate_state_val.
		apply evaluate_ctxts_cons with res; try easy.
		apply evaluate_ctxt_Cmat.
		apply evaluate_match_NM; try easy.
		apply eq_distinct_list_rel; easy.

	-  inversion H0; subst.
		apply evaluate_state_val.
		apply evaluate_ctxts_cons with res; try easy.
		apply evaluate_ctxt_Cmat.
		apply evaluate_match_M with env''; try easy.
		apply eq_distinct_list_rel; easy.
	- constructor.
		inversion H0; subst.
		apply evaluate_ctxts_cons with (Rerr (Rraise err_v)); try easy.
		constructor.
		constructor.
	- inversion H0; subst.
		inversion H5; subst.
		inversion H7;subst.
		apply evaluate_state_val.
		apply evaluate_ctxts_cons with res; try easy.
		apply evaluate_ctxt_Cmat_check; try easy.
	
	- inversion H0; subst.
		apply evaluate_state_val.
		apply evaluate_ctxts_cons with (Rval v'); try easy.
		apply evaluate_ctxt_Ccon with []; try easy.
		+ simpl. rewrite PeanoNat.Nat.add_0_r; easy.
		+ constructor.
	- inversion H0; subst.
		inversion H6; subst.
		inversion H8; subst.
		+ apply evaluate_state_val.
			apply evaluate_ctxts_cons with (Rval v') ; try easy.
			apply evaluate_ctxt_Ccon with (v::vs'); try easy.
			* simpl. simpl in H4.
				rewrite PeanoNat.Nat.add_1_r.
				rewrite <- PeanoNat.Nat.add_assoc in H4.
				rewrite PeanoNat.Nat.add_1_l with (n:=  Datatypes.length es) in H4.
				easy.
			* simpl. rewrite <- app_assoc. easy.
			* constructor; easy. 
		+  constructor.
			inversion H6; subst.
			apply evaluate_ctxts_cons with (Rerr err); try easy.
			constructor.
			* rewrite <- H10. f_equal. simpl; lia.
			* apply evaluate_cons_err2 with v; try easy.
		+ constructor.
			apply evaluate_ctxts_cons with (Rerr err); try easy.
			constructor.
			* rewrite <- H. f_equal. simpl; lia.
			* constructor; easy.
	- inversion H0; subst.
		inversion H4; subst.
		+ apply evaluate_state_val.
			apply evaluate_ctxts_cons with (Rerr (Rraise va)); try easy. 
			constructor.
		+ constructor.
			apply evaluate_ctxts_cons with (Rerr (Rraise va)); try easy.
			constructor.
		+ constructor.
			apply evaluate_ctxts_cons with (Rerr (Rraise va)); try easy.
			constructor.
	- constructor. inversion H0; subst.
		inversion H4; subst.
		+ apply evaluate_ctxts_cons with (Rval va); try easy.
			constructor.
		+ apply evaluate_ctxts_cons with (Rval va); try easy.
		constructor.
	- constructor; try easy.
		inversion H0; subst.
		inversion H4; subst.
		inversion H6; subst.
		apply evaluate_ctxts_handle with res; try easy.
	- constructor.
		inversion H0; subst.
		apply evaluate_ctxts_not_handle; try easy.
Qed.


Theorem  small_exp_to_big_exp : 
	forall env e c env' e' c', RTC small_state e_step_rel (env,e,c) (env',e',c') -> 
	forall r, evaluate_state (env',e',c') r ->
	evaluate_state (env,e,c) r.
Proof.
	intros.
	induction H; try easy.
	destruct x. destruct p.
	destruct y. destruct p.
	apply one_step_backward with s0 e1 l0 ; try easy.
	apply IHRTC; try easy.
Qed.

Theorem small_big_exp_equiv: 
	forall env e br ,(exists env', RTC small_state e_step_rel (env, Exp e, []) (env', to_small_result br, [])) <->
	evaluate env e br.
Proof.
	intros.
	split; intro. 
	- destruct H. apply small_exp_to_big_exp with (r:=br) in H.
		+ inversion H. 
			inversion H5. 
			rewrite H8 in H4.
			easy.
		+ destruct br; simpl.
			* apply evaluate_state_val.
				apply evaluate_ctxts_nil.
			* destruct e0.
				constructor.
				constructor.
	- apply big_to_small in H.
		destruct H.
		exists x.
		easy.
Qed.