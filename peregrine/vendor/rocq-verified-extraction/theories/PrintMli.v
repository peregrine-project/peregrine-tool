From Stdlib Require Import Nat List Strings.Ascii.
From MetaRocq.Template Require Import Loader All Checker.
From MetaRocq.Utils Require Import bytestring.

Open Scope bool_scope.
Open Scope bs.

Definition newline : ascii := "010".
Definition nl : string := String.String (byte_of_ascii newline) String.EmptyString.

Definition uncapitalize_char (c : Byte.byte) : Byte.byte :=
  let n := Byte.to_nat c in
  if (65 <=? n)%nat && (n <=? 90)%nat then match Byte.of_nat (n + 32) with Some c => c | _ => c end
  else c.

Definition uncapitalize (s : bytestring.string) : bytestring.string :=
  match s with 
  | bytestring.String.EmptyString => bytestring.String.EmptyString
  | bytestring.String.String c s => bytestring.String.String (uncapitalize_char c) s
  end.

Definition capitalize_char (c : Byte.byte) : Byte.byte :=
  let n := Byte.to_nat c in
  if (97 <=? n)%nat && (n <=? 123)%nat then match Byte.of_nat (n - 32) with Some c => c | _ => c end
  else c.

Definition capitalize (s : bytestring.string) : bytestring.string :=
  match s with 
  | bytestring.String.EmptyString => bytestring.String.EmptyString
  | bytestring.String.String c s => bytestring.String.String (capitalize_char c) s
  end.

Definition term_eqb (t1 t2 : term) :=
  @eq_term config.default_checker_flags init_graph t1 t2.

Notation "t === u" := (term_eqb t u) (at level 70).

Unset Guard Checking.
  
Section fix_global.
  
  Variable Σ : global_declarations.

  Definition print_parens_around sep l :=
    match l with
      [] => ""
    | [c] => c ++ " "
    | l => "(" ++ String.concat sep l ++ ") "
    end.

  Fixpoint print_type_def (printf : bool) (names : list ident) (t : term) {struct t} :=
    let def := "Obj.t (* not supported *)" in
    match t with
    | tConst kn univs =>
        if (tConst kn univs === <% PrimInt63.int %>) then
          "int"
        else
          if (tConst kn univs === <% PrimFloat.float %>) then
          "float"
        else
        match lookup_global Σ kn with
                    | Some (ConstantDecl d) => match d.(cst_body) with
                               | Some b => print_type_def true [] b
                               | _ => "<constant doesn't have a body>"
                               end
                    | Some _ => "<constant not a decl>"
                    | _ => "<constant not found>"
                    end
    | tInd {| inductive_mind := (_, i) |} _ => uncapitalize i
    | tProd {| binder_name := nNamed na |}  A B =>
        (if printf then "" else "(") ++
        print_type_def false names A ++ " -> " ++ print_type_def printf (("'" ++ uncapitalize na) :: names) B
            ++ if printf then "" else ") (* higher-order functions are not safe to extract *)" 
    | tProd _ A B =>
        (if printf then "" else "(") ++
          print_type_def false names A ++ " -> " ++ print_type_def printf ("Obj.t" :: names) B
            ++ if printf then "" else ") (* higher-order functions are not safe to extract *)" 
    | tApp f args =>
          if f === <% prod %> then
            match args with [A; B] => "(" ++ print_type_def printf names A ++ " * " ++ print_type_def printf names B ++ ")"
                       | _ => def
            end
          else
            print_parens_around ", " (map (print_type_def printf names) args) ++ " " ++ print_type_def printf names f
    | tSort _ =>
        "Obj.t"
    | tRel n =>
        nth n names " Obj.t"
    | _t => def
    end.

  Definition typevariable_from_aname (a : aname) :=
    match a.(binder_name) with
    | nNamed i => "'" ++ uncapitalize i
    | _ => "<IMPOSSIBLE>"
    end.

  Definition print_type := print_type_def true [].

  Fixpoint print_types names (ctx : context) :=
    match ctx with
    | [] => ""
    | [{| decl_type := T |}] => print_type_def true names T
    | {| decl_type := T ; decl_name := na |} :: l => print_type_def true names T ++ " * " ++ print_types ((typevariable_from_aname na) :: names) l
    end.

  Definition print_constructor na (names : list ident) (ctx : context) :=
    capitalize na ++
      match ctx with
      | [] => " "
      | l => " of " ++ print_types names l
      end.

  Fixpoint print_constructors pars (names : list ident) (l : list constructor_body) :=
    match l with
    | [] => ""
    | [c] => print_constructor c.(cstr_name) names (skipn pars (MRList.rev (fst (decompose_prod_assum [] c.(cstr_type)))))
    | c :: l => print_constructor c.(cstr_name) names (skipn pars (MRList.rev (fst (decompose_prod_assum [] c.(cstr_type))))) ++ " | " ++ print_constructors pars names l
    end.

  Fixpoint print_record nms (ctx : context) :=
    match ctx with
    | {| decl_name := {| binder_name := nNamed na |} ;
        decl_type := A
      |} :: ctx => (uncapitalize na) ++ " : " ++ print_type_def true nms A ++ " ; " ++ print_record (na :: nms) ctx
    | _ => ""
    end.

  Definition print_record_bodies pars (bds : list one_inductive_body) :=
    match bds with
    | b :: _ => match  b.(ind_ctors) with
                [c] => let all := (rev (fst (decompose_prod_assum [] c.(cstr_type)))) in
                  print_record (map
                                  (fun d => typevariable_from_aname (d.(decl_name)))
                                  (firstn pars all)) (skipn pars all)
              | _ => "<this is not a record>"
              end
    | _ => ""
    end.

  Fixpoint print_inductive_bodies pars (names : list ident) (bds : list one_inductive_body) :=
    match bds with
    | [] => ""
    | [b] => uncapitalize (b.(ind_name)) ++ " = " ++ print_constructors pars names b.(ind_ctors)
    | b :: bds => uncapitalize (b.(ind_name)) ++ " = " ++ print_constructors pars names b.(ind_ctors) ++ nl ++ "and " ++ print_inductive_bodies pars names bds
    end.

  Definition print_inductive na (m : mutual_inductive_body) :=
    match m.(ind_finite) with
    | Finite =>
        "type " ++
                print_parens_around ", " (MRList.rev_map (fun d => typevariable_from_aname (d.(decl_name))) m.(ind_params)) ++
                print_inductive_bodies m.(ind_npars) (map (fun d => typevariable_from_aname (d.(decl_name))) m.(ind_params) ++ MRList.rev_map (fun x=> uncapitalize (ind_name x)) m.(ind_bodies)) m.(ind_bodies)
    | BiFinite => "type " ++
                   print_parens_around ", " (MRList.rev_map (fun d => typevariable_from_aname (d.(decl_name))) m.(ind_params)) ++
                   (uncapitalize na) ++ " = " ++ "{ " ++ print_record_bodies m.(ind_npars) m.(ind_bodies) ++ " }"
    | CoFinite => "<co recursive type not supported>"
    end.

End fix_global.
Set Guard Checking.

Fixpoint print_globals (Σ : global_declarations) :=
  match Σ with
  | [] => ""
  | (na, InductiveDecl m) :: l =>
      (* These types have matching representations with OCaml in generated code *)
      if (na == (MPfile ["Datatypes"; "Init"; "Coq"], "unit"))
        || (na == (MPfile ["Datatypes"; "Init"; "Coq"], "bool"))
        || (na == (MPfile ["Datatypes"; "Init"; "Coq"], "list"))
        || (na == (MPfile ["Datatypes"; "Init"; "Coq"], "prod"))
        || (na == (MPfile ["Datatypes"; "Init"; "Coq"], "option"))
      then print_globals l
      else print_globals l
             ++ nl ++ print_inductive Σ na.2 m 
  | _ :: l => print_globals l
  end.

Fixpoint decompose_prod (t : Ast.term) : list Ast.term :=
  match t with
  | Ast.tApp (Ast.tInd _ _) [l ; r ] => r :: decompose_prod l
  | r => [r]
  end.

Definition print_mli names (p : program) :=
  print_globals (p.1.(declarations)) ++ nl ++ fold_right (fun '(na,t) str => "val " ++ (uncapitalize na) ++ " : " ++ print_type p.1.(declarations) t ++ nl ++ str) ""%bs (combine names (rev (decompose_prod p.2))).

Import MRMonadNotation.

Fixpoint extract_names (t : Ast.term) : list ident :=
  match t with
  | Ast.tConst kn _ => [kn.2]
  | Ast.tApp (Ast.tConstruct _ _ _) [_ ; _ ; l ; Ast.tConst kn _ ] => kn.2 :: extract_names l
  | _ => []
  end.

Definition PrintMLI {A} (a : A) :=
  A <- tmEval cbv A ;;
  p <- tmQuoteRec A ;;
  t <- tmQuote a ;;
  match rev (extract_names t) with
  | [] =>
      tmEval cbv (print_mli ["main"] p) >>= tmMsg
  | names =>
      tmEval cbv (print_mli names p) >>= tmMsg
  end.

Notation "'Print' 'mli' x" := (PrintMLI x) (at level 0).

(* Record testrec := *)
(*   { *)
(*     testproj1 : nat; *)
(*     testproj2 : bool *)
(*   }. *)

(* Inductive ltree := Tree (a : nat) (b1 : ltree) (b2 : ltree) (d : bla) *)
(*                      with bla := a (n : nat) (b : blub) with blub := B (c : bla). *)

(* Definition test (A : Type) (u : testrec) (a : list A) (l : ltree) := a. *)

(* MetaRocq Run Print mli (test, add). *)

(* Definition ho (f : bool -> bool) := f true. *)

(* MetaRocq Run Print mli ho. *)

(* MetaRocq Run Print mli Byte.to_nat. *)
