From CertiRocq Require Import AstCommon.
From CertiRocq.LambdaBoxMut Require Import compile.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.
From Peregrine Require Import SerializeCommon.

Import ListNotations.
Local Open Scope bs_scope.



Instance Serialize_Cnstr : Serialize Cnstr :=
  fun c =>
    [ Atom "Cnstr";
      to_sexp (CnstrNm c);
      to_sexp (CnstrArity c)
    ]%sexp.

Instance Serialize_ityp : Serialize ityp :=
  fun t =>
    [ Atom "ityp";
      to_sexp (itypNm t);
      to_sexp (itypCnstrs t)
    ]%sexp.

Instance Serialize_itypPack : Serialize itypPack :=
  fun t => to_sexp t.

Instance Serialize_envClass {T : Set} `{Serialize T} : Serialize (envClass T) :=
  fun e =>
    match e with
    | ecTrm t => [Atom "ecTrm"; to_sexp t]
    | ecTyp n t => [Atom "ecTyp"; to_sexp n; to_sexp t]
    end%sexp.

Instance Serialize_environ {T : Set} `{Serialize T} : Serialize (environ T) :=
  fun env => to_sexp env.

Instance Serialize_Program {T : Set} `{Serialize T} : Serialize (Program T) :=
  fun p =>
    [ Atom "Program";
      to_sexp (main p);
      to_sexp (env p)
    ]%sexp.

Instance Serialize_prim_tag : Serialize prim_tag :=
  fun p =>
    match p with
    | primInt => Atom "primInt"
    | primFloat => Atom "primFloat"
    | primString => Atom "primString"
    end.

Instance Serialize_prim_value {p : primitive_value} : Serialize (prim_value (projT1 p)) :=
  fun v => Atom "v". (* TODO *)

Instance Serialize_primitive_value : Serialize primitive_value :=
  fun p =>
    match projT1 p with
    | primInt => [Atom "primInt"; to_sexp (projT2 p)]
    | primFloat => [Atom "primFloat"; to_sexp (projT2 p)]
    | primString => [Atom "primString"; to_sexp (projT2 p)]
    end%sexp.



Fixpoint Terms_to_list (l : Terms) : list Term :=
  match l with
  | tnil => []
  | tcons t ts => t :: Terms_to_list ts
  end.

Fixpoint Terms_of_list (l : list Term) : Terms :=
  match l with
  | [] => tnil
  | t :: ts => tcons t (Terms_of_list ts)
  end.

Fixpoint Brs_to_list (l : Brs) : list (list name * Term) :=
  match l with
  | bnil => []
  | bcons ns t ts => (ns, t) :: Brs_to_list ts
  end.

Fixpoint Brs_of_list (l : list (list name * Term)) : Brs :=
  match l with
  | [] => bnil
  | (ns,t) :: ts => bcons ns t (Brs_of_list ts)
  end.

Fixpoint Defs_to_list (l : Defs) : list (name * Term * nat) :=
  match l with
  | dnil => []
  | dcons n t i ts => (n, t, i) :: Defs_to_list ts
  end.

Fixpoint Defs_of_list (l : list (name * Term * nat)) : Defs :=
  match l with
  | [] => dnil
  | (n,t,i) :: ts => dcons n t i (Defs_of_list ts)
  end.

#[bypass_check(guard)]
Definition Serialize_Term_aux : Serialize Term :=
  fix sz t {struct t} :=
    match t with
    | TRel n => [Atom "TRel"; to_sexp n]
    | TProof => Atom "TProof"
    | TLambda n t => [Atom "TLambda"; sz t]
    | TLetIn n t1 t2 => [Atom "TLetIn"; to_sexp n; sz t1; sz t2]
    | TApp t1 t2 => [Atom "TApp"; sz t1; sz t2]
    | TConst kn => [Atom "TConst"; to_sexp kn]
    | TConstruct ind n ts =>
      [ Atom "TConstruct";
        to_sexp ind;
        to_sexp n;
        @Serialize_list _ sz (Terms_to_list ts)
      ]
    | TCase ind t brs =>
      [ Atom "TCase";
        to_sexp ind;
        sz t;
        @Serialize_list _
          (@Serialize_product _ _ _ sz)
          (Brs_to_list brs)
      ]
    | TFix ds n =>
      [ Atom "TFix";
        @Serialize_list _
          (@Serialize_product _ _
            (@Serialize_product _ _ _ sz) _)
          (Defs_to_list ds);
        to_sexp n
      ]
    | TPrim p => [Atom "TPrim"; to_sexp p]
    | TWrong s => [Atom "TWrong"; to_sexp s]
    end%sexp.

Instance Serialize_Term : Serialize Term :=
  Serialize_Term_aux.



Definition string_of_Cnstr (x : Cnstr) : string :=
  @to_string Cnstr Serialize_Cnstr x.

Definition string_of_ityp (x : ityp) : string :=
  @to_string ityp Serialize_ityp x.

Definition string_of_itypPack (x : itypPack) : string :=
  @to_string itypPack Serialize_itypPack x.

Definition string_of_envClass {T : Set} `{Serialize T} (x : envClass T) : string :=
  @to_string (envClass T) Serialize_envClass x.

Definition string_of_environ {T : Set} `{Serialize T} (x : environ T) : string :=
  @to_string (environ T) Serialize_environ x.

Definition string_of_Program {T : Set} `{Serialize T} (x : Program T) : string :=
  @to_string (Program T) Serialize_Program x.

Definition string_of_prim_tag (x : prim_tag) : string :=
  @to_string prim_tag Serialize_prim_tag x.

Definition string_of_primitive_value (x : primitive_value) : string :=
  @to_string primitive_value Serialize_primitive_value x.

Definition string_of_Term (x : Term) : string :=
  @to_string Term Serialize_Term x.
