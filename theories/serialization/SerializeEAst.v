From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializePrimitives.
From Peregrine Require Import CeresExtra.

Import ListNotations.
Local Open Scope bs_scope.



(** * Serializers *)

(** ** Term serializer *)

Instance Serialize_def {T : Set} `{Serialize T} : Serialize (def T) :=
  fun d =>
    [ Atom "def"; to_sexp (dname d); to_sexp (dbody d); to_sexp (rarg d) ]%sexp.

Instance Serialize_mfixpoint {T : Set} `{Serialize T} : Serialize (mfixpoint T) :=
  fun f =>
    to_sexp f.

Instance Serialize_term : Serialize term :=
  fix sz (t : term) : sexp :=
    match t with
    | tBox => Atom "tBox"
    | tRel n => [ Atom "tRel"; to_sexp n ]
    | tVar i => [ Atom "tVar"; to_sexp i]
    | tEvar n l => [ Atom "tEvar"; to_sexp n; List (map sz l) ]
    | tLambda na t => [ Atom "tLambda"; to_sexp na; sz t ]
    | tLetIn na b t => [ Atom "tLetIn"; to_sexp na; sz b; sz t ]
    | tApp u v => [ Atom "tApp"; sz u; sz v ]
    | tConst k => [ Atom "tConst"; to_sexp k ]
    | tConstruct ind n args => [ Atom "tConstruct"; to_sexp ind; to_sexp n; List (map sz args)  ]
    | tCase indn c brs => [ Atom "tCase"; to_sexp indn; sz c; List (map (@to_sexp _ (@Serialize_product _ _ _ sz)) brs) ]
    | tProj p c => [ Atom "tProj"; to_sexp p; sz c ]
    | tFix mfix idx => [ Atom "tFix"; @to_sexp _ (@Serialize_mfixpoint _ sz) mfix; to_sexp idx ]
    | tCoFix mfix idx => [ Atom "tCoFix"; @to_sexp _ (@Serialize_mfixpoint _ sz) mfix; to_sexp idx  ]
    | tPrim prim => [ Atom "tPrim"; @to_sexp _ (@Serialize_prim_val _ sz) prim ]
    | tLazy t => [ Atom "tLazy"; sz t ]
    | tForce t => [ Atom "tForce"; sz t ]
    end%sexp.



(** ** Context serializer *)

Instance Serialize_constructor_body : Serialize constructor_body :=
  fun cb =>
    [ Atom "constructor_body"; to_sexp (cstr_name cb); to_sexp (cstr_nargs cb) ]%sexp.

Instance Serialize_projection_body : Serialize projection_body :=
  fun pb =>
    [ Atom "projection_body"; to_sexp (proj_name pb) ]%sexp.

Instance Serialize_one_inductive_body : Serialize one_inductive_body :=
  fun oib =>
    [ Atom "one_inductive_body"
    ; to_sexp (ind_name oib)
    ; to_sexp (ind_propositional oib)
    ; to_sexp (ind_kelim oib)
    ; to_sexp (ind_ctors oib)
    ; to_sexp (ind_projs oib)
    ]%sexp.

Instance Serialize_mutual_inductive_body : Serialize mutual_inductive_body :=
  fun mib =>
    [ Atom "mutual_inductive_body"
    ; to_sexp (ind_finite mib)
    ; to_sexp (ind_npars mib)
    ; to_sexp (ind_bodies mib)
    ]%sexp.

Instance Serialize_constant_body : Serialize constant_body :=
  fun cb =>
    [ Atom "constant_body"
    ; to_sexp (cst_body cb)
    ]%sexp.

Instance Serialize_global_decl : Serialize global_decl :=
  fun gd =>
    match gd with
    | ConstantDecl cb => [ Atom "ConstantDecl"; to_sexp cb ]
    | InductiveDecl mib => [ Atom "InductiveDecl"; to_sexp mib ]
    end%sexp.

Instance Serialize_global_declarations : Serialize global_declarations :=
  fun gd =>
    to_sexp gd.



(** ** Serialize program *)

Instance Serialize_program : Serialize program :=
 fun p =>
    to_sexp p.



(** * Main serialization functions *)

(** ** Term serializer *)
Definition string_of_def {T : Set} `{Serialize T} (d : def T) : string :=
  @to_string (def T) Serialize_def d.

Definition string_of_mfixpoint {T : Set} `{Serialize T} (f : mfixpoint T) : string :=
  @to_string (mfixpoint T) Serialize_mfixpoint f.

Definition string_of_term (t : term) : string :=
  @to_string term Serialize_term t.

(** ** Context serializer *)
Definition string_of_constructor_body (cb : constructor_body) : string :=
  @to_string constructor_body Serialize_constructor_body cb.

Definition string_of_projection_body (pb : projection_body) : string :=
  @to_string projection_body Serialize_projection_body pb.

Definition string_of_one_inductive_body (oib : one_inductive_body) : string :=
  @to_string one_inductive_body Serialize_one_inductive_body oib.

Definition string_of_mutual_inductive_body (mib : mutual_inductive_body) : string :=
  @to_string mutual_inductive_body Serialize_mutual_inductive_body mib.

Definition string_of_constant_body (cb : constant_body) : string :=
  @to_string constant_body Serialize_constant_body cb.

Definition string_of_global_decl (gd : global_decl) : string :=
  @to_string global_decl Serialize_global_decl gd.

Definition string_of_global_declarations (gd : global_declarations) : string :=
  @to_string global_declarations Serialize_global_declarations gd.

(** ** Serialize program *)
Definition string_of_program (p : program) : string :=
  @to_string program Serialize_program p.
