From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From Ceres Require Import Ceres.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializePrimitives.

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



(** * Deserializers *)

(** ** Term deserializer *)

Instance Deserialize_def {T : Set} `{Deserialize T} : Deserialize (def T) :=
  fun l e =>
    Deser.match_con "def" []
      [ ("def", Deser.con3_ (@Build_def T)) ]
      l e.

Instance Deserialize_mfixpoint {T : Set} `{Deserialize T} : Deserialize (mfixpoint T) :=
 fun l e =>
    _from_sexp l e.

#[bypass_check(guard)]
Fixpoint deserialize_term (l : loc) (e : sexp) {struct e} : error + term :=
    let ds := deserialize_term in
    let ds_term_list : FromSexp (list term) := fun l e => @_from_sexp (list term) (@Deserialize_list term ds) l e in
    let ds_mfixpoint : FromSexp (mfixpoint term) := @_from_sexp (mfixpoint term) (@Deserialize_mfixpoint term ds) in
    let ds_cases : FromSexp (list (list BasicAst.name * term)) := @_from_sexp (list (list BasicAst.name * term))
      (@Deserialize_list (list BasicAst.name * term) (@Deserialize_prod (list BasicAst.name) term _from_sexp ds)) in
    let ds_prim : FromSexp (EPrimitive.prim_val term) := @_from_sexp (EPrimitive.prim_val term) (@Deserialize_prim_val term ds) in
    Deser.match_con "term"
      [ ("tBox", tBox) ]
      [ ("tRel", Deser.con1_ tRel)
      ; ("tVar", Deser.con1_ tVar)
      ; ("tEvar", Deser.con2 tEvar _from_sexp ds_term_list)
      ; ("tLambda", Deser.con2 tLambda _from_sexp ds)
      ; ("tLetIn", Deser.con3 tLetIn _from_sexp ds ds)
      ; ("tApp", Deser.con2 tApp ds ds)
      ; ("tConst", Deser.con1_ tConst)
      ; ("tConstruct", Deser.con3 tConstruct _from_sexp _from_sexp ds_term_list)
      ; ("tCase", Deser.con3 tCase _from_sexp ds ds_cases)
      ; ("tProj", Deser.con2 tProj _from_sexp ds)
      ; ("tFix", Deser.con2 tFix ds_mfixpoint _from_sexp)
      ; ("tCoFix", Deser.con2 tCoFix ds_mfixpoint _from_sexp)
      ; ("tPrim", Deser.con1 tPrim ds_prim)
      ; ("tLazy", Deser.con1 tLazy ds)
      ; ("tForce", Deser.con1 tForce ds)
      ]
      l e.

Instance Deserialize_term : Deserialize term :=
  deserialize_term.



(** ** Context deserializer *)

Instance Deserialize_constructor_body : Deserialize constructor_body :=
  fun l e =>
    Deser.match_con "constructor_body" []
      [ ("constructor_body", Deser.con2_ mkConstructor) ]
      l e.

Instance Deserialize_projection_body : Deserialize projection_body :=
  fun l e =>
    Deser.match_con "projection_body" []
      [ ("projection_body", Deser.con1_ mkProjection) ]
      l e.

Instance Deserialize_one_inductive_body : Deserialize one_inductive_body :=
  fun l e =>
    Deser.match_con "one_inductive_body" []
      [ ("one_inductive_body", Deser.con5_ Build_one_inductive_body) ]
      l e.

Instance Deserialize_mutual_inductive_body : Deserialize mutual_inductive_body :=
  fun l e =>
    Deser.match_con "mutual_inductive_body" []
      [ ("mutual_inductive_body", Deser.con3_ Build_mutual_inductive_body) ]
      l e.

Instance Deserialize_constant_body : Deserialize constant_body :=
  fun l e =>
    Deser.match_con "constant_body" []
      [ ("constant_body", Deser.con1_ Build_constant_body) ]
      l e.

Instance Deserialize_global_decl : Deserialize global_decl :=
  fun l e =>
    Deser.match_con "global_decl"
      []
      [ ("ConstantDecl", Deser.con1_ ConstantDecl)
      ; ("InductiveDecl", Deser.con1_ InductiveDecl)
      ]
      l e.

Instance Deserialize_global_declarations : Deserialize global_declarations :=
 fun l e =>
    _from_sexp l e.



(** ** Deserialize program *)

Instance Deserialize_program : Deserialize program :=
 fun l e =>
    _from_sexp l e.



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



(** * Main deserialization functions *)

(** ** Term deserializer *)
Definition def_of_string {T : Set} `{Deserialize T} (s : string) : error + (def T) :=
  @from_string (def T) Deserialize_def s.

Definition mfixpoint_of_string {T : Set} `{Deserialize T} (s : string) : error + (mfixpoint T) :=
  @from_string (mfixpoint T) Deserialize_mfixpoint s.

Definition term_of_string (s : string) : error + term :=
  @from_string term Deserialize_term s.

(** ** Context deserializer *)
Definition constructor_body_of_string (s : string) : error + constructor_body :=
  @from_string constructor_body Deserialize_constructor_body s.

Definition projection_body_of_string (s : string) : error + projection_body :=
  @from_string projection_body Deserialize_projection_body s.

Definition one_inductive_body_of_string (s : string) : error + one_inductive_body :=
  @from_string one_inductive_body Deserialize_one_inductive_body s.

Definition mutual_inductive_body_of_string (s : string) : error + mutual_inductive_body :=
  @from_string mutual_inductive_body Deserialize_mutual_inductive_body s.

Definition constant_body_of_string (s : string) : error + constant_body :=
  @from_string constant_body Deserialize_constant_body s.

Definition global_decl_of_string (s : string) : error + global_decl :=
  @from_string global_decl Deserialize_global_decl s.

Definition context_of_string (s : string) : error + global_declarations :=
  @from_string global_declarations Deserialize_global_declarations s.

(** ** Deserialize program *)
Definition program_of_string (s : string) : error + program :=
  @from_string program Deserialize_program s.
