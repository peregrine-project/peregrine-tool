From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.
From Peregrine Require Import DeserializeCommon.
From Peregrine Require Import DeserializePrimitives.
From Peregrine Require Import CeresExtra.

Import ListNotations.
Local Open Scope bs_scope.



(** * Deserializers *)

(** ** Term deserializer *)

Instance Deserialize_def {T : Set} `{Deserialize T} : Deserialize (def T) :=
  fun l e =>
    Deser.match_con "def" []
      [ ("def", con3_ (@Build_def T)) ]
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
      [ ("tRel", con1_ tRel)
      ; ("tVar", con1_ tVar)
      ; ("tEvar", con2 tEvar _from_sexp ds_term_list)
      ; ("tLambda", con2 tLambda _from_sexp ds)
      ; ("tLetIn", con3 tLetIn _from_sexp ds ds)
      ; ("tApp", con2 tApp ds ds)
      ; ("tConst", con1_ tConst)
      ; ("tConstruct", con3 tConstruct _from_sexp _from_sexp ds_term_list)
      ; ("tCase", con3 tCase _from_sexp ds ds_cases)
      ; ("tProj", con2 tProj _from_sexp ds)
      ; ("tFix", con2 tFix ds_mfixpoint _from_sexp)
      ; ("tCoFix", con2 tCoFix ds_mfixpoint _from_sexp)
      ; ("tPrim", con1 tPrim ds_prim)
      ; ("tLazy", con1 tLazy ds)
      ; ("tForce", con1 tForce ds)
      ]
      l e.

Instance Deserialize_term : Deserialize term :=
  deserialize_term.



(** ** Context deserializer *)

Instance Deserialize_constructor_body : Deserialize constructor_body :=
  fun l e =>
    Deser.match_con "constructor_body" []
      [ ("constructor_body", con2_ mkConstructor) ]
      l e.

Instance Deserialize_projection_body : Deserialize projection_body :=
  fun l e =>
    Deser.match_con "projection_body" []
      [ ("projection_body", con1_ mkProjection) ]
      l e.

Instance Deserialize_one_inductive_body : Deserialize one_inductive_body :=
  fun l e =>
    Deser.match_con "one_inductive_body" []
      [ ("one_inductive_body", con5_ Build_one_inductive_body) ]
      l e.

Instance Deserialize_mutual_inductive_body : Deserialize mutual_inductive_body :=
  fun l e =>
    Deser.match_con "mutual_inductive_body" []
      [ ("mutual_inductive_body", con3_ Build_mutual_inductive_body) ]
      l e.

Instance Deserialize_constant_body : Deserialize constant_body :=
  fun l e =>
    Deser.match_con "constant_body" []
      [ ("constant_body", con1_ Build_constant_body) ]
      l e.

Instance Deserialize_global_decl : Deserialize global_decl :=
  fun l e =>
    Deser.match_con "global_decl"
      []
      [ ("ConstantDecl", con1_ ConstantDecl)
      ; ("InductiveDecl", con1_ InductiveDecl)
      ]
      l e.

Instance Deserialize_global_declarations : Deserialize global_declarations :=
 fun l e =>
    _from_sexp l e.



(** ** Deserialize program *)

Instance Deserialize_program : Deserialize program :=
 fun l e =>
    _from_sexp l e.



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
