From MetaRocq.Erasure Require Import ExAst.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.
From Peregrine Require Import DeserializeCommon.
From Peregrine Require Import DeserializeEAst.
From Peregrine Require Import CeresExtra.

Import ListNotations.
Local Open Scope bs_scope.



(** * Deserializers *)

(* Inductive box_type :=
| TBox
| TAny
| TArr (dom : box_type) (codom : box_type)
| TApp (_ : box_type) (_ : box_type)
| TVar (_ : nat) (* Level of type variable *)
| TInd (_ : inductive)
| TConst (_ : kername). *)
Instance Deserialize_box_type : Deserialize box_type :=
  fix ds (l : loc) (e : sexp) : error + box_type :=
    Deser.match_con "box_type"
      [ ("TBox", TBox)
      ; ("TAny", TAny)
      ]
      [ ("TArr", Deser.con2 TArr ds ds)
      ; ("TApp", Deser.con2 TApp ds ds)
      ; ("TVar", Deser.con1_ TVar)
      ; ("TInd", Deser.con1_ TInd)
      ; ("TConst", Deser.con1_ TConst )
      ] l e.

(* Record type_var_info :=
  { tvar_name : name;
    tvar_is_logical : bool;
    tvar_is_arity : bool;
    tvar_is_sort : bool; }. *)
Instance Deserialize_type_var_info : Deserialize type_var_info :=
  fun l e =>
    Deser.match_con "type_var_info" []
      [ ("type_var_info", Deser.con4_ Build_type_var_info) ]
      l e.

(* Record constant_body :=
  { cst_type : list name * box_type;
    cst_body : option term; }. *)
Instance Deserialize_constant_body : Deserialize constant_body :=
  fun l e =>
    Deser.match_con "constant_body" []
      [ ("constant_body", Deser.con2_ Build_constant_body) ]
      l e.

(* Record one_inductive_body :=
  { ind_name : ident;
    ind_propositional : bool;
    ind_kelim : Universes.allowed_eliminations;
    ind_type_vars : list type_var_info;
    ind_ctors : list (ident *
                      list (name * box_type) *
                      nat (* original arities, unfortunately needed for erases_one_inductive_body *)
                     );
    ind_projs : list (ident * box_type); }. *)
Instance Deserialize_one_inductive_body : Deserialize one_inductive_body :=
  fun l e =>
    Deser.match_con "one_inductive_body" []
      [ ("one_inductive_body", Deser.con6_ Build_one_inductive_body) ]
      l e.

(* Record mutual_inductive_body :=
  { ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_bodies : list one_inductive_body }. *)
Instance Deserialize_mutual_inductive_body : Deserialize mutual_inductive_body :=
  fun l e =>
    Deser.match_con "mutual_inductive_body" []
      [ ("mutual_inductive_body", Deser.con3_ Build_mutual_inductive_body) ]
      l e.

(* Inductive global_decl :=
| ConstantDecl : constant_body -> global_decl
| InductiveDecl : mutual_inductive_body -> global_decl
| TypeAliasDecl : option (list type_var_info * box_type) -> global_decl. *)
Instance Deserialize_global_decl : Deserialize global_decl :=
  fun l e =>
    Deser.match_con "global_decl"
      []
      [ ("ConstantDecl", Deser.con1_ ConstantDecl)
      ; ("InductiveDecl", Deser.con1_ InductiveDecl)
      ; ("TypeAliasDecl", Deser.con1_ TypeAliasDecl)
      ]
      l e.

(* Definition global_env := list (kername * bool (* has_deps *) * global_decl). *)
Instance Deserialize_global_env : Deserialize global_env :=
 fun l e =>
    _from_sexp l e.



(** * Main deserialization functions *)

Definition box_type_of_string (s : string) : error + box_type :=
  @from_string box_type Deserialize_box_type s.

Definition type_var_info_of_string (s : string) : error + type_var_info :=
  @from_string type_var_info Deserialize_type_var_info s.

Definition constant_body_of_string (s : string) : error + constant_body :=
  @from_string constant_body Deserialize_constant_body s.

Definition one_inductive_body_of_string (s : string) : error + one_inductive_body :=
  @from_string one_inductive_body Deserialize_one_inductive_body s.

Definition mutual_inductive_body_of_string (s : string) : error + mutual_inductive_body :=
  @from_string mutual_inductive_body Deserialize_mutual_inductive_body s.

Definition global_decl_of_string (s : string) : error + global_decl :=
  @from_string global_decl Deserialize_global_decl s.

Definition global_env_of_string (s : string) : error + global_env :=
  @from_string global_env Deserialize_global_env s.
