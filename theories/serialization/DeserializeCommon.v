From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import Universes.
From Peregrine Require Import CeresExtra.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.

Import ListNotations.
Local Open Scope bs_scope.



(** * Deserializers *)

(** ** Kername *)
Instance Deserialize_ident : Deserialize ident :=
  fun l e =>
    match e with
    | Atom_ (Str s) => inr s
    | _ => inl (DeserError l "error")
    end.

Instance Deserialize_dirpath : Deserialize dirpath :=
 fun l e =>
    _from_sexp l e.

Instance Deserialize_modpath : Deserialize modpath :=
  fix ds (l : loc) (e : sexp) : error + modpath :=
    Deser.match_con "modpath" []
      [ ("MPfile", Deser.con1_ MPfile)
      ; ("MPbound", Deser.con3_ MPbound)
      ; ("MPdot", Deser.con2 MPdot ds _from_sexp )
      ] l e.

Instance Deserialize_kername : Deserialize kername :=
 fun l e =>
    _from_sexp l e.

Instance Deserialize_inductive : Deserialize inductive :=
  fun l e =>
    Deser.match_con "inductive" []
      [ ("inductive", Deser.con2_ mkInd) ]
      l e.

Instance Deserialize_projection : Deserialize projection :=
  fun l e =>
    Deser.match_con "projection" []
      [ ("projection", Deser.con3_ mkProjection) ]
      l e.

(** ** BasicAst *)
Instance Deserialize_name : Deserialize name :=
  fun l e =>
    Deser.match_con "name"
      [ ("nAnon", nAnon) ]
      [ ("nNamed", Deser.con1_ nNamed) ]
      l e.

Instance Deserialize_recursivity_kind : Deserialize recursivity_kind :=
  fun l e =>
    Deser.match_con "recursivity_kind"
      [ ("Finite", Finite)
      ; ("CoFinite", CoFinite)
      ; ("BiFinite", BiFinite)
      ]
      []
      l e.

(** ** Universe *)
Instance Deserialize_allowed_eliminations : Deserialize allowed_eliminations :=
  fun l e =>
    Deser.match_con "allowed_eliminations"
      [ ("IntoSProp", IntoSProp)
      ; ("IntoPropSProp", IntoPropSProp)
      ; ("IntoSetPropSProp", IntoSetPropSProp)
      ; ("IntoAny", IntoAny)
      ]
      []
      l e.



(** * Main deserialization functions *)

(** ** Kername *)
Definition ident_of_string (s : string) : error + ident :=
  @from_string ident Deserialize_ident s.

Definition dirpath_of_string (s : string) : error + dirpath :=
  @from_string dirpath Deserialize_dirpath s.

Definition modpath_of_string (s : string) : error + modpath :=
  @from_string modpath Deserialize_modpath s.

Definition kername_of_string (s : string) : error + kername :=
  @from_string kername Deserialize_kername s.

Definition inductive_of_string (s : string) : error + inductive :=
  @from_string inductive Deserialize_inductive s.

Definition projection_of_string (s : string) : error + projection :=
  @from_string projection Deserialize_projection s.

(** ** BasicAst *)
Definition name_of_string (s : string) : error + name :=
  @from_string name Deserialize_name s.

Definition recursivity_kind_of_string (s : string) : error + recursivity_kind :=
  @from_string recursivity_kind Deserialize_recursivity_kind s.

(** ** Universe *)
Definition allowed_eliminations_of_string (s : string) : error + allowed_eliminations :=
  @from_string allowed_eliminations Deserialize_allowed_eliminations s.
