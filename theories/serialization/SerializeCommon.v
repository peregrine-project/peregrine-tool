From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import Universes.
From Stdlib Require Import List.
From Ceres Require Import Ceres.

Import ListNotations.
Local Open Scope bs_scope.



(** * Serializers *)

(** ** Kername *)
Instance Serialize_ident : Serialize ident :=
  fun i =>
    Atom (Str i).

Instance Serialize_dirpath : Serialize dirpath :=
  fun d =>
    to_sexp d.

Instance Serialize_modpath : Serialize modpath :=
  fix sz (m : modpath) : sexp :=
    match m with
    | MPfile dp => [ Atom "MPfile"; to_sexp dp ]
    | MPbound dp id i => [ Atom "MPbound"; to_sexp dp; to_sexp id; to_sexp i ]
    | MPdot mp id => [ Atom "MPdot"; sz mp; to_sexp id ]
    end%sexp.

Instance Serialize_kername : Serialize kername :=
  fun kn =>
    to_sexp kn.

Instance Serialize_inductive : Serialize inductive :=
  fun i =>
    [ Atom "inductive"; to_sexp (inductive_mind i); to_sexp (inductive_ind i) ]%sexp.

Instance Serialize_projection : Serialize projection :=
  fun p =>
    [ Atom "projection"; to_sexp (proj_ind p); to_sexp (proj_npars p); to_sexp (proj_arg p) ]%sexp.

(** ** BasicAst *)
Instance Serialize_name : Serialize name :=
  fun n =>
    match n with
    | nAnon => Atom "nAnon"
    | nNamed i => [ Atom "nNamed"; to_sexp i ]
    end%sexp.

Instance Serialize_recursivity_kind : Serialize recursivity_kind :=
  fun x =>
    match x with
    | Finite => Atom "Finite"
    | CoFinite => Atom "CoFinite"
    | BiFinite => Atom "BiFinite"
    end%sexp.

(** ** Universe *)
Instance Serialize_allowed_eliminations : Serialize allowed_eliminations :=
  fun x =>
    match x with
    | IntoSProp => Atom "IntoSProp"
    | IntoPropSProp => Atom "IntoPropSProp"
    | IntoSetPropSProp => Atom "IntoSetPropSProp"
    | IntoAny => Atom "IntoAny"
    end%sexp.



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



(** * Main serialization functions *)

(** ** Kername *)
Definition string_of_ident (id : ident) : string :=
  @to_string ident Serialize_ident id.

Definition string_of_dirpath (d : dirpath) : string :=
  @to_string dirpath Serialize_dirpath d.

Definition string_of_modpath (m : modpath) : string :=
  @to_string modpath Serialize_modpath m.

Definition string_of_kername (kn : kername) : string :=
  @to_string kername Serialize_kername kn.

Definition string_of_inductive (ind : inductive) : string :=
  @to_string inductive Serialize_inductive ind.

Definition string_of_projection (proj : projection) : string :=
  @to_string projection Serialize_projection proj.

(** ** BasicAst *)
Definition string_of_name (n : name) : string :=
  @to_string name Serialize_name n.

Definition string_of_recursivity_kind (x : recursivity_kind) : string :=
  @to_string recursivity_kind Serialize_recursivity_kind x.

(** ** Universe *)
Definition string_of_allowed_eliminations (x : allowed_eliminations) : string :=
  @to_string allowed_eliminations Serialize_allowed_eliminations x.



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
