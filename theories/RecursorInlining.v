(** * Automatic inlining of recursors

    Rocq's own extraction inlines the automatically generated eliminators
    [I_rect] / [I_rec] of every inductive [I] (see [Mlutil] in Rocq's
    extraction plugin; only [Extraction NoInline] prevents it).  Together
    with beta reduction this turns applications of recursors back into
    direct pattern matching and recursion, which the target compilers handle
    much better than closures passed to a generic recursor.

    Peregrine inlines exactly the constants listed in [inlinings_opts] (from
    the configuration or from [--attributes] files).  [recursor_inlinings]
    computes such a list from the program itself: every constant named
    [mp.I_rect] or [mp.I_rec] such that the environment declares, under the
    same module path [mp], a mutual inductive block with a body named [I].
    Both the untyped ([EAst]) and the typed ([ExAst]) environments are
    supported.

    [recursor_attributes] packages the list as an [attributes_config]; the
    pipeline merges it into the configuration exactly as it merges the
    [--attributes] files, before name sanitisation.  Enabling
    [--inline-recursors] therefore has the same effect as passing an
    attribute file that lists these constants.  The inlining pass itself
    (MetaRocq's [EInlining.inline_transformation]) is not touched; its
    specification is stated for an arbitrary set of constants to inline, so
    computing the set here adds nothing to what has to be trusted. *)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require BasicAst Universes.
From MetaRocq.Erasure Require EAst ExAst.
From MetaRocq.Erasure.Typed Require Utils.
From Peregrine Require Import Config PAst.

Import ListNotations.
Local Open Scope bs_scope.

(** The eliminators Rocq generates (in [Type]) for an inductive body [I]
    declared at module path [mp]. *)
Definition recursor_names (mp : modpath) (I : ident) : list kername :=
  [(mp, I ++ "_rect"); (mp, I ++ "_rec")].

Section Generic.
  (** [decl] is [EAst.global_decl] or [ExAst.global_decl]. *)
  Context {decl : Type}
    (is_constant : decl -> bool)
    (* Names of the bodies of a mutual inductive block, [[]] for other
       declarations. *)
    (inductive_names : decl -> list ident).

  Definition recursor_inlinings_env (env : list (kername * decl)) : list kername :=
    let consts := MetaRocq.Erasure.Typed.Utils.kername_set_of_list
      (List.map fst (List.filter (fun '(_, d) => is_constant d) env)) in
    List.concat (List.map (fun '(kn, d) =>
      List.filter (fun r => KernameSet.mem r consts)
        (List.concat (List.map (recursor_names (fst kn)) (inductive_names d)))) env).
End Generic.

Definition east_is_constant (d : EAst.global_decl) : bool :=
  match d with EAst.ConstantDecl _ => true | _ => false end.

Definition east_inductive_names (d : EAst.global_decl) : list ident :=
  match d with
  | EAst.InductiveDecl mib => List.map EAst.ind_name mib.(EAst.ind_bodies)
  | _ => []
  end.

Definition exast_is_constant (d : ExAst.global_decl) : bool :=
  match d with ExAst.ConstantDecl _ => true | _ => false end.

Definition exast_inductive_names (d : ExAst.global_decl) : list ident :=
  match d with
  | ExAst.InductiveDecl mib => List.map ExAst.ind_name mib.(ExAst.ind_bodies)
  | _ => []
  end.

(** The recursors of the program's environment, in environment order. *)
Definition recursor_inlinings (p : PAst) : list kername :=
  match p with
  | Untyped env _ =>
      recursor_inlinings_env east_is_constant east_inductive_names env
  | Typed env _ =>
      recursor_inlinings_env exast_is_constant exast_inductive_names
        (List.map (fun '(kn, _, d) => (kn, d)) env)
  end.

(** The same list, as the attribute file [--inline-recursors] stands for. *)
Definition recursor_attributes (p : PAst) : attributes_config := {|
  inlinings_opt         := recursor_inlinings p;
  const_remappings_opt  := [];
  ind_remappings_opt    := [];
  cstr_reorders_opt     := [];
  custom_attributes_opt := [];
|}.

(** ** Checks *)

Module RecursorInliningChecks.

  Definition mp : modpath := MPfile ["Datatypes"; "Init"; "Corelib"].
  Definition mp' : modpath := MPfile ["Other"].

  (* Untyped environment. *)
  Definition body (n : ident) : EAst.one_inductive_body :=
    {| EAst.ind_name := n; EAst.ind_propositional := false;
       EAst.ind_kelim := Universes.IntoAny;
       EAst.ind_ctors := []; EAst.ind_projs := [] |}.
  Definition mib (ns : list ident) : EAst.global_decl :=
    EAst.InductiveDecl
      {| EAst.ind_finite := BasicAst.Finite; EAst.ind_npars := 0;
         EAst.ind_bodies := List.map body ns |}.
  Definition cst : EAst.global_decl := EAst.ConstantDecl {| EAst.cst_body := Some EAst.tBox |}.

  Definition env : untyped_env :=
    [ ((mp, "nat"), mib ["nat"]);
      ((mp, "nat_rect"), cst);
      ((mp, "nat_rec"), cst);
      ((mp, "nat_ind"), cst);                (* not a recursor name *)
      ((mp', "nat_rect"), cst);              (* other module path: no [nat] there *)
      ((mp, "list_rect"), cst);              (* inductive [list] not declared *)
      ((mp, "Even"), mib ["Even"; "Odd"]);   (* mutual block: every body counts *)
      ((mp, "Odd_rec"), cst);
      ((mp, "Even_rect"), cst);
      ((mp', "Odd"), mib ["Odd"]) ].         (* [Odd] elsewhere does not make [mp.Odd_rec] twice *)

  Example recursor_inlinings_untyped :
    recursor_inlinings (Untyped env None)
    = [(mp, "nat_rect"); (mp, "nat_rec"); (mp, "Even_rect"); (mp, "Odd_rec")].
  Proof. vm_compute. reflexivity. Qed.

  Example recursor_inlinings_empty :
    recursor_inlinings (Untyped [((mp, "nat"), mib ["nat"])] None) = [].
  Proof. vm_compute. reflexivity. Qed.

  (* Typed environment. *)
  Definition tbody (n : ident) : ExAst.one_inductive_body :=
    {| ExAst.ind_name := n; ExAst.ind_propositional := false;
       ExAst.ind_kelim := Universes.IntoAny; ExAst.ind_type_vars := [];
       ExAst.ind_ctors := []; ExAst.ind_projs := [] |}.
  Definition tmib (ns : list ident) : ExAst.global_decl :=
    ExAst.InductiveDecl
      {| ExAst.ind_finite := BasicAst.Finite; ExAst.ind_npars := 0;
         ExAst.ind_bodies := List.map tbody ns |}.
  Definition tcst : ExAst.global_decl :=
    ExAst.ConstantDecl {| ExAst.cst_type := ([], ExAst.TBox); ExAst.cst_body := Some EAst.tBox |}.

  Definition tenv : typed_env :=
    [ ((mp, "nat"), true, tmib ["nat"]);
      ((mp, "nat_rec"), true, tcst);
      ((mp, "nat_ind"), true, tcst);
      ((mp, "bool"), true, ExAst.TypeAliasDecl None);  (* a type alias is not an inductive *)
      ((mp, "bool_rect"), true, tcst);
      ((mp', "nat_rect"), false, tcst) ].

  Example recursor_inlinings_typed :
    recursor_inlinings (Typed tenv None) = [(mp, "nat_rec")].
  Proof. vm_compute. reflexivity. Qed.

End RecursorInliningChecks.
