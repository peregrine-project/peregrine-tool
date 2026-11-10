From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require ExAst.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require PrintKokaTyped.

Import MonadNotation.

Local Open Scope bs_scope.

(* The typed Koka backend (experimental, unverified) prints typed lambda-box,
   so the generated program needs no casts; it shares the configuration of the
   untyped Koka backend ([KokaBackend]). *)

Definition koka_typed_phases := {|
  implement_box_c  := Compatible false;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
  cse_c            := Compatible false;
  lift_constants_c := Compatible false;
|}.

(* A remapped constant is called with its arity, and its module, if any, is imported. *)
Definition mk_remaps (rs : constant_remappings) : Kernames.kername -> option (string * nat) :=
  fun kn => option_map (fun '(_, r) => (r.(re_const_s), r.(re_const_arity)))
                       (List.find (fun '(kn', _) => Kernames.eq_kername kn kn') rs).

Definition remap_imports (rs : constant_remappings) : list string :=
  List.fold_right (fun '(_, r) acc =>
    match r.(re_const_ext) with
    | Some m => if existsb (String.eqb m) acc then acc else m :: acc
    | None => acc
    end) [] rs.

Definition extract_koka_typed (remaps : constant_remappings)
                              (custom_attr : custom_attributes)
                              (opts : koka_config)
                              (file_name : string)
                              (p : ExAst.global_env)
                              : result' string :=
  match PrintKokaTyped.print_program (mk_remaps remaps) (remap_imports remaps) opts.(koka_module) p with
  | Ok s => Ok s
  | Err e => Err ("The typed Koka backend cannot print this program (" ++ e ++ "); the untyped backend, peregrine koka, can")
  end.
