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
|}.

Definition mk_remaps (rs : constant_remappings) : Kernames.kername -> option string :=
  fun kn => option_map (fun '(_, r) => r.(re_const_s))
                       (List.find (fun '(kn', _) => Kernames.eq_kername kn kn') rs).

Definition extract_koka_typed (remaps : constant_remappings)
                              (custom_attr : custom_attributes)
                              (opts : koka_config)
                              (file_name : string)
                              (p : ExAst.global_env)
                              : result' string :=
  match PrintKokaTyped.print_program (mk_remaps remaps) opts.(koka_module) p with
  | Ok s => Ok s
  | Err e => Err ("The typed Koka backend cannot print this program (" ++ e ++ "); the untyped backend, peregrine koka, can")
  end.
