From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From CertiRocq Require Import CodegenWasm.toplevel.
From CertiRocq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CertiRocqBackend.
From Wasm Require Import binary_format_printer.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_wasm_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 1;  (* lambda lifting; 0 keeps every closure (#133) *)
  anf_conf  := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition wasm_phases := {|
  implement_box_c  := Required;
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



Definition wasm_pipeline prs (p : EAst.program) :=
  anf_pipeline compile_LambdaANF_to_Wasm prs p.

Definition print_wasm p : string :=
  String.parse (binary_of_module p).

(* The Int63 operations that CertiCoq-Wasm compiles natively ([primop_map] of
   LambdaANF_to_Wasm_primints, proved correct there).  They are constants without a
   body, so the pipeline's axiom check needs them registered.  The code generator
   finds the operation by its name and ignores [prim_target] and [prim_alloc],
   so neither field has an effect here. *)
Definition int63_mod : Kernames.modpath :=
  Kernames.MPfile ["PrimInt63"; "Int63"; "Cyclic"; "Numbers"; "Corelib"].

Definition int63_prims : primitives :=
  map (fun '(op, arity, alloc) =>
         {| prim_name := (int63_mod, op); prim_target := op; prim_arity := arity; prim_alloc := alloc |})
      [("add", 2, false); ("sub", 2, false); ("mul", 2, false); ("div", 2, false); ("mod", 2, false);
       ("lsl", 2, false); ("lsr", 2, false); ("land", 2, false); ("lor", 2, false); ("lxor", 2, false);
       ("eqb", 2, false); ("ltb", 2, false); ("leb", 2, false); ("compare", 2, false);
       ("addc", 2, true); ("addcarryc", 2, true); ("subc", 2, true); ("subcarryc", 2, true);
       ("mulc", 2, true); ("head0", 1, false); ("tail0", 1, false); ("diveucl", 2, true);
       ("diveucl_21", 3, true); ("addmuldiv", 3, false)].

(* A user's remapping of one of these operations replaces its entry, but the code
   generator still compiles the operation natively: only the arity is taken from
   the user's entry. *)
Definition wasm_prims (remaps : constant_remappings) : primitives :=
  let user := mk_prims remaps in
  let is_user (pr : primitive) := existsb (fun u => Kernames.eq_kername u.(prim_name) pr.(prim_name)) user in
  List.app user (filter (fun pr => negb (is_user pr)) int63_prims).

Definition extract_wasm (remaps : constant_remappings)
                        (custom_attr : custom_attributes)
                        (opts : wasm_config)
                        (file_name : string)
                        (p : EAst.program)
                        : result' string :=
  let config := mk_opts opts in
  let prs := wasm_prims remaps in
  let (res, _) := run_pipeline EAst.program _ config p (wasm_pipeline prs) in
  match res with
  | compM.Ret m => Ok (print_wasm m)
  | compM.Err s => Err s
  end.
