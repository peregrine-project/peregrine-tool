(* LLVM backend: CertiRocq's CodegenLLVM (LambdaANF -> Vellvm's LLVM AST),
   printed as textual LLVM IR. Mirrors WasmBackend.v. CodegenLLVM is not in
   any CertiRocq release yet; rocq-peregrine.opam pins CertiRocq by commit. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From CertiRocq Require Import CodegenLLVM.toplevel.
From CertiRocq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CertiRocqBackend.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_llvm_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 1;  (* lambda lifting; 0 keeps every closure (#133) *)
  anf_conf  := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition llvm_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
  cse_c            := Compatible false;
|}.



Definition llvm_pipeline prs (p : EAst.program) :=
  anf_pipeline compile_LambdaANF_to_LLVM prs p.

(* The emitted module calls the runtime's [garbage_collect] without declaring
   it; the correctness statement of CodegenLLVM puts this declaration in front
   of the module ([runtime_prelude]), and so does the printer, which makes the
   file a complete module. *)
Definition llvm_prelude : string :=
  "declare void @garbage_collect(ptr)" ++ String.String "010"%byte String.EmptyString.

(* The module calls each remapped constant without declaring it, so the printer
   adds the declarations, as for [garbage_collect].  Every value is an [i64], and a
   constant that allocates also takes the thread info (see [Eprim] in
   LambdaANF_to_LLVM).  Two constants may share a target, which is declared once. *)
Definition llvm_prim_decl (r : remapped_constant) : string :=
  let args := List.app (if r.(re_const_gc) then ["ptr"] else []) (repeat "i64" r.(re_const_arity)) in
  "declare i64 @" ++ r.(re_const_s) ++ "(" ++ String.concat ", " args ++ ")"
    ++ String.String "010"%byte String.EmptyString.

Fixpoint llvm_prim_decls (seen : list string) (rs : constant_remappings) : string :=
  match rs with
  | [] => ""
  | (_, r) :: rs =>
    if existsb (String.eqb r.(re_const_s)) seen then llvm_prim_decls seen rs
    else llvm_prim_decl r ++ llvm_prim_decls (r.(re_const_s) :: seen) rs
  end.

Definition print_llvm (remaps : constant_remappings) p : string :=
  llvm_prelude ++ llvm_prim_decls [] remaps ++ serialize_bytestring p.

Definition extract_llvm (remaps : constant_remappings)
                        (custom_attr : custom_attributes)
                        (opts : llvm_config)
                        (file_name : string)
                        (p : EAst.program)
                        : result' string :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let (res, _) := run_pipeline EAst.program _ config p (llvm_pipeline prs) in
  match res with
  | compM.Ret m => Ok (print_llvm remaps m)
  | compM.Err s => Err s
  end.
