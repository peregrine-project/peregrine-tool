From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Primitive.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require LeanCompile.

Import MonadNotation.

Local Open Scope bs_scope.

(* Terms [LeanCompile] has no translation for, shared by the Lean, F# and
   Koka backends.  [compile_term] would turn them into [LPanic], which the
   printers emit as the erased-value placeholder, so the program would
   compute a wrong result instead of failing.  The phases these backends
   require remove [tBox], [tLazy], [tForce] and [tCoFix]; [tCoFix] is still
   listed so that it fails loudly should that ever change. *)
Fixpoint unsupported_term (t : EAst.term) : option string :=
  let first := fix first (l : list (option string)) :=
    match l with
    | [] => None
    | Some s :: _ => Some s
    | None :: l => first l
    end in
  match t with
  | EAst.tEvar _ _ => Some "tEvar"
  | EAst.tCoFix _ _ => Some "tCoFix"
  | EAst.tPrim p =>
    match projT1 p with
    | Primitive.primInt | Primitive.primString => None
    | Primitive.primFloat => Some "primitive floats"
    | Primitive.primArray => Some "primitive arrays"
    end
  | EAst.tLambda _ b | EAst.tProj _ b | EAst.tLazy b | EAst.tForce b =>
    unsupported_term b
  | EAst.tLetIn _ b u | EAst.tApp b u =>
    first [unsupported_term b; unsupported_term u]
  | EAst.tConstruct _ _ args => first (List.map unsupported_term args)
  | EAst.tCase _ d brs =>
    first (unsupported_term d :: List.map (fun br => unsupported_term (snd br)) brs)
  | EAst.tFix mfix _ => first (List.map (fun d => unsupported_term d.(EAst.dbody)) mfix)
  | _ => None
  end.

Definition check_supported (backend : string) (remaps : constant_remappings) (p : EAst.program) : result' unit :=
  let check_body (where_ : string) (t : EAst.term) : result' unit :=
    match unsupported_term t with
    | Some s => Err ("The " ++ backend ++ " backend does not support " ++ s ++ ", used in " ++ where_)
    | None => Ok tt
    end in
  let check_decl (d : kername * EAst.global_decl) : result' unit :=
    match snd d with
    (* The body of a remapped constant is not printed. *)
    | EAst.ConstantDecl {| EAst.cst_body := Some t |} =>
      match LeanCompile.lookup_remap remaps (fst d) with
      | Some _ => Ok tt
      | None => check_body (string_of_kername (fst d)) t
      end
    | _ => Ok tt
    end in
  monad_iter check_decl (fst p);;
  check_body "the main term" (snd p).

