(* This file is based on erasure/theories/Extraction.v from MetaRocq *)
From Stdlib Require Import Ascii FSets ExtrOcamlBasic ExtrOCamlFloats ExtrOCamlInt63.
From MetaRocq.Utils Require Import utils.

(* Ignore [Decimal.int] before the extraction issue is solved:
    https://github.com/rocq-prover/rocq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".
Extract Inductive Hexadecimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".
Extract Inductive Number.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Blacklist
           Classes config uGraph Universes Ast String List Nat Int Init
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality Classes
           Uint63
           Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

From MetaRocq.Erasure Require Import EAst EAstUtils EInduction ELiftSubst EGlobalEnv Extract ErasureFunction Erasure.
From TypedExtraction.Rust Require Import PluginExtract.
From MetaRocq.Erasure.Typed Require Import Utils.


Extraction Inline Equations.Prop.Classes.noConfusion.
Extraction Inline Equations.Prop.Logic.eq_elim.
Extraction Inline Equations.Prop.Logic.eq_elim_r.
Extraction Inline Equations.Prop.Logic.transport.
Extraction Inline Equations.Prop.Logic.transport_r.
Extraction Inline Equations.Prop.Logic.False_rect_dep.
Extraction Inline Equations.Prop.Logic.True_rect_dep.
Extraction Inline Equations.Init.pr1.
Extraction Inline Equations.Init.pr2.
Extraction Inline Equations.Init.hidebody.
Extraction Inline Equations.Prop.DepElim.solution_left.

Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].
Extract Constant PCUICTyping.guard_checking => "{ fix_guard = (fun _ _ _ -> true); cofix_guard = (fun _ _ _ -> true) }".
Extract Constant PCUICSafeChecker.check_one_ind_body => "(fun _ _ _ _ _ _ _ -> ret envcheck_monad __)".

(* FIXME: commented out for now, since we use both Rocq's strings and
bytestrings from MetaRocq that leads to clashes. E.g. we cannot use
[ExtrOcamlString]. *)

(* Extract Constant timed =>
"(fun c x ->
   let time = Unix.gettimeofday() in
   let temp = x () in
   let time = (Unix.gettimeofday() -. time) in
   Feedback.msg_debug (Pp.str (Printf.sprintf ""%s executed in: %fs"" ((fun s-> (String.concat """" (List.map (String.make 1) s))) c) time));
              temp)". *)

#[local]
Set Extraction Output Directory "src".
#[warnings="-extraction-axiom-to-realize"]
Separate Extraction PluginExtract.extract
         (* The following directives ensure separate extraction does not produce name clashes *)
          Bool Nat Stdlib.Strings.String bytestring.String TypedExtraction.Common.Common TemplateMonad.Common utils ELiftSubst EGlobalEnv Common.Transform ResultMonad.

(* Definition . *)
