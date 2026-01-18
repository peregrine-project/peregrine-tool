From MetaRocq.Erasure Require EAst.
From Peregrine Require CheckWf.
From Peregrine Require EvalBox.
From Peregrine Require ErasurePipeline.
Local Unset Universe Checking. (* TODO: fix universe inconsistency *)
From Peregrine Require Translations.
Local Set Universe Checking.
From Peregrine Require SerializePrimitives.
From Peregrine Require Serialize.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOCamlFloats.
From Stdlib Require Import ExtrOCamlInt63.
From Stdlib Require Import ExtrOCamlPString.
(* From Stdlib Require Import ExtrOcamlNativeString. *)
From Stdlib Require Import Extraction.



Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

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
Extract Constant Equations.Init.pr1 => "fst".
Extract Constant Equations.Init.pr2 => "snd".
Extraction Inline Equations.Init.pr1 Equations.Init.pr2.

Extraction Blacklist config List String Nat Int Ast Universes UnivSubst Typing Retyping
           OrderedType Logic Common Equality Char char uGraph
           Instances Classes Term Monad Coqlib Errors Compile Checker Eq Classes0 Numeral
           Uint63 Number Values Bytes ws_cumul_pb.


(* TODO: add time implementation if *)
Extract Constant MetaRocq.Common.Transform.time =>
  "(fun c f x -> f x)".

(* TODO: validate prim int implementations *)
Extract Constant SerializePrimitives.string_of_prim_int =>
  "(fun i -> i |> Uint63.to_int64 |> Int64.to_string |> Caml_bytestring.bytestring_of_caml_string)".
Extract Constant SerializePrimitives.prim_int_of_string =>
  "(fun s -> s |> Caml_bytestring.caml_string_of_bytestring |> Int64.of_string |> Uint63.of_int64)".
  (* "(fun s -> failwith "" "")". *)

(* TODO: validate prim float implementations *)
Extract Constant SerializePrimitives.string_of_prim_float =>
  "(fun f -> f |> Float64.to_float |> Int64.bits_of_float |> Int64.to_string |> Caml_bytestring.bytestring_of_caml_string)".
  (* "(fun s -> failwith "" "")". *)
Extract Constant SerializePrimitives.prim_float_of_string =>
  "(fun s -> s |> Caml_bytestring.caml_string_of_bytestring |> Int64.of_string |> Int64.float_of_bits |> Float64.of_float)".
  (* "(fun s -> failwith "" "")". *)

(* TODO: validate prim string implementations *)
Extract Constant SerializePrimitives.string_of_prim_string =>
  "(fun f -> f |> Pstring.to_string |> Caml_bytestring.bytestring_of_caml_string)".
  (* "(fun s -> failwith "" "")". *)
Extract Constant SerializePrimitives.prim_string_of_string =>
  "(fun s -> s |> Caml_bytestring.caml_string_of_bytestring |> Pstring.of_string |> Option.get)".
  (* "(fun s -> failwith "" "")". *)


Extract Constant Malfunction.FFI.coq_msg_info => "(fun s -> ())".
Extract Constant Malfunction.FFI.coq_user_error => "(fun s -> ())".
Extraction Inline Malfunction.FFI.coq_msg_info.
Extraction Inline Malfunction.FFI.coq_user_error.


Set Warnings "-extraction-reserved-identifier".
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-logical-axiom".
Set Extraction Output Directory "src/extraction/".

Require compcert.cfrontend.Csyntax
        compcert.cfrontend.Clight.

Separate Extraction Translations.l_box_to_wasm CertiCoqPipeline.show_IR CertiCoqPipeline.make_opts
                    Translations.l_box_to_rust LambdaBoxToRust.default_remaps LambdaBoxToRust.default_attrs LambdaBoxToRust.mk_preamble
                    Translations.l_box_to_elm LambdaBoxToElm.default_remaps LambdaBoxToElm.mk_preamble
                    Translations.l_box_to_c
                    Translations.l_box_to_ocaml
                    TypedTransforms.mk_params ErasurePipeline.implement_box
                    EvalBox.eval
                    CheckWf.check_wf_program CheckWf.CheckWfExAst.check_wf_typed_program CheckWf.agda_eflags CheckWf.agda_typed_eflags
                    Serialize.program_of_string Serialize.global_env_of_string Serialize.kername_of_string Serialize.string_of_error
                    Floats.Float32.to_bits Floats.Float.to_bits
                    Floats.Float32.of_bits Floats.Float.of_bits
                    Csyntax
                    Clight
                    String.length.
