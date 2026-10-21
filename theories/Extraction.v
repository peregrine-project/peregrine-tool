From MetaRocq.Erasure Require EAst.
From Peregrine Require Pipeline.
From Peregrine Require ConfigUtils.
From Peregrine Require RustGMPRemaps.
From Peregrine Require RustNativeRemaps.
From Peregrine Require RustMixedRemaps.
From Peregrine Require SerializePrimitives.
From Peregrine Require DeserializePrimitives.
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

Extract Constant SerializePrimitives.string_of_prim_string =>
  "(fun f -> f |> Pstring.to_string |> Caml_bytestring.bytestring_of_caml_string)".
  (* "(fun s -> failwith "" "")". *)
Extract Constant DeserializePrimitives.prim_string_of_string =>
  "(fun s -> s |> Caml_bytestring.caml_string_of_bytestring |> Pstring.of_string |> Option.get)".
  (* "(fun s -> failwith "" "")". *)


Extract Constant Malfunction.FFI.coq_msg_info => "(fun s -> s |> Caml_bytestring.caml_string_of_bytestring |> Stdlib.print_endline)".
Extract Constant Malfunction.FFI.coq_user_error => "(fun s -> s |> Caml_bytestring.caml_string_of_bytestring |> Stdlib.print_endline)".
Extraction Inline Malfunction.FFI.coq_msg_info.
Extraction Inline Malfunction.FFI.coq_user_error.
Extract Constant CakeML.Backend.FFI.coq_msg_info => "(fun s -> s |> Caml_bytestring.caml_string_of_bytestring |> Stdlib.print_endline)".
Extract Constant CakeML.Backend.FFI.coq_user_error => "(fun s -> s |> Caml_bytestring.caml_string_of_bytestring |> Stdlib.print_endline)".
Extraction Inline CakeML.Backend.FFI.coq_msg_info.
Extraction Inline CakeML.Backend.FFI.coq_user_error.


(* Tail-recursive realisations of functions the printers apply to very long
   inputs: extracted as is, they recurse once per element and overflow the
   default 8 MiB stack (benchmarks UPSTREAM_ISSUES entry 13). On OCaml 4.14
   List.map is not tail-recursive either, hence rev_map. *)
From MetaRocq.Utils Require bytestring.
From Stdlib Require List.
Extract Constant Corelib.Lists.ListDef.map =>
  "(fun f l -> List.rev (List.rev_map f l))".
Extract Constant Stdlib.Lists.List.concat =>
  "(fun ls -> List.rev (List.fold_left (fun acc l -> List.rev_append l acc) [] ls))".
(* seq lives in mathcomp.ssreflect up to mathcomp 2.4 and in mathcomp.boot
   from 2.5 on (the Nix CI), so name it by its short path *)
From mathcomp Require seq.
Extract Constant seq.cat =>
  "(fun s1 s2 -> List.rev_append (List.rev s1) s2)".
Extract Constant Corelib.Init.Datatypes.length =>
  "(fun l -> let rec go n = function [] -> n | _ :: l -> go (S n) l in go O l)".
Extract Constant MetaRocq.Utils.bytestring.String.append =>
  "(fun x y ->
     let rec rev acc = function EmptyString -> acc | String (c, s) -> rev (c :: acc) s in
     List.fold_left (fun s c -> String (c, s)) y (rev [] x))".
Extract Constant MetaRocq.Utils.bytestring.String.parse =>
  "(fun l -> List.fold_left (fun s c -> String (c, s)) EmptyString (List.rev l))".
Extract Constant MetaRocq.Utils.bytestring.String.print =>
  "(fun s -> let rec go acc = function EmptyString -> List.rev acc | String (c, s) -> go (c :: acc) s in go [] s)".

Set Warnings "-extraction-reserved-identifier".
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-logical-axiom".
Set Extraction Output Directory "src/extraction/".

Require compcert.cfrontend.Csyntax
        compcert.cfrontend.Clight.

Separate Extraction Pipeline.peregrine_pipeline Pipeline.peregrine_validate
                    ConfigUtils.empty_rust_config' ConfigUtils.empty_elm_config' ConfigUtils.empty_certirocq_config'
                    ConfigUtils.empty_ocaml_config' ConfigUtils.empty_cakeml_config' ConfigUtils.empty_lean_config'
                    ConfigUtils.empty_config'
                    RustGMPRemaps.gmp_const_remaps RustGMPRemaps.gmp_ind_remaps RustGMPRemaps.gmp_rust_config'
                    RustNativeRemaps.native_const_remaps RustNativeRemaps.native_ind_remaps RustNativeRemaps.native_rust_config'
                    RustMixedRemaps.mixed_const_remaps RustMixedRemaps.mixed_const_remaps2 RustMixedRemaps.mixed_ind_remaps RustMixedRemaps.mixed_rust_config'
                    Floats.Float32.to_bits Floats.Float.to_bits
                    Floats.Float32.of_bits Floats.Float.of_bits
                    Csyntax
                    Clight
                    String.length.
