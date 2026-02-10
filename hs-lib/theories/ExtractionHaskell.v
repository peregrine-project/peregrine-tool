From Peregrine Require SerializePrimitives.
From Peregrine Require Deserialize.
From MetaRocq.Utils Require bytestring.
From Stdlib Require Import ExtrHaskellBasic.
From Stdlib Require Import ExtrHaskellString.
From Stdlib Require PrimInt63.
From Stdlib Require PrimFloat.
From Stdlib Require PrimString.

From Stdlib Require Import Extraction.


Extraction Language Haskell.

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

Extraction Inline Equations.Init.pr1 Equations.Init.pr2.

Extraction Blacklist config List String Nat Int Ast Universes UnivSubst Typing Retyping
           OrderedType Logic Common Equality Char char uGraph
           Instances Classes Term Monad Coqlib Errors Compile Checker Eq Classes0 Numeral
           Uint63 Number Values Bytes ws_cumul_pb.


Extract Constant PrimInt63.int => "Data.Int.Int64".
Extract Constant SerializePrimitives.string_of_prim_int =>
  "(\i -> Bytestring._String__of_string (Prelude.show i))".

Extract Constant PrimFloat.float => "Prelude.Double".
(* TODO *)
Extract Constant SerializePrimitives.string_of_prim_float =>
  "(\s -> Prelude.error ""Float serialization not implemented"")".

Extract Constant PrimString.string => "Prelude.String".
Extract Constant SerializePrimitives.string_of_prim_string =>
  "(\f -> Bytestring._String__of_string f)".  


Set Warnings "-extraction-reserved-identifier".
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-logical-axiom".
Set Extraction Output Directory "extraction/".


Separate Extraction Deserialize.string_of_PAst Deserialize.string_of_config
                    Deserialize.string_of_backend_config Deserialize.string_of_erasure_phases
                    Deserialize.string_of_attributes_config
                    bytestring.String.of_string bytestring.String.to_string.
