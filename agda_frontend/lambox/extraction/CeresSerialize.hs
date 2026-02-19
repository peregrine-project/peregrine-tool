module CeresSerialize where

import qualified Prelude
import qualified BinInt
import qualified BinNums
import qualified CeresFormat
import qualified CeresS
import qualified CeresString
import qualified Datatypes
import qualified ListDef
import qualified Bytestring

type Serialize a = a -> CeresS.Coq_sexp_ CeresS.Coq_atom

to_sexp :: (Serialize a1) -> a1 -> CeresS.Coq_sexp_ CeresS.Coq_atom
to_sexp serialize =
  serialize

to_string :: (Serialize a1) -> a1 -> Bytestring.String__Coq_t
to_string h a =
  CeresFormat.string_of_sexp (to_sexp h a)

type Integral a = a -> BinNums.Z

to_Z :: (Integral a1) -> a1 -> BinNums.Z
to_Z integral =
  integral

coq_Serialize_Integral :: (Integral a1) -> Serialize a1
coq_Serialize_Integral h z =
  CeresS.Atom_ (CeresS.Num (to_Z h z))

coq_Integral_nat :: Integral Datatypes.Coq_nat
coq_Integral_nat =
  BinInt._Z__of_nat

coq_Serialize_bool :: Serialize Prelude.Bool
coq_Serialize_bool b =
  CeresS.Atom_ (CeresS.Raw (CeresString.string_of_bool b))

coq_Serialize_option :: (Serialize a1) -> Serialize (Prelude.Maybe a1)
coq_Serialize_option h oa =
  case oa of {
   Prelude.Just a -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'S' (Bytestring.String__String 'o'
    (Bytestring.String__String 'm' (Bytestring.String__String 'e'
    Bytestring.String__EmptyString)))))) ((:) (to_sexp h a) ([])));
   Prelude.Nothing -> CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'N'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    (Bytestring.String__String 'e' Bytestring.String__EmptyString)))))}

coq_Serialize_product :: (Serialize a1) -> (Serialize a2) -> Serialize
                         ((,) a1 a2)
coq_Serialize_product h h0 ab =
  CeresS.List ((:) (to_sexp h (Datatypes.fst ab)) ((:)
    (to_sexp h0 (Datatypes.snd ab)) ([])))

coq_Serialize_unit :: Serialize ()
coq_Serialize_unit _ =
  CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 't'
    (Bytestring.String__String 't' Bytestring.String__EmptyString)))

coq_Serialize_list :: (Serialize a1) -> Serialize (([]) a1)
coq_Serialize_list h xs =
  CeresS.List (ListDef.map (to_sexp h) xs)

