module SerializePrimitives where

import qualified Prelude
import qualified CeresS
import qualified CeresSerialize
import qualified EPrimitive
import qualified PrimFloat
import qualified PrimInt63
import qualified PrimString
import qualified Primitive
import qualified Bytestring

string_of_prim_int :: PrimInt63.Coq_int -> Bytestring.String__Coq_t
string_of_prim_int = (\i -> Bytestring._String__of_string (Prelude.show i))

string_of_prim_float :: PrimFloat.Coq_float -> Bytestring.String__Coq_t
string_of_prim_float = (\s -> Prelude.error "Float serialization not implemented")

string_of_prim_string :: PrimString.Coq_string -> Bytestring.String__Coq_t
string_of_prim_string = (\f -> Bytestring._String__of_string f)

coq_Serialize_prim_tag :: CeresSerialize.Serialize Primitive.Coq_prim_tag
coq_Serialize_prim_tag t =
  case t of {
   Primitive.Coq_primInt -> CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'p' (Bytestring.String__String 'r'
    (Bytestring.String__String 'i' (Bytestring.String__String 'm'
    (Bytestring.String__String 'I' (Bytestring.String__String 'n'
    (Bytestring.String__String 't' Bytestring.String__EmptyString))))))));
   Primitive.Coq_primFloat -> CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'p' (Bytestring.String__String 'r'
    (Bytestring.String__String 'i' (Bytestring.String__String 'm'
    (Bytestring.String__String 'F' (Bytestring.String__String 'l'
    (Bytestring.String__String 'o' (Bytestring.String__String 'a'
    (Bytestring.String__String 't' Bytestring.String__EmptyString))))))))));
   Primitive.Coq_primString -> CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'p' (Bytestring.String__String 'r'
    (Bytestring.String__String 'i' (Bytestring.String__String 'm'
    (Bytestring.String__String 'S' (Bytestring.String__String 't'
    (Bytestring.String__String 'r' (Bytestring.String__String 'i'
    (Bytestring.String__String 'n' (Bytestring.String__String 'g'
    Bytestring.String__EmptyString)))))))))));
   Primitive.Coq_primArray -> CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'p' (Bytestring.String__String 'r'
    (Bytestring.String__String 'i' (Bytestring.String__String 'm'
    (Bytestring.String__String 'A' (Bytestring.String__String 'r'
    (Bytestring.String__String 'r' (Bytestring.String__String 'a'
    (Bytestring.String__String 'y' Bytestring.String__EmptyString))))))))))}

coq_Serialize_prim_int :: CeresSerialize.Serialize PrimInt63.Coq_int
coq_Serialize_prim_int i =
  CeresS.Atom_ (CeresS.Str (string_of_prim_int i))

coq_Serialize_prim_float :: CeresSerialize.Serialize PrimFloat.Coq_float
coq_Serialize_prim_float f =
  CeresS.Atom_ (CeresS.Str (string_of_prim_float f))

coq_Serialize_prim_string :: CeresSerialize.Serialize PrimString.Coq_string
coq_Serialize_prim_string s =
  CeresS.Atom_ (CeresS.Str (string_of_prim_string s))

coq_Serialize_array_model :: (CeresSerialize.Serialize a1) ->
                             CeresSerialize.Serialize
                             (EPrimitive.Coq_array_model a1)
coq_Serialize_array_model h a =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'a'
    (Bytestring.String__String 'r' (Bytestring.String__String 'r'
    (Bytestring.String__String 'a' (Bytestring.String__String 'y'
    (Bytestring.String__String '_' (Bytestring.String__String 'm'
    (Bytestring.String__String 'o' (Bytestring.String__String 'd'
    (Bytestring.String__String 'e' (Bytestring.String__String 'l'
    Bytestring.String__EmptyString))))))))))))) ((:)
    (CeresSerialize.to_sexp h (EPrimitive.array_default a)) ((:)
    (CeresSerialize.to_sexp (CeresSerialize.coq_Serialize_list h)
      (EPrimitive.array_value a))
    ([]))))

coq_Serialize_prim_val :: (CeresSerialize.Serialize a1) ->
                          CeresSerialize.Serialize
                          (EPrimitive.Coq_prim_val a1)
coq_Serialize_prim_val h p =
  let {t = EPrimitive.prim_val_tag p} in
  case EPrimitive.prim_val_model p of {
   EPrimitive.Coq_primIntModel i ->
    CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_product coq_Serialize_prim_tag
        coq_Serialize_prim_int)
      ((,) t i);
   EPrimitive.Coq_primFloatModel f ->
    CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_product coq_Serialize_prim_tag
        coq_Serialize_prim_float)
      ((,) t f);
   EPrimitive.Coq_primStringModel s ->
    CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_product coq_Serialize_prim_tag
        coq_Serialize_prim_string)
      ((,) t s);
   EPrimitive.Coq_primArrayModel a ->
    CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_product coq_Serialize_prim_tag
        (coq_Serialize_array_model h))
      ((,) t a)}

