module SerializePAst where

import qualified Prelude
import qualified CeresS
import qualified CeresSerialize
import qualified PAst
import qualified SerializeEAst
import qualified SerializeExAst
import qualified Bytestring

coq_Serialize_typed_env :: CeresSerialize.Serialize PAst.Coq_typed_env
coq_Serialize_typed_env p =
  CeresSerialize.to_sexp SerializeExAst.coq_Serialize_global_env p

coq_Serialize_untyped_env :: CeresSerialize.Serialize PAst.Coq_untyped_env
coq_Serialize_untyped_env p =
  CeresSerialize.to_sexp SerializeEAst.coq_Serialize_global_declarations p

coq_Serialize_PAst :: CeresSerialize.Serialize PAst.PAst
coq_Serialize_PAst ast =
  case ast of {
   PAst.Untyped env t -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'U' (Bytestring.String__String 'n'
    (Bytestring.String__String 't' (Bytestring.String__String 'y'
    (Bytestring.String__String 'p' (Bytestring.String__String 'e'
    (Bytestring.String__String 'd' Bytestring.String__EmptyString)))))))))
    ((:) (CeresSerialize.to_sexp coq_Serialize_untyped_env env) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option SerializeEAst.coq_Serialize_term)
      t)
    ([]))));
   PAst.Typed env t -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'T' (Bytestring.String__String 'y'
    (Bytestring.String__String 'p' (Bytestring.String__String 'e'
    (Bytestring.String__String 'd' Bytestring.String__EmptyString))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_typed_env env) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option SerializeEAst.coq_Serialize_term)
      t)
    ([]))))}

string_of_PAst :: PAst.PAst -> Bytestring.String__Coq_t
string_of_PAst ast =
  CeresSerialize.to_string coq_Serialize_PAst ast

