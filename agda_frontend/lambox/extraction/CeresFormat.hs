module CeresFormat where

import qualified Prelude
import qualified CeresS
import qualified CeresString
import qualified List0
import qualified Bytestring

dstring_of_sexp :: (a1 -> CeresString.DString__Coq_t) -> (CeresS.Coq_sexp_
                   a1) -> CeresString.DString__Coq_t
dstring_of_sexp dstring_A x =
  case x of {
   CeresS.Atom_ a -> dstring_A a;
   CeresS.List xs0 ->
    case xs0 of {
     ([]) ->
      CeresString._DString__of_string (Bytestring.String__String '('
        (Bytestring.String__String ')' Bytestring.String__EmptyString));
     (:) x0 xs -> (\s0 -> Bytestring.String__String '('
      (dstring_of_sexp dstring_A x0
        (List0.fold_right (\x1 s ->
          CeresString._DString__app_string
            (CeresString._DString__of_byte ' ')
            (CeresString._DString__app_string (dstring_of_sexp dstring_A x1)
              s))
          (Bytestring.String__String ')' s0) xs)))}}

string_of_sexp_ :: (a1 -> Bytestring.String__Coq_t) -> (CeresS.Coq_sexp_ 
                   a1) -> Bytestring.String__Coq_t
string_of_sexp_ string_A x =
  dstring_of_sexp (\x0 -> CeresString._DString__of_string (string_A x0)) x
    Bytestring.String__EmptyString

string_of_atom :: CeresS.Coq_atom -> Bytestring.String__Coq_t
string_of_atom a =
  case a of {
   CeresS.Num n -> CeresString.string_of_Z n;
   CeresS.Str s -> CeresString.escape_string s;
   CeresS.Raw s -> s}

string_of_sexp :: (CeresS.Coq_sexp_ CeresS.Coq_atom) ->
                  Bytestring.String__Coq_t
string_of_sexp =
  string_of_sexp_ string_of_atom

