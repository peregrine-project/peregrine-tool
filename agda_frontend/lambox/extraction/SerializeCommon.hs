module SerializeCommon where

import qualified Prelude
import qualified BasicAst
import qualified CeresS
import qualified CeresSerialize
import qualified Kernames
import qualified Universes0
import qualified Bytestring

coq_Serialize_ident :: CeresSerialize.Serialize Kernames.Coq_ident
coq_Serialize_ident i =
  CeresS.Atom_ (CeresS.Str i)

coq_Serialize_dirpath :: CeresSerialize.Serialize Kernames.Coq_dirpath
coq_Serialize_dirpath d =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_list coq_Serialize_ident) d

coq_Serialize_modpath :: CeresSerialize.Serialize Kernames.Coq_modpath
coq_Serialize_modpath m =
  case m of {
   Kernames.MPfile dp -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'M' (Bytestring.String__String 'P'
    (Bytestring.String__String 'f' (Bytestring.String__String 'i'
    (Bytestring.String__String 'l' (Bytestring.String__String 'e'
    Bytestring.String__EmptyString)))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_dirpath dp) ([])));
   Kernames.MPbound dp id i -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'M' (Bytestring.String__String 'P'
    (Bytestring.String__String 'b' (Bytestring.String__String 'o'
    (Bytestring.String__String 'u' (Bytestring.String__String 'n'
    (Bytestring.String__String 'd' Bytestring.String__EmptyString)))))))))
    ((:) (CeresSerialize.to_sexp coq_Serialize_dirpath dp) ((:)
    (CeresSerialize.to_sexp coq_Serialize_ident id) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      i)
    ([])))));
   Kernames.MPdot mp id -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'M' (Bytestring.String__String 'P'
    (Bytestring.String__String 'd' (Bytestring.String__String 'o'
    (Bytestring.String__String 't' Bytestring.String__EmptyString))))))) ((:)
    (coq_Serialize_modpath mp) ((:)
    (CeresSerialize.to_sexp coq_Serialize_ident id) ([]))))}

coq_Serialize_kername :: CeresSerialize.Serialize Kernames.Coq_kername
coq_Serialize_kername kn =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_product coq_Serialize_modpath
      coq_Serialize_ident)
    kn

coq_Serialize_inductive :: CeresSerialize.Serialize Kernames.Coq_inductive
coq_Serialize_inductive i =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'i'
    (Bytestring.String__String 'n' (Bytestring.String__String 'd'
    (Bytestring.String__String 'u' (Bytestring.String__String 'c'
    (Bytestring.String__String 't' (Bytestring.String__String 'i'
    (Bytestring.String__String 'v' (Bytestring.String__String 'e'
    Bytestring.String__EmptyString))))))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_kername
      (Kernames.inductive_mind i))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      (Kernames.inductive_ind i))
    ([]))))

coq_Serialize_projection :: CeresSerialize.Serialize Kernames.Coq_projection
coq_Serialize_projection p =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'p'
    (Bytestring.String__String 'r' (Bytestring.String__String 'o'
    (Bytestring.String__String 'j' (Bytestring.String__String 'e'
    (Bytestring.String__String 'c' (Bytestring.String__String 't'
    (Bytestring.String__String 'i' (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' Bytestring.String__EmptyString))))))))))))
    ((:)
    (CeresSerialize.to_sexp coq_Serialize_inductive (Kernames.proj_ind p))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      (Kernames.proj_npars p))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      (Kernames.proj_arg p))
    ([])))))

coq_Serialize_name :: CeresSerialize.Serialize BasicAst.Coq_name
coq_Serialize_name n =
  case n of {
   BasicAst.Coq_nAnon -> CeresS.Atom_ (CeresS.Raw (Bytestring.String__String
    'n' (Bytestring.String__String 'A' (Bytestring.String__String 'n'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    Bytestring.String__EmptyString))))));
   BasicAst.Coq_nNamed i -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'n' (Bytestring.String__String 'N'
    (Bytestring.String__String 'a' (Bytestring.String__String 'm'
    (Bytestring.String__String 'e' (Bytestring.String__String 'd'
    Bytestring.String__EmptyString)))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_ident i) ([])))}

coq_Serialize_recursivity_kind :: CeresSerialize.Serialize
                                  BasicAst.Coq_recursivity_kind
coq_Serialize_recursivity_kind x =
  case x of {
   BasicAst.Finite -> CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'F'
    (Bytestring.String__String 'i' (Bytestring.String__String 'n'
    (Bytestring.String__String 'i' (Bytestring.String__String 't'
    (Bytestring.String__String 'e' Bytestring.String__EmptyString)))))));
   BasicAst.CoFinite -> CeresS.Atom_ (CeresS.Raw (Bytestring.String__String
    'C' (Bytestring.String__String 'o' (Bytestring.String__String 'F'
    (Bytestring.String__String 'i' (Bytestring.String__String 'n'
    (Bytestring.String__String 'i' (Bytestring.String__String 't'
    (Bytestring.String__String 'e' Bytestring.String__EmptyString)))))))));
   BasicAst.BiFinite -> CeresS.Atom_ (CeresS.Raw (Bytestring.String__String
    'B' (Bytestring.String__String 'i' (Bytestring.String__String 'F'
    (Bytestring.String__String 'i' (Bytestring.String__String 'n'
    (Bytestring.String__String 'i' (Bytestring.String__String 't'
    (Bytestring.String__String 'e' Bytestring.String__EmptyString)))))))))}

coq_Serialize_allowed_eliminations :: CeresSerialize.Serialize
                                      Universes0.Coq_allowed_eliminations
coq_Serialize_allowed_eliminations x =
  case x of {
   Universes0.IntoSProp -> CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'I' (Bytestring.String__String 'n'
    (Bytestring.String__String 't' (Bytestring.String__String 'o'
    (Bytestring.String__String 'S' (Bytestring.String__String 'P'
    (Bytestring.String__String 'r' (Bytestring.String__String 'o'
    (Bytestring.String__String 'p' Bytestring.String__EmptyString))))))))));
   Universes0.IntoPropSProp -> CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'I' (Bytestring.String__String 'n'
    (Bytestring.String__String 't' (Bytestring.String__String 'o'
    (Bytestring.String__String 'P' (Bytestring.String__String 'r'
    (Bytestring.String__String 'o' (Bytestring.String__String 'p'
    (Bytestring.String__String 'S' (Bytestring.String__String 'P'
    (Bytestring.String__String 'r' (Bytestring.String__String 'o'
    (Bytestring.String__String 'p'
    Bytestring.String__EmptyString))))))))))))));
   Universes0.IntoSetPropSProp -> CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'I' (Bytestring.String__String 'n'
    (Bytestring.String__String 't' (Bytestring.String__String 'o'
    (Bytestring.String__String 'S' (Bytestring.String__String 'e'
    (Bytestring.String__String 't' (Bytestring.String__String 'P'
    (Bytestring.String__String 'r' (Bytestring.String__String 'o'
    (Bytestring.String__String 'p' (Bytestring.String__String 'S'
    (Bytestring.String__String 'P' (Bytestring.String__String 'r'
    (Bytestring.String__String 'o' (Bytestring.String__String 'p'
    Bytestring.String__EmptyString)))))))))))))))));
   Universes0.IntoAny -> CeresS.Atom_ (CeresS.Raw (Bytestring.String__String
    'I' (Bytestring.String__String 'n' (Bytestring.String__String 't'
    (Bytestring.String__String 'o' (Bytestring.String__String 'A'
    (Bytestring.String__String 'n' (Bytestring.String__String 'y'
    Bytestring.String__EmptyString))))))))}

