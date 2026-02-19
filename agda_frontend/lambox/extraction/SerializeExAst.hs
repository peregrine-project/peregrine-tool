module SerializeExAst where

import qualified Prelude
import qualified CeresS
import qualified CeresSerialize
import qualified ExAst
import qualified SerializeCommon
import qualified SerializeEAst
import qualified Bytestring

coq_Serialize_box_type :: CeresSerialize.Serialize ExAst.Coq_box_type
coq_Serialize_box_type bt =
  case bt of {
   ExAst.TBox -> CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'T'
    (Bytestring.String__String 'B' (Bytestring.String__String 'o'
    (Bytestring.String__String 'x' Bytestring.String__EmptyString)))));
   ExAst.TAny -> CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'T'
    (Bytestring.String__String 'A' (Bytestring.String__String 'n'
    (Bytestring.String__String 'y' Bytestring.String__EmptyString)))));
   ExAst.TArr dom codom -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'T' (Bytestring.String__String 'A'
    (Bytestring.String__String 'r' (Bytestring.String__String 'r'
    Bytestring.String__EmptyString)))))) ((:) (coq_Serialize_box_type dom)
    ((:) (coq_Serialize_box_type codom) ([]))));
   ExAst.TApp u v -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'T' (Bytestring.String__String 'A'
    (Bytestring.String__String 'p' (Bytestring.String__String 'p'
    Bytestring.String__EmptyString)))))) ((:) (coq_Serialize_box_type u) ((:)
    (coq_Serialize_box_type v) ([]))));
   ExAst.TVar i -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'T' (Bytestring.String__String 'V'
    (Bytestring.String__String 'a' (Bytestring.String__String 'r'
    Bytestring.String__EmptyString)))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      i)
    ([])));
   ExAst.TInd ind -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'T' (Bytestring.String__String 'I'
    (Bytestring.String__String 'n' (Bytestring.String__String 'd'
    Bytestring.String__EmptyString)))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_inductive ind)
    ([])));
   ExAst.TConst k -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'T' (Bytestring.String__String 'C'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    (Bytestring.String__String 's' (Bytestring.String__String 't'
    Bytestring.String__EmptyString)))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_kername k) ([])))}

coq_Serialize_type_var_info :: CeresSerialize.Serialize
                               ExAst.Coq_type_var_info
coq_Serialize_type_var_info tv =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 't'
    (Bytestring.String__String 'y' (Bytestring.String__String 'p'
    (Bytestring.String__String 'e' (Bytestring.String__String '_'
    (Bytestring.String__String 'v' (Bytestring.String__String 'a'
    (Bytestring.String__String 'r' (Bytestring.String__String '_'
    (Bytestring.String__String 'i' (Bytestring.String__String 'n'
    (Bytestring.String__String 'f' (Bytestring.String__String 'o'
    Bytestring.String__EmptyString))))))))))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_name
      (ExAst.tvar_name tv))
    ((:)
    (CeresSerialize.to_sexp CeresSerialize.coq_Serialize_bool
      (ExAst.tvar_is_logical tv))
    ((:)
    (CeresSerialize.to_sexp CeresSerialize.coq_Serialize_bool
      (ExAst.tvar_is_arity tv))
    ((:)
    (CeresSerialize.to_sexp CeresSerialize.coq_Serialize_bool
      (ExAst.tvar_is_sort tv))
    ([]))))))

coq_Serialize_constant_body :: CeresSerialize.Serialize
                               ExAst.Coq_constant_body
coq_Serialize_constant_body cb =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'c'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    (Bytestring.String__String 's' (Bytestring.String__String 't'
    (Bytestring.String__String 'a' (Bytestring.String__String 'n'
    (Bytestring.String__String 't' (Bytestring.String__String '_'
    (Bytestring.String__String 'b' (Bytestring.String__String 'o'
    (Bytestring.String__String 'd' (Bytestring.String__String 'y'
    Bytestring.String__EmptyString))))))))))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_product
        (CeresSerialize.coq_Serialize_list
          SerializeCommon.coq_Serialize_name)
        coq_Serialize_box_type)
      (ExAst.cst_type cb))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option SerializeEAst.coq_Serialize_term)
      (ExAst.cst_body cb))
    ([]))))

coq_Serialize_one_inductive_body :: CeresSerialize.Serialize
                                    ExAst.Coq_one_inductive_body
coq_Serialize_one_inductive_body oib =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' (Bytestring.String__String 'e'
    (Bytestring.String__String '_' (Bytestring.String__String 'i'
    (Bytestring.String__String 'n' (Bytestring.String__String 'd'
    (Bytestring.String__String 'u' (Bytestring.String__String 'c'
    (Bytestring.String__String 't' (Bytestring.String__String 'i'
    (Bytestring.String__String 'v' (Bytestring.String__String 'e'
    (Bytestring.String__String '_' (Bytestring.String__String 'b'
    (Bytestring.String__String 'o' (Bytestring.String__String 'd'
    (Bytestring.String__String 'y'
    Bytestring.String__EmptyString)))))))))))))))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_ident
      (ExAst.ind_name oib))
    ((:)
    (CeresSerialize.to_sexp CeresSerialize.coq_Serialize_bool
      (ExAst.ind_propositional oib))
    ((:)
    (CeresSerialize.to_sexp
      SerializeCommon.coq_Serialize_allowed_eliminations
      (ExAst.ind_kelim oib))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list coq_Serialize_type_var_info)
      (ExAst.ind_type_vars oib))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list
        (CeresSerialize.coq_Serialize_product
          (CeresSerialize.coq_Serialize_product
            SerializeCommon.coq_Serialize_ident
            (CeresSerialize.coq_Serialize_list
              (CeresSerialize.coq_Serialize_product
                SerializeCommon.coq_Serialize_name coq_Serialize_box_type)))
          (CeresSerialize.coq_Serialize_Integral
            CeresSerialize.coq_Integral_nat)))
      (ExAst.ind_ctors oib))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list
        (CeresSerialize.coq_Serialize_product
          SerializeCommon.coq_Serialize_ident coq_Serialize_box_type))
      (ExAst.ind_projs oib))
    ([]))))))))

coq_Serialize_mutual_inductive_body :: CeresSerialize.Serialize
                                       ExAst.Coq_mutual_inductive_body
coq_Serialize_mutual_inductive_body mib =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'm'
    (Bytestring.String__String 'u' (Bytestring.String__String 't'
    (Bytestring.String__String 'u' (Bytestring.String__String 'a'
    (Bytestring.String__String 'l' (Bytestring.String__String '_'
    (Bytestring.String__String 'i' (Bytestring.String__String 'n'
    (Bytestring.String__String 'd' (Bytestring.String__String 'u'
    (Bytestring.String__String 'c' (Bytestring.String__String 't'
    (Bytestring.String__String 'i' (Bytestring.String__String 'v'
    (Bytestring.String__String 'e' (Bytestring.String__String '_'
    (Bytestring.String__String 'b' (Bytestring.String__String 'o'
    (Bytestring.String__String 'd' (Bytestring.String__String 'y'
    Bytestring.String__EmptyString))))))))))))))))))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_recursivity_kind
      (ExAst.ind_finite mib))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      (ExAst.ind_npars mib))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list coq_Serialize_one_inductive_body)
      (ExAst.ind_bodies mib))
    ([])))))

coq_Serialize_global_decl :: CeresSerialize.Serialize ExAst.Coq_global_decl
coq_Serialize_global_decl gd =
  case gd of {
   ExAst.ConstantDecl cb -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'C' (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' (Bytestring.String__String 's'
    (Bytestring.String__String 't' (Bytestring.String__String 'a'
    (Bytestring.String__String 'n' (Bytestring.String__String 't'
    (Bytestring.String__String 'D' (Bytestring.String__String 'e'
    (Bytestring.String__String 'c' (Bytestring.String__String 'l'
    Bytestring.String__EmptyString)))))))))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_constant_body cb) ([])));
   ExAst.InductiveDecl mib -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'I' (Bytestring.String__String 'n'
    (Bytestring.String__String 'd' (Bytestring.String__String 'u'
    (Bytestring.String__String 'c' (Bytestring.String__String 't'
    (Bytestring.String__String 'i' (Bytestring.String__String 'v'
    (Bytestring.String__String 'e' (Bytestring.String__String 'D'
    (Bytestring.String__String 'e' (Bytestring.String__String 'c'
    (Bytestring.String__String 'l'
    Bytestring.String__EmptyString))))))))))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_mutual_inductive_body mib) ([])));
   ExAst.TypeAliasDecl o -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'T' (Bytestring.String__String 'y'
    (Bytestring.String__String 'p' (Bytestring.String__String 'e'
    (Bytestring.String__String 'A' (Bytestring.String__String 'l'
    (Bytestring.String__String 'i' (Bytestring.String__String 'a'
    (Bytestring.String__String 's' (Bytestring.String__String 'D'
    (Bytestring.String__String 'e' (Bytestring.String__String 'c'
    (Bytestring.String__String 'l'
    Bytestring.String__EmptyString))))))))))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        (CeresSerialize.coq_Serialize_product
          (CeresSerialize.coq_Serialize_list coq_Serialize_type_var_info)
          coq_Serialize_box_type))
      o)
    ([])))}

coq_Serialize_global_env :: CeresSerialize.Serialize ExAst.Coq_global_env
coq_Serialize_global_env env =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_list
      (CeresSerialize.coq_Serialize_product
        (CeresSerialize.coq_Serialize_product
          SerializeCommon.coq_Serialize_kername
          CeresSerialize.coq_Serialize_bool)
        coq_Serialize_global_decl))
    env

