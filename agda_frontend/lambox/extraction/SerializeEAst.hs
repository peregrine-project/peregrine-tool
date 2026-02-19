module SerializeEAst where

import qualified Prelude
import qualified CeresS
import qualified CeresSerialize
import qualified EAst
import qualified ListDef
import qualified SerializeCommon
import qualified SerializePrimitives
import qualified Bytestring

coq_Serialize_def :: (CeresSerialize.Serialize a1) ->
                     CeresSerialize.Serialize (EAst.Coq_def a1)
coq_Serialize_def h d =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'd'
    (Bytestring.String__String 'e' (Bytestring.String__String 'f'
    Bytestring.String__EmptyString))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_name
      (EAst.dname d))
    ((:) (CeresSerialize.to_sexp h (EAst.dbody d)) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      (EAst.rarg d))
    ([])))))

coq_Serialize_mfixpoint :: (CeresSerialize.Serialize a1) ->
                           CeresSerialize.Serialize (EAst.Coq_mfixpoint a1)
coq_Serialize_mfixpoint h f =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_list (coq_Serialize_def h)) f

coq_Serialize_term :: CeresSerialize.Serialize EAst.Coq_term
coq_Serialize_term t =
  case t of {
   EAst.Coq_tBox -> CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 't'
    (Bytestring.String__String 'B' (Bytestring.String__String 'o'
    (Bytestring.String__String 'x' Bytestring.String__EmptyString)))));
   EAst.Coq_tRel n -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'R'
    (Bytestring.String__String 'e' (Bytestring.String__String 'l'
    Bytestring.String__EmptyString)))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      n)
    ([])));
   EAst.Coq_tVar i -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'V'
    (Bytestring.String__String 'a' (Bytestring.String__String 'r'
    Bytestring.String__EmptyString)))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_ident i) ([])));
   EAst.Coq_tEvar n l -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'E'
    (Bytestring.String__String 'v' (Bytestring.String__String 'a'
    (Bytestring.String__String 'r' Bytestring.String__EmptyString))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      n)
    ((:) (CeresS.List (ListDef.map coq_Serialize_term l)) ([]))));
   EAst.Coq_tLambda na t0 -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'L'
    (Bytestring.String__String 'a' (Bytestring.String__String 'm'
    (Bytestring.String__String 'b' (Bytestring.String__String 'd'
    (Bytestring.String__String 'a' Bytestring.String__EmptyString)))))))))
    ((:) (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_name na) ((:)
    (coq_Serialize_term t0) ([]))));
   EAst.Coq_tLetIn na b t0 -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'L'
    (Bytestring.String__String 'e' (Bytestring.String__String 't'
    (Bytestring.String__String 'I' (Bytestring.String__String 'n'
    Bytestring.String__EmptyString)))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_name na) ((:)
    (coq_Serialize_term b) ((:) (coq_Serialize_term t0) ([])))));
   EAst.Coq_tApp u v -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'A'
    (Bytestring.String__String 'p' (Bytestring.String__String 'p'
    Bytestring.String__EmptyString)))))) ((:) (coq_Serialize_term u) ((:)
    (coq_Serialize_term v) ([]))));
   EAst.Coq_tConst k -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'C'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    (Bytestring.String__String 's' (Bytestring.String__String 't'
    Bytestring.String__EmptyString)))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_kername k) ([])));
   EAst.Coq_tConstruct ind n args -> CeresS.List ((:) (CeresS.Atom_
    (CeresS.Raw (Bytestring.String__String 't' (Bytestring.String__String 'C'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    (Bytestring.String__String 's' (Bytestring.String__String 't'
    (Bytestring.String__String 'r' (Bytestring.String__String 'u'
    (Bytestring.String__String 'c' (Bytestring.String__String 't'
    Bytestring.String__EmptyString)))))))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_inductive ind) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      n)
    ((:) (CeresS.List (ListDef.map coq_Serialize_term args)) ([])))));
   EAst.Coq_tCase indn c brs -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'C'
    (Bytestring.String__String 'a' (Bytestring.String__String 's'
    (Bytestring.String__String 'e' Bytestring.String__EmptyString))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_product
        SerializeCommon.coq_Serialize_inductive
        (CeresSerialize.coq_Serialize_Integral
          CeresSerialize.coq_Integral_nat))
      indn)
    ((:) (coq_Serialize_term c) ((:) (CeresS.List
    (ListDef.map
      (CeresSerialize.to_sexp
        (CeresSerialize.coq_Serialize_product
          (CeresSerialize.coq_Serialize_list
            SerializeCommon.coq_Serialize_name)
          coq_Serialize_term))
      brs))
    ([])))));
   EAst.Coq_tProj p c -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'P'
    (Bytestring.String__String 'r' (Bytestring.String__String 'o'
    (Bytestring.String__String 'j' Bytestring.String__EmptyString))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_projection p) ((:)
    (coq_Serialize_term c) ([]))));
   EAst.Coq_tFix mfix idx -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'F'
    (Bytestring.String__String 'i' (Bytestring.String__String 'x'
    Bytestring.String__EmptyString)))))) ((:)
    (CeresSerialize.to_sexp (coq_Serialize_mfixpoint coq_Serialize_term)
      mfix)
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      idx)
    ([]))));
   EAst.Coq_tCoFix mfix idx -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'C'
    (Bytestring.String__String 'o' (Bytestring.String__String 'F'
    (Bytestring.String__String 'i' (Bytestring.String__String 'x'
    Bytestring.String__EmptyString)))))))) ((:)
    (CeresSerialize.to_sexp (coq_Serialize_mfixpoint coq_Serialize_term)
      mfix)
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      idx)
    ([]))));
   EAst.Coq_tPrim prim -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'P'
    (Bytestring.String__String 'r' (Bytestring.String__String 'i'
    (Bytestring.String__String 'm' Bytestring.String__EmptyString))))))) ((:)
    (CeresSerialize.to_sexp
      (SerializePrimitives.coq_Serialize_prim_val coq_Serialize_term) prim)
    ([])));
   EAst.Coq_tLazy t0 -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'L'
    (Bytestring.String__String 'a' (Bytestring.String__String 'z'
    (Bytestring.String__String 'y' Bytestring.String__EmptyString))))))) ((:)
    (coq_Serialize_term t0) ([])));
   EAst.Coq_tForce t0 -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 't' (Bytestring.String__String 'F'
    (Bytestring.String__String 'o' (Bytestring.String__String 'r'
    (Bytestring.String__String 'c' (Bytestring.String__String 'e'
    Bytestring.String__EmptyString)))))))) ((:) (coq_Serialize_term t0)
    ([])))}

coq_Serialize_constructor_body :: CeresSerialize.Serialize
                                  EAst.Coq_constructor_body
coq_Serialize_constructor_body cb =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'c'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    (Bytestring.String__String 's' (Bytestring.String__String 't'
    (Bytestring.String__String 'r' (Bytestring.String__String 'u'
    (Bytestring.String__String 'c' (Bytestring.String__String 't'
    (Bytestring.String__String 'o' (Bytestring.String__String 'r'
    (Bytestring.String__String '_' (Bytestring.String__String 'b'
    (Bytestring.String__String 'o' (Bytestring.String__String 'd'
    (Bytestring.String__String 'y'
    Bytestring.String__EmptyString)))))))))))))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_ident
      (EAst.cstr_name cb))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      (EAst.cstr_nargs cb))
    ([]))))

coq_Serialize_projection_body :: CeresSerialize.Serialize
                                 EAst.Coq_projection_body
coq_Serialize_projection_body pb =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'p'
    (Bytestring.String__String 'r' (Bytestring.String__String 'o'
    (Bytestring.String__String 'j' (Bytestring.String__String 'e'
    (Bytestring.String__String 'c' (Bytestring.String__String 't'
    (Bytestring.String__String 'i' (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' (Bytestring.String__String '_'
    (Bytestring.String__String 'b' (Bytestring.String__String 'o'
    (Bytestring.String__String 'd' (Bytestring.String__String 'y'
    Bytestring.String__EmptyString))))))))))))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_ident
      (EAst.proj_name pb))
    ([])))

coq_Serialize_one_inductive_body :: CeresSerialize.Serialize
                                    EAst.Coq_one_inductive_body
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
      (EAst.ind_name oib))
    ((:)
    (CeresSerialize.to_sexp CeresSerialize.coq_Serialize_bool
      (EAst.ind_propositional oib))
    ((:)
    (CeresSerialize.to_sexp
      SerializeCommon.coq_Serialize_allowed_eliminations
      (EAst.ind_kelim oib))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list coq_Serialize_constructor_body)
      (EAst.ind_ctors oib))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list coq_Serialize_projection_body)
      (EAst.ind_projs oib))
    ([])))))))

coq_Serialize_mutual_inductive_body :: CeresSerialize.Serialize
                                       EAst.Coq_mutual_inductive_body
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
      (EAst.ind_finite mib))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      (EAst.ind_npars mib))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list coq_Serialize_one_inductive_body)
      (EAst.ind_bodies mib))
    ([])))))

coq_Serialize_constant_body :: CeresSerialize.Serialize
                               EAst.Coq_constant_body
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
      (CeresSerialize.coq_Serialize_option coq_Serialize_term)
      (EAst.cst_body cb))
    ([])))

coq_Serialize_global_decl :: CeresSerialize.Serialize EAst.Coq_global_decl
coq_Serialize_global_decl gd =
  case gd of {
   EAst.ConstantDecl cb -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'C' (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' (Bytestring.String__String 's'
    (Bytestring.String__String 't' (Bytestring.String__String 'a'
    (Bytestring.String__String 'n' (Bytestring.String__String 't'
    (Bytestring.String__String 'D' (Bytestring.String__String 'e'
    (Bytestring.String__String 'c' (Bytestring.String__String 'l'
    Bytestring.String__EmptyString)))))))))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_constant_body cb) ([])));
   EAst.InductiveDecl mib -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'I' (Bytestring.String__String 'n'
    (Bytestring.String__String 'd' (Bytestring.String__String 'u'
    (Bytestring.String__String 'c' (Bytestring.String__String 't'
    (Bytestring.String__String 'i' (Bytestring.String__String 'v'
    (Bytestring.String__String 'e' (Bytestring.String__String 'D'
    (Bytestring.String__String 'e' (Bytestring.String__String 'c'
    (Bytestring.String__String 'l'
    Bytestring.String__EmptyString))))))))))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_mutual_inductive_body mib) ([])))}

coq_Serialize_global_declarations :: CeresSerialize.Serialize
                                     EAst.Coq_global_declarations
coq_Serialize_global_declarations gd =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_list
      (CeresSerialize.coq_Serialize_product
        SerializeCommon.coq_Serialize_kername coq_Serialize_global_decl))
    gd

