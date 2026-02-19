module ERemapInductives where

import qualified Prelude
import qualified Kernames

data Coq_extract_inductive =
   Build_extract_inductive (([]) Kernames.Coq_kername) Kernames.Coq_kername

cstrs :: Coq_extract_inductive -> ([]) Kernames.Coq_kername
cstrs e =
  case e of {
   Build_extract_inductive cstrs0 _ -> cstrs0}

elim :: Coq_extract_inductive -> Kernames.Coq_kername
elim e =
  case e of {
   Build_extract_inductive _ elim0 -> elim0}

