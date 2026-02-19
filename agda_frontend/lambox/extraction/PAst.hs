module PAst where

import qualified Prelude
import qualified EAst
import qualified ExAst

type Coq_typed_env = ExAst.Coq_global_env

type Coq_untyped_env = EAst.Coq_global_declarations

data PAst =
   Untyped Coq_untyped_env (Prelude.Maybe EAst.Coq_term)
 | Typed Coq_typed_env (Prelude.Maybe EAst.Coq_term)

