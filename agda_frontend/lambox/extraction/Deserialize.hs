module Deserialize where

import qualified Prelude
import qualified Config0
import qualified ConfigUtils
import qualified PAst
import qualified SerializeConfig
import qualified SerializePAst
import qualified Bytestring

string_of_PAst :: PAst.PAst -> Bytestring.String__Coq_t
string_of_PAst =
  SerializePAst.string_of_PAst

string_of_config :: ConfigUtils.Coq_config' -> Bytestring.String__Coq_t
string_of_config =
  SerializeConfig.string_of_config'

string_of_backend_config :: ConfigUtils.Coq_backend_config' ->
                            Bytestring.String__Coq_t
string_of_backend_config =
  SerializeConfig.string_of_backend_config'

string_of_erasure_phases :: ConfigUtils.Coq_erasure_phases' ->
                            Bytestring.String__Coq_t
string_of_erasure_phases =
  SerializeConfig.string_of_erasure_phases'

string_of_attributes_config :: Config0.Coq_attributes_config ->
                               Bytestring.String__Coq_t
string_of_attributes_config =
  SerializeConfig.string_of_attributes_config

