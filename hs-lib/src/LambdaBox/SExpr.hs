-- Lambda Box Serializers
module LambdaBox.SExpr where

import qualified LambdaBox.LambdaBox
import qualified LambdaBox.LBoxConvert
import qualified LambdaBox.Config
import qualified LambdaBox.ConfigConvert
import qualified LambdaBox.Target
import qualified Deserialize
import qualified Bytestring
import Data.ByteString.Char8 (pack)
import Data.Text (unpack)
import Data.Text.Encoding (decodeUtf8)

decodeString :: Bytestring.String__Coq_t -> String
decodeString s =
  unpack $ decodeUtf8 $ pack $ Bytestring._String__to_string s

lBoxModuleToSexp :: LambdaBox.Target.Target t -> LambdaBox.LambdaBox.LBoxModule t -> String
lBoxModuleToSexp target p =
  decodeString $ Deserialize.string_of_PAst $ LambdaBox.LBoxConvert.lBoxModuleConv target p

configToSexp :: LambdaBox.Config.Config -> String
configToSexp c =
  decodeString $ Deserialize.string_of_config $ LambdaBox.ConfigConvert.configConv c

backendConfigToSexp :: LambdaBox.Config.BackendConfig -> String
backendConfigToSexp c =
  decodeString $ Deserialize.string_of_backend_config $ LambdaBox.ConfigConvert.backendConfigConv c

erasurePhasesToSexp :: LambdaBox.Config.ErasurePhases -> String
erasurePhasesToSexp c =
  decodeString $ Deserialize.string_of_erasure_phases $ LambdaBox.ConfigConvert.erasurePhasesConv c

attributesConfigToSexp :: LambdaBox.Config.AttributesConfig -> String
attributesConfigToSexp c =
  decodeString $ Deserialize.string_of_attributes_config $ LambdaBox.ConfigConvert.attributesConfigConv c
