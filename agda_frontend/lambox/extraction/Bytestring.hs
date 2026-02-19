module Bytestring where

import qualified Prelude

data String__Coq_t =
   String__EmptyString
 | String__String Prelude.Char String__Coq_t

_String__append :: String__Coq_t -> String__Coq_t -> String__Coq_t
_String__append x y =
  case x of {
   String__EmptyString -> y;
   String__String x0 xs -> String__String x0 (_String__append xs y)}

_String__to_string :: String__Coq_t -> Prelude.String
_String__to_string b =
  case b of {
   String__EmptyString -> "";
   String__String x xs -> (:) ((\x -> x) x) (_String__to_string xs)}

_String__of_string :: Prelude.String -> String__Coq_t
_String__of_string b =
  case b of {
   ([]) -> String__EmptyString;
   (:) x xs -> String__String ((\x -> x) x) (_String__of_string xs)}

