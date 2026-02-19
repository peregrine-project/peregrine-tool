module ListDef where

import qualified Prelude

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a l0 -> (:) (f a) (map f l0)}

