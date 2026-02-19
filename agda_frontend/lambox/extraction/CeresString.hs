{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module CeresString where

import qualified Prelude
import qualified Ascii
import qualified BinInt
import qualified BinNums
import qualified ByteCompare
import qualified Datatypes
import qualified DecimalString
import qualified Nat0
import qualified PeanoNat
import qualified Bytestring

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

eqb_byte :: Prelude.Char -> Prelude.Char -> Prelude.Bool
eqb_byte =
  ByteCompare.eqb

byte_compare :: Prelude.Char -> Prelude.Char -> Datatypes.Coq_comparison
byte_compare =
  ByteCompare.compare

leb_byte :: Prelude.Char -> Prelude.Char -> Prelude.Bool
leb_byte a b =
  case byte_compare a b of {
   Datatypes.Gt -> Prelude.False;
   _ -> Prelude.True}

is_printable :: Prelude.Char -> Prelude.Bool
is_printable c =
  (Prelude.&&) (leb_byte ' ' c) (leb_byte c '~')

is_utf_8 :: Prelude.Char -> Prelude.Bool
is_utf_8 c =
  (Prelude.&&) (leb_byte '\x80' c) (leb_byte c '\xf4')

_units_digit :: Datatypes.Coq_nat -> Prelude.Char
_units_digit n =
  (\x -> x)
    (Ascii.ascii_of_nat
      (Nat0.add
        (PeanoNat._Nat__modulo n (Datatypes.S (Datatypes.S (Datatypes.S
          (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
          (Datatypes.S (Datatypes.S Datatypes.O)))))))))))
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S
        Datatypes.O))))))))))))))))))))))))))))))))))))))))))))))))))

_three_digit :: Datatypes.Coq_nat -> Bytestring.String__Coq_t
_three_digit n =
  let {n0 = _units_digit n} in
  let {
   n1 = _units_digit
          (PeanoNat._Nat__div n (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S Datatypes.O)))))))))))}
  in
  let {
   n2 = _units_digit
          (PeanoNat._Nat__div n (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
            (Datatypes.S (Datatypes.S
            Datatypes.O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))}
  in
  Bytestring.String__String n2 (Bytestring.String__String n1
  (Bytestring.String__String n0 Bytestring.String__EmptyString))

_escape_string :: Bytestring.String__Coq_t -> Bytestring.String__Coq_t ->
                  Bytestring.String__Coq_t
_escape_string _end s =
  case s of {
   Bytestring.String__EmptyString -> _end;
   Bytestring.String__String c s' ->
    let {escaped_s' = _escape_string _end s'} in
    case eqb_byte '\t' c of {
     Prelude.True -> Bytestring.String__String '\\'
      (Bytestring.String__String 't' escaped_s');
     Prelude.False ->
      case eqb_byte '\n' c of {
       Prelude.True -> Bytestring.String__String '\\'
        (Bytestring.String__String 'n' escaped_s');
       Prelude.False ->
        case eqb_byte '\r' c of {
         Prelude.True -> Bytestring.String__String '\\'
          (Bytestring.String__String 'r' escaped_s');
         Prelude.False ->
          case eqb_byte '"' c of {
           Prelude.True -> Bytestring.String__String '\\'
            (Bytestring.String__String '"' escaped_s');
           Prelude.False ->
            case eqb_byte '\\' c of {
             Prelude.True -> Bytestring.String__String '\\'
              (Bytestring.String__String '\\' escaped_s');
             Prelude.False ->
              case (Prelude.||) (is_printable c) (is_utf_8 c) of {
               Prelude.True -> Bytestring.String__String c escaped_s';
               Prelude.False ->
                let {n = Ascii.nat_of_ascii ((\x -> x) c)} in
                Bytestring.String__String '\\'
                (Bytestring._String__append (_three_digit n) escaped_s')}}}}}}}

escape_string :: Bytestring.String__Coq_t -> Bytestring.String__Coq_t
escape_string s =
  Bytestring.String__String '"'
    (_escape_string (Bytestring.String__String '"'
      Bytestring.String__EmptyString) s)

string_of_Z :: BinNums.Z -> Bytestring.String__Coq_t
string_of_Z n =
  Bytestring._String__of_string
    (DecimalString._NilEmpty__string_of_int (BinInt._Z__to_int n))

string_of_bool :: Prelude.Bool -> Bytestring.String__Coq_t
string_of_bool b =
  case b of {
   Prelude.True -> Bytestring.String__String 't' (Bytestring.String__String
    'r' (Bytestring.String__String 'u' (Bytestring.String__String 'e'
    Bytestring.String__EmptyString)));
   Prelude.False -> Bytestring.String__String 'f' (Bytestring.String__String
    'a' (Bytestring.String__String 'l' (Bytestring.String__String 's'
    (Bytestring.String__String 'e' Bytestring.String__EmptyString))))}

type DString__Coq_t = Bytestring.String__Coq_t -> Bytestring.String__Coq_t

_DString__of_string :: Bytestring.String__Coq_t -> DString__Coq_t
_DString__of_string =
  Bytestring._String__append

_DString__of_byte :: Prelude.Char -> DString__Coq_t
_DString__of_byte c s =
  Bytestring.String__String c s

_DString__app_string :: DString__Coq_t -> Bytestring.String__Coq_t ->
                        Bytestring.String__Coq_t
_DString__app_string =
  unsafeCoerce Datatypes.id

