From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From Stdlib Require Import Strings.Byte.
From Stdlib Require Import NArith.BinNat.
From Peregrine Require Import Unicode.

Local Open Scope bs_scope.



(* XID Unicode properties
  According to
    https://www.unicode.org/reports/tr31/
    https://www.unicode.org/versions/Unicode17.0.0/
*)

(* XID_Start property *)
Timeout 5 Definition is_xid_start' (u v w x y z : hex_digit) : bool :=
  if negb (hex_eqb u D0) then false else (* No code points over U+033479 *)
  let c := (u,(v,(w,(x,(y,z))))) in
  (match compare_range c (D0,(D0,(Da,(Db,(D5,Dc))))) (D0,(D0,(Da,(Db,(D6,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(Df,Dc))))) (D0,(D0,(D1,(D2,(D4,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(Dd,D0))))) (D0,(D0,(D0,(Da,(Dd,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D0,D0))))) (D0,(D0,(D0,(D8,(D1,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(Df,D7))))) (D0,(D0,(D0,(D4,(D8,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D2,(De,Dc))))) (D0,(D0,(D0,(D2,(De,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Dc,D0))))) (D0,(D0,(D0,(D0,(Dd,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Da,Da))))) (D0,(D0,(D0,(D0,(Da,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(D6,D1))))) (D0,(D0,(D0,(D0,(D7,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(D4,D1))))) (D0,(D0,(D0,(D0,(D5,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D0,(Db,Da))))) (D0,(D0,(D0,(D0,(Db,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Db,D5))))) (D0,(D0,(D0,(D0,(Db,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D2,(Dc,D6))))) (D0,(D0,(D0,(D2,(Dd,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Df,D8))))) (D0,(D0,(D0,(D2,(Dc,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Dd,D8))))) (D0,(D0,(D0,(D0,(Df,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D2,(De,D0))))) (D0,(D0,(D0,(D2,(De,D4))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D3,(D8,D6))))) (D0,(D0,(D0,(D3,(D8,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(D7,D6))))) (D0,(D0,(D0,(D3,(D7,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(D7,D0))))) (D0,(D0,(D0,(D3,(D7,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D2,(De,De))))) (D0,(D0,(D0,(D2,(De,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D3,(D7,Df))))) (D0,(D0,(D0,(D3,(D7,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(D7,Db))))) (D0,(D0,(D0,(D3,(D7,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D3,(D8,De))))) (D0,(D0,(D0,(D3,(Da,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(D8,Dc))))) (D0,(D0,(D0,(D3,(D8,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(D8,D8))))) (D0,(D0,(D0,(D3,(D8,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D3,(Da,D3))))) (D0,(D0,(D0,(D3,(Df,D5))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D6,(De,D5))))) (D0,(D0,(D0,(D6,(De,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(De,Df))))) (D0,(D0,(D0,(D5,(Df,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(D5,D9))))) (D0,(D0,(D0,(D5,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(D3,D1))))) (D0,(D0,(D0,(D5,(D5,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D4,(D8,Da))))) (D0,(D0,(D0,(D5,(D2,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D5,(Dd,D0))))) (D0,(D0,(D0,(D5,(De,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(D6,D0))))) (D0,(D0,(D0,(D5,(D8,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D6,(D7,D1))))) (D0,(D0,(D0,(D6,(Dd,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(D6,De))))) (D0,(D0,(D0,(D6,(D6,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(D2,D0))))) (D0,(D0,(D0,(D6,(D4,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D6,(Dd,D5))))) (D0,(D0,(D0,(D6,(Dd,D5))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D7,(D4,Dd))))) (D0,(D0,(D0,(D7,(Da,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(Df,Df))))) (D0,(D0,(D0,(D6,(Df,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(Df,Da))))) (D0,(D0,(D0,(D6,(Df,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(De,De))))) (D0,(D0,(D0,(D6,(De,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D7,(D1,D2))))) (D0,(D0,(D0,(D7,(D2,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D7,(D1,D0))))) (D0,(D0,(D0,(D7,(D1,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D7,(Df,D4))))) (D0,(D0,(D0,(D7,(Df,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D7,(Dc,Da))))) (D0,(D0,(D0,(D7,(De,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D7,(Db,D1))))) (D0,(D0,(D0,(D7,(Db,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D7,(Df,Da))))) (D0,(D0,(D0,(D7,(Df,Da))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(Dd,Dc))))) (D0,(D0,(D0,(D9,(Dd,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(D5,D0))))) (D0,(D0,(D0,(D9,(D5,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D7,D0))))) (D0,(D0,(D0,(D8,(D8,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D2,D8))))) (D0,(D0,(D0,(D8,(D2,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D2,D4))))) (D0,(D0,(D0,(D8,(D2,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D1,Da))))) (D0,(D0,(D0,(D8,(D1,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D8,(D6,D0))))) (D0,(D0,(D0,(D8,(D6,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D4,D0))))) (D0,(D0,(D0,(D8,(D5,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(D0,D4))))) (D0,(D0,(D0,(D9,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(Da,D0))))) (D0,(D0,(D0,(D8,(Dc,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D8,D9))))) (D0,(D0,(D0,(D8,(D8,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(D3,Dd))))) (D0,(D0,(D0,(D9,(D3,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(Da,Da))))) (D0,(D0,(D0,(D9,(Db,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(D8,D5))))) (D0,(D0,(D0,(D9,(D8,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(D7,D1))))) (D0,(D0,(D0,(D9,(D8,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(D5,D8))))) (D0,(D0,(D0,(D9,(D6,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(D9,D3))))) (D0,(D0,(D0,(D9,(Da,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(D8,Df))))) (D0,(D0,(D0,(D9,(D9,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(Db,Dd))))) (D0,(D0,(D0,(D9,(Db,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Db,D6))))) (D0,(D0,(D0,(D9,(Db,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Db,D2))))) (D0,(D0,(D0,(D9,(Db,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(Dc,De))))) (D0,(D0,(D0,(D9,(Dc,De))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D5,D9))))) (D0,(D0,(D0,(Da,(D5,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D1,D3))))) (D0,(D0,(D0,(Da,(D2,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Df,Dc))))) (D0,(D0,(D0,(D9,(Df,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Df,D0))))) (D0,(D0,(D0,(D9,(Df,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Dd,Df))))) (D0,(D0,(D0,(D9,(De,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D0,Df))))) (D0,(D0,(D0,(Da,(D1,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D0,D5))))) (D0,(D0,(D0,(Da,(D0,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D3,D5))))) (D0,(D0,(D0,(Da,(D3,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D3,D2))))) (D0,(D0,(D0,(Da,(D3,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D2,Da))))) (D0,(D0,(D0,(Da,(D3,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D3,D8))))) (D0,(D0,(D0,(Da,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D9,D3))))) (D0,(D0,(D0,(Da,(Da,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D8,D5))))) (D0,(D0,(D0,(Da,(D8,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D7,D2))))) (D0,(D0,(D0,(Da,(D7,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D5,De))))) (D0,(D0,(D0,(Da,(D5,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D8,Df))))) (D0,(D0,(D0,(Da,(D9,D1))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(Db,D5))))) (D0,(D0,(D0,(Da,(Db,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(Db,D2))))) (D0,(D0,(D0,(Da,(Db,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(Da,Da))))) (D0,(D0,(D0,(Da,(Db,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(Db,Dd))))) (D0,(D0,(D0,(Da,(Db,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(D0,De))))) (D0,(D0,(D0,(Dd,(D1,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(Da,De))))) (D0,(D0,(D0,(Db,(Db,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D5,Df))))) (D0,(D0,(D0,(Db,(D6,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D2,Da))))) (D0,(D0,(D0,(Db,(D3,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D0,D5))))) (D0,(D0,(D0,(Db,(D0,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(Df,D9))))) (D0,(D0,(D0,(Da,(Df,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(De,D0))))) (D0,(D0,(D0,(Da,(De,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D1,D3))))) (D0,(D0,(D0,(Db,(D2,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D0,Df))))) (D0,(D0,(D0,(Db,(D1,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D3,Dd))))) (D0,(D0,(D0,(Db,(D3,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D3,D5))))) (D0,(D0,(D0,(Db,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D3,D2))))) (D0,(D0,(D0,(Db,(D3,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D5,Dc))))) (D0,(D0,(D0,(Db,(D5,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D9,D9))))) (D0,(D0,(D0,(Db,(D9,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D8,D5))))) (D0,(D0,(D0,(Db,(D8,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D8,D3))))) (D0,(D0,(D0,(Db,(D8,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D7,D1))))) (D0,(D0,(D0,(Db,(D7,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D9,D2))))) (D0,(D0,(D0,(Db,(D9,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D8,De))))) (D0,(D0,(D0,(Db,(D9,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(Da,D3))))) (D0,(D0,(D0,(Db,(Da,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D9,De))))) (D0,(D0,(D0,(Db,(D9,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D9,Dc))))) (D0,(D0,(D0,(Db,(D9,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(Da,D8))))) (D0,(D0,(D0,(Db,(Da,Da))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D8,D5))))) (D0,(D0,(D0,(Dc,(D8,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D3,Dd))))) (D0,(D0,(D0,(Dc,(D3,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D0,De))))) (D0,(D0,(D0,(Dc,(D1,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D0,D5))))) (D0,(D0,(D0,(Dc,(D0,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(Dd,D0))))) (D0,(D0,(D0,(Db,(Dd,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D2,Da))))) (D0,(D0,(D0,(Dc,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D1,D2))))) (D0,(D0,(D0,(Dc,(D2,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D6,D0))))) (D0,(D0,(D0,(Dc,(D6,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D5,Dc))))) (D0,(D0,(D0,(Dc,(D5,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D5,D8))))) (D0,(D0,(D0,(Dc,(D5,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D8,D0))))) (D0,(D0,(D0,(Dc,(D8,D0))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(Db,Dd))))) (D0,(D0,(D0,(Dc,(Db,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(Da,Da))))) (D0,(D0,(D0,(Dc,(Db,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D9,D2))))) (D0,(D0,(D0,(Dc,(Da,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D8,De))))) (D0,(D0,(D0,(Dc,(D9,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(Db,D5))))) (D0,(D0,(D0,(Dc,(Db,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(Df,D1))))) (D0,(D0,(D0,(Dc,(Df,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(De,D0))))) (D0,(D0,(D0,(Dc,(De,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(Dd,Dc))))) (D0,(D0,(D0,(Dc,(Dd,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(D0,D4))))) (D0,(D0,(D0,(Dd,(D0,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(De,(Db,Dd))))) (D0,(D0,(D0,(De,(Db,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(Dc,D0))))) (D0,(D0,(D0,(Dd,(Dc,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D7,Da))))) (D0,(D0,(D0,(Dd,(D7,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D4,De))))) (D0,(D0,(D0,(Dd,(D4,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D3,Dd))))) (D0,(D0,(D0,(Dd,(D3,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D1,D2))))) (D0,(D0,(D0,(Dd,(D3,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(D5,Df))))) (D0,(D0,(D0,(Dd,(D6,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D5,D4))))) (D0,(D0,(D0,(Dd,(D5,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(Db,D3))))) (D0,(D0,(D0,(Dd,(Db,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D9,Da))))) (D0,(D0,(D0,(Dd,(Db,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D8,D5))))) (D0,(D0,(D0,(Dd,(D9,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(Db,Dd))))) (D0,(D0,(D0,(Dd,(Db,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(De,(D8,D6))))) (D0,(D0,(D0,(De,(D8,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D4,D0))))) (D0,(D0,(D0,(De,(D4,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D3,D2))))) (D0,(D0,(D0,(De,(D3,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D0,D1))))) (D0,(D0,(D0,(De,(D3,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(De,(D8,D4))))) (D0,(D0,(D0,(De,(D8,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D8,D1))))) (D0,(D0,(D0,(De,(D8,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(De,(Da,D7))))) (D0,(D0,(D0,(De,(Db,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(Da,D5))))) (D0,(D0,(D0,(De,(Da,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D8,Dc))))) (D0,(D0,(D0,(De,(Da,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(De,(Db,D2))))) (D0,(D0,(D0,(De,(Db,D2))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D0,(D5,Da))))) (D0,(D0,(D1,(D0,(D5,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(D4,D9))))) (D0,(D0,(D0,(Df,(D6,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(Dd,Dc))))) (D0,(D0,(D0,(De,(Dd,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(Dc,D6))))) (D0,(D0,(D0,(De,(Dc,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(Dc,D0))))) (D0,(D0,(D0,(De,(Dc,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Df,(D4,D0))))) (D0,(D0,(D0,(Df,(D4,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(D0,D0))))) (D0,(D0,(D0,(Df,(D0,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D0,(D3,Df))))) (D0,(D0,(D1,(D0,(D3,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(D0,D0))))) (D0,(D0,(D1,(D0,(D2,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(D8,D8))))) (D0,(D0,(D0,(Df,(D8,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D0,(D5,D0))))) (D0,(D0,(D1,(D0,(D5,D5))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D0,(D8,De))))) (D0,(D0,(D1,(D0,(D8,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(D6,De))))) (D0,(D0,(D1,(D0,(D7,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(D6,D5))))) (D0,(D0,(D1,(D0,(D6,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(D6,D1))))) (D0,(D0,(D1,(D0,(D6,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D0,(D7,D5))))) (D0,(D0,(D1,(D0,(D8,D1))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D0,(Dc,Dd))))) (D0,(D0,(D1,(D0,(Dc,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(Dc,D7))))) (D0,(D0,(D1,(D0,(Dc,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(Da,D0))))) (D0,(D0,(D1,(D0,(Dc,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D0,(Dd,D0))))) (D0,(D0,(D1,(D0,(Df,Da))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D2,D4))))) (D0,(D0,(D2,(D1,(D2,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Db,(D0,D5))))) (D0,(D0,(D1,(Db,(D3,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D6,(Da,D0))))) (D0,(D0,(D1,(D6,(De,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(Dc,D2))))) (D0,(D0,(D1,(D2,(Dc,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D8,Da))))) (D0,(D0,(D1,(D2,(D8,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D5,D8))))) (D0,(D0,(D1,(D2,(D5,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D5,D0))))) (D0,(D0,(D1,(D2,(D5,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D4,Da))))) (D0,(D0,(D1,(D2,(D4,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D2,(D6,D0))))) (D0,(D0,(D1,(D2,(D8,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D5,Da))))) (D0,(D0,(D1,(D2,(D5,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D2,(Db,D8))))) (D0,(D0,(D1,(D2,(Db,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(Db,D2))))) (D0,(D0,(D1,(D2,(Db,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D9,D0))))) (D0,(D0,(D1,(D2,(Db,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D2,(Dc,D0))))) (D0,(D0,(D1,(D2,(Dc,D0))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D3,(Da,D0))))) (D0,(D0,(D1,(D3,(Df,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D3,(D1,D2))))) (D0,(D0,(D1,(D3,(D1,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(Dd,D8))))) (D0,(D0,(D1,(D3,(D1,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(Dc,D8))))) (D0,(D0,(D1,(D2,(Dd,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D3,(D8,D0))))) (D0,(D0,(D1,(D3,(D8,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D3,(D1,D8))))) (D0,(D0,(D1,(D3,(D5,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D6,(D6,Df))))) (D0,(D0,(D1,(D6,(D7,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D4,(D0,D1))))) (D0,(D0,(D1,(D6,(D6,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D3,(Df,D8))))) (D0,(D0,(D1,(D3,(Df,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D6,(D8,D1))))) (D0,(D0,(D1,(D6,(D9,Da))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D8,(D8,D0))))) (D0,(D0,(D1,(D8,(Da,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D6,De))))) (D0,(D0,(D1,(D7,(D7,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D1,Df))))) (D0,(D0,(D1,(D7,(D3,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D0,D0))))) (D0,(D0,(D1,(D7,(D1,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D6,(De,De))))) (D0,(D0,(D1,(D6,(Df,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D7,(D6,D0))))) (D0,(D0,(D1,(D7,(D6,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D4,D0))))) (D0,(D0,(D1,(D7,(D5,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D7,(Dd,Dc))))) (D0,(D0,(D1,(D7,(Dd,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(Dd,D7))))) (D0,(D0,(D1,(D7,(Dd,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D8,D0))))) (D0,(D0,(D1,(D7,(Db,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D8,(D2,D0))))) (D0,(D0,(D1,(D8,(D7,D8))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D9,(D8,D0))))) (D0,(D0,(D1,(D9,(Da,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D9,(D0,D0))))) (D0,(D0,(D1,(D9,(D1,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D8,(Db,D0))))) (D0,(D0,(D1,(D8,(Df,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D8,(Da,Da))))) (D0,(D0,(D1,(D8,(Da,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D9,(D7,D0))))) (D0,(D0,(D1,(D9,(D7,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D9,(D5,D0))))) (D0,(D0,(D1,(D9,(D6,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Da,(D2,D0))))) (D0,(D0,(D1,(Da,(D5,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Da,(D0,D0))))) (D0,(D0,(D1,(Da,(D1,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D9,(Db,D0))))) (D0,(D0,(D1,(D9,(Dc,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Da,(Da,D7))))) (D0,(D0,(D1,(Da,(Da,D7))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(D5,Db))))) (D0,(D0,(D1,(Df,(D5,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(De,D9))))) (D0,(D0,(D1,(Dc,(De,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(D4,Dd))))) (D0,(D0,(D1,(Dc,(D4,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Db,(Da,De))))) (D0,(D0,(D1,(Db,(Da,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Db,(D8,D3))))) (D0,(D0,(D1,(Db,(Da,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Db,(D4,D5))))) (D0,(D0,(D1,(Db,(D4,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Dc,(D0,D0))))) (D0,(D0,(D1,(Dc,(D2,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Db,(Db,Da))))) (D0,(D0,(D1,(Db,(De,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Dc,(D9,D0))))) (D0,(D0,(D1,(Dc,(Db,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(D8,D0))))) (D0,(D0,(D1,(Dc,(D8,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(D5,Da))))) (D0,(D0,(D1,(Dc,(D7,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Dc,(Db,Dd))))) (D0,(D0,(D1,(Dc,(Db,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(D1,D8))))) (D0,(D0,(D1,(Df,(D1,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(Df,Da))))) (D0,(D0,(D1,(Dc,(Df,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(Df,D5))))) (D0,(D0,(D1,(Dc,(Df,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(De,De))))) (D0,(D0,(D1,(Dc,(Df,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(De,(D0,D0))))) (D0,(D0,(D1,(Df,(D1,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dd,(D0,D0))))) (D0,(D0,(D1,(Dd,(Db,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(D5,D0))))) (D0,(D0,(D1,(Df,(D5,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D4,D8))))) (D0,(D0,(D1,(Df,(D4,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D2,D0))))) (D0,(D0,(D1,(Df,(D4,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(D5,D9))))) (D0,(D0,(D1,(Df,(D5,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(Df,D2))))) (D0,(D0,(D1,(Df,(Df,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Dc,D2))))) (D0,(D0,(D1,(Df,(Dc,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D8,D0))))) (D0,(D0,(D1,(Df,(Db,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D5,Df))))) (D0,(D0,(D1,(Df,(D7,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D5,Dd))))) (D0,(D0,(D1,(Df,(D5,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(Db,De))))) (D0,(D0,(D1,(Df,(Db,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Db,D6))))) (D0,(D0,(D1,(Df,(Db,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(Dd,D6))))) (D0,(D0,(D1,(Df,(Dd,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Dd,D0))))) (D0,(D0,(D1,(Df,(Dd,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Dc,D6))))) (D0,(D0,(D1,(Df,(Dc,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(De,D0))))) (D0,(D0,(D1,(Df,(De,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D0,D2))))) (D0,(D0,(D2,(D1,(D0,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D0,(D7,Df))))) (D0,(D0,(D2,(D0,(D7,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D0,(D7,D1))))) (D0,(D0,(D2,(D0,(D7,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Df,D6))))) (D0,(D0,(D1,(Df,(Df,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D0,(D9,D0))))) (D0,(D0,(D2,(D0,(D9,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D1,D5))))) (D0,(D0,(D2,(D1,(D1,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D0,Da))))) (D0,(D0,(D2,(D1,(D1,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D0,D7))))) (D0,(D0,(D2,(D1,(D0,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D1,D8))))) (D0,(D0,(D2,(D1,(D1,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D6,(D4,D0))))) (D0,(D0,(Da,(D6,(D6,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Dc,D8))))) (D0,(D0,(D2,(Dd,(Dc,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(D0,D0))))) (D0,(D0,(D2,(Dd,(D2,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D4,De))))) (D0,(D0,(D2,(D1,(D4,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D2,Da))))) (D0,(D0,(D2,(D1,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D2,D8))))) (D0,(D0,(D2,(D1,(D2,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D2,D6))))) (D0,(D0,(D2,(D1,(D2,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D4,D5))))) (D0,(D0,(D2,(D1,(D4,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D3,Dc))))) (D0,(D0,(D2,(D1,(D3,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dc,(De,Db))))) (D0,(D0,(D2,(Dc,(De,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dc,(D0,D0))))) (D0,(D0,(D2,(Dc,(De,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D6,D0))))) (D0,(D0,(D2,(D1,(D8,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dc,(Df,D2))))) (D0,(D0,(D2,(Dc,(Df,D3))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dd,(Da,D0))))) (D0,(D0,(D2,(Dd,(Da,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(D3,D0))))) (D0,(D0,(D2,(Dd,(D6,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(D2,Dd))))) (D0,(D0,(D2,(Dd,(D2,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(D2,D7))))) (D0,(D0,(D2,(Dd,(D2,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dd,(D8,D0))))) (D0,(D0,(D2,(Dd,(D9,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(D6,Df))))) (D0,(D0,(D2,(Dd,(D6,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dd,(Db,D8))))) (D0,(D0,(D2,(Dd,(Db,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Db,D0))))) (D0,(D0,(D2,(Dd,(Db,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Da,D8))))) (D0,(D0,(D2,(Dd,(Da,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dd,(Dc,D0))))) (D0,(D0,(D2,(Dd,(Dc,D6))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D1,(D0,D5))))) (D0,(D0,(D3,(D1,(D2,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D0,(D3,D8))))) (D0,(D0,(D3,(D0,(D3,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D0,(D0,D5))))) (D0,(D0,(D3,(D0,(D0,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Dd,D8))))) (D0,(D0,(D2,(Dd,(Dd,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Dd,D0))))) (D0,(D0,(D2,(Dd,(Dd,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D0,(D3,D1))))) (D0,(D0,(D3,(D0,(D3,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D0,(D2,D1))))) (D0,(D0,(D3,(D0,(D2,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D0,(Da,D1))))) (D0,(D0,(D3,(D0,(Df,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D0,(D9,Dd))))) (D0,(D0,(D3,(D0,(D9,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D0,(D4,D1))))) (D0,(D0,(D3,(D0,(D9,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D0,(Df,Dc))))) (D0,(D0,(D3,(D0,(Df,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D4,(De,(D0,D0))))) (D0,(D0,(Da,(D4,(D8,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D1,(Df,D0))))) (D0,(D0,(D3,(D1,(Df,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D1,(Da,D0))))) (D0,(D0,(D3,(D1,(Db,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D1,(D3,D1))))) (D0,(D0,(D3,(D1,(D8,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D4,(D0,D0))))) (D0,(D0,(D4,(Dd,(Db,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D6,(D1,D0))))) (D0,(D0,(Da,(D6,(D1,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D5,(D0,D0))))) (D0,(D0,(Da,(D6,(D0,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D4,(Dd,D0))))) (D0,(D0,(Da,(D4,(Df,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D6,(D2,Da))))) (D0,(D0,(Da,(D6,(D2,Db))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D9,(Df,Da))))) (D0,(D0,(Da,(D9,(Df,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(D8,D2))))) (D0,(D0,(Da,(D8,(Db,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D7,(Df,D1))))) (D0,(D0,(Da,(D8,(D0,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D7,(D1,D7))))) (D0,(D0,(Da,(D7,(D1,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D6,(Da,D0))))) (D0,(D0,(Da,(D6,(De,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D6,(D7,Df))))) (D0,(D0,(Da,(D6,(D9,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D7,(D8,Db))))) (D0,(D0,(Da,(D7,(Dd,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D7,(D2,D2))))) (D0,(D0,(Da,(D7,(D8,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D8,(D0,Dc))))) (D0,(D0,(Da,(D8,(D2,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(D0,D7))))) (D0,(D0,(Da,(D8,(D0,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(D0,D3))))) (D0,(D0,(Da,(D8,(D0,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D8,(D4,D0))))) (D0,(D0,(Da,(D8,(D7,D3))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D9,(D6,D0))))) (D0,(D0,(Da,(D9,(D7,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(Df,Dd))))) (D0,(D0,(Da,(D8,(Df,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(Df,Db))))) (D0,(D0,(Da,(D8,(Df,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(Df,D2))))) (D0,(D0,(Da,(D8,(Df,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D9,(D3,D0))))) (D0,(D0,(Da,(D9,(D4,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D9,(D0,Da))))) (D0,(D0,(Da,(D9,(D2,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D9,(De,D0))))) (D0,(D0,(Da,(D9,(De,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D9,(Dc,Df))))) (D0,(D0,(Da,(D9,(Dc,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D9,(D8,D4))))) (D0,(D0,(Da,(D9,(Db,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D9,(De,D6))))) (D0,(D0,(Da,(D9,(De,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Da,(Dc,D2))))) (D0,(D0,(Da,(Da,(Dc,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(D7,De))))) (D0,(D0,(Da,(Da,(Da,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(D4,D4))))) (D0,(D0,(Da,(Da,(D4,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(D4,D0))))) (D0,(D0,(Da,(Da,(D4,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(D0,D0))))) (D0,(D0,(Da,(Da,(D2,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Da,(D7,Da))))) (D0,(D0,(Da,(Da,(D7,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(D6,D0))))) (D0,(D0,(Da,(Da,(D7,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Da,(Db,D9))))) (D0,(D0,(Da,(Da,(Db,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(Db,D5))))) (D0,(D0,(Da,(Da,(Db,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(Db,D1))))) (D0,(D0,(Da,(Da,(Db,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Da,(Dc,D0))))) (D0,(D0,(Da,(Da,(Dc,D0))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Db,(D0,D9))))) (D0,(D0,(Da,(Db,(D0,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(Df,D2))))) (D0,(D0,(Da,(Da,(Df,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(De,D0))))) (D0,(D0,(Da,(Da,(De,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(Dd,Db))))) (D0,(D0,(Da,(Da,(Dd,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Db,(D0,D1))))) (D0,(D0,(Da,(Db,(D0,D6))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Db,(D2,D8))))) (D0,(D0,(Da,(Db,(D2,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Db,(D2,D0))))) (D0,(D0,(Da,(Db,(D2,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Db,(D1,D1))))) (D0,(D0,(Da,(Db,(D1,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Db,(D3,D0))))) (D0,(D0,(Da,(Db,(D5,Da))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D9,(D0,Dc))))) (D0,(D1,(D1,(D9,(D1,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D9,(D8,D0))))) (D0,(D1,(D0,(D9,(Db,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D1,(D4,D0))))) (D0,(D1,(D0,(D1,(D7,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,D1))))) (D0,(D0,(Df,(De,(D7,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D2,Da))))) (D0,(D0,(Df,(Db,(D3,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Da,(D7,D0))))) (D0,(D0,(Df,(Da,(Dd,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Dd,(D7,(Db,D0))))) (D0,(D0,(Dd,(D7,(Dc,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Dc,(D0,D0))))) (D0,(D0,(Dd,(D7,(Da,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Db,(D7,D0))))) (D0,(D0,(Da,(Db,(De,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(D9,(D0,D0))))) (D0,(D0,(Df,(Da,(D6,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Dd,(D7,(Dc,Db))))) (D0,(D0,(Dd,(D7,(Df,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Db,(D1,Dd))))) (D0,(D0,(Df,(Db,(D1,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D1,D3))))) (D0,(D0,(Df,(Db,(D1,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D0,D0))))) (D0,(D0,(Df,(Db,(D0,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Db,(D1,Df))))) (D0,(D0,(Df,(Db,(D2,D8))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Db,(Dd,D3))))) (D0,(D0,(Df,(Dc,(D5,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D4,D0))))) (D0,(D0,(Df,(Db,(D4,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D3,De))))) (D0,(D0,(Df,(Db,(D3,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D3,D8))))) (D0,(D0,(Df,(Db,(D3,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Db,(D4,D6))))) (D0,(D0,(Df,(Db,(Db,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D4,D3))))) (D0,(D0,(Df,(Db,(D4,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Dd,(D9,D2))))) (D0,(D0,(Df,(Dd,(Dc,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Dd,(D5,D0))))) (D0,(D0,(Df,(Dd,(D8,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Dc,(D6,D4))))) (D0,(D0,(Df,(Dd,(D3,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Dd,(Df,D0))))) (D0,(D0,(Df,(Dd,(Df,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Df,(Dc,D2))))) (D0,(D0,(Df,(Df,(Dc,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,Df))))) (D0,(D0,(Df,(De,(Df,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,D9))))) (D0,(D0,(Df,(De,(D7,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,D7))))) (D0,(D0,(Df,(De,(D7,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,D3))))) (D0,(D0,(Df,(De,(D7,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(De,(D7,Dd))))) (D0,(D0,(Df,(De,(D7,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,Db))))) (D0,(D0,(Df,(De,(D7,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Df,(D6,D6))))) (D0,(D0,(Df,(Df,(D9,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(D4,D1))))) (D0,(D0,(Df,(Df,(D5,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(D2,D1))))) (D0,(D0,(Df,(Df,(D3,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Df,(Da,D0))))) (D0,(D0,(Df,(Df,(Db,De))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D0,(D2,D8))))) (D0,(D1,(D0,(D0,(D3,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(Dd,Da))))) (D0,(D0,(Df,(Df,(Dd,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(Dd,D2))))) (D0,(D0,(Df,(Df,(Dd,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(Dc,Da))))) (D0,(D0,(Df,(Df,(Dc,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D0,(D0,Dd))))) (D0,(D1,(D0,(D0,(D2,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D0,(D0,D0))))) (D0,(D1,(D0,(D0,(D0,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D0,(D5,D0))))) (D0,(D1,(D0,(D0,(D5,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D0,(D3,Df))))) (D0,(D1,(D0,(D0,(D4,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D0,(D3,Dc))))) (D0,(D1,(D0,(D0,(D3,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D0,(D8,D0))))) (D0,(D1,(D0,(D0,(Df,Da))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D5,(Db,Db))))) (D0,(D1,(D0,(D5,(Db,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D4,(Db,D0))))) (D0,(D1,(D0,(D4,(Dd,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D3,(D8,D0))))) (D0,(D1,(D0,(D3,(D9,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D3,(D0,D0))))) (D0,(D1,(D0,(D3,(D1,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D2,(Da,D0))))) (D0,(D1,(D0,(D2,(Dd,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D2,(D8,D0))))) (D0,(D1,(D0,(D2,(D9,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D3,(D5,D0))))) (D0,(D1,(D0,(D3,(D7,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D3,(D2,Dd))))) (D0,(D1,(D0,(D3,(D4,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D3,(Dd,D1))))) (D0,(D1,(D0,(D3,(Dd,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D3,(Dc,D8))))) (D0,(D1,(D0,(D3,(Dc,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D3,(Da,D0))))) (D0,(D1,(D0,(D3,(Dc,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D4,(D0,D0))))) (D0,(D1,(D0,(D4,(D9,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D5,(D8,Dc))))) (D0,(D1,(D0,(D5,(D9,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D3,D0))))) (D0,(D1,(D0,(D5,(D6,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D0,D0))))) (D0,(D1,(D0,(D5,(D2,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D4,(Dd,D8))))) (D0,(D1,(D0,(D4,(Df,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D5,(D7,Dc))))) (D0,(D1,(D0,(D5,(D8,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D7,D0))))) (D0,(D1,(D0,(D5,(D7,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D5,(Da,D3))))) (D0,(D1,(D0,(D5,(Db,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D9,D7))))) (D0,(D1,(D0,(D5,(Da,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D9,D4))))) (D0,(D1,(D0,(D5,(D9,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D5,(Db,D3))))) (D0,(D1,(D0,(D5,(Db,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(D3,D7))))) (D0,(D1,(D0,(D8,(D3,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D7,(D8,D7))))) (D0,(D1,(D0,(D7,(Db,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D7,(D4,D0))))) (D0,(D1,(D0,(D7,(D5,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D6,(D0,D0))))) (D0,(D1,(D0,(D7,(D3,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(Dc,D0))))) (D0,(D1,(D0,(D5,(Df,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D7,(D8,D0))))) (D0,(D1,(D0,(D7,(D8,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D7,(D6,D0))))) (D0,(D1,(D0,(D7,(D6,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(D0,D8))))) (D0,(D1,(D0,(D8,(D0,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(D0,D0))))) (D0,(D1,(D0,(D8,(D0,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D7,(Db,D2))))) (D0,(D1,(D0,(D7,(Db,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(D0,Da))))) (D0,(D1,(D0,(D8,(D3,D5))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(De,D0))))) (D0,(D1,(D0,(D8,(Df,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(D6,D0))))) (D0,(D1,(D0,(D8,(D7,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(D3,Df))))) (D0,(D1,(D0,(D8,(D5,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(D3,Dc))))) (D0,(D1,(D0,(D8,(D3,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(D8,D0))))) (D0,(D1,(D0,(D8,(D9,De))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D9,(D2,D0))))) (D0,(D1,(D0,(D9,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D9,(D0,D0))))) (D0,(D1,(D0,(D9,(D1,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(Df,D4))))) (D0,(D1,(D0,(D8,(Df,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D9,(D4,D0))))) (D0,(D1,(D0,(D9,(D5,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D2,(D0,D0))))) (D0,(D1,(D1,(D2,(D1,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(De,(Dc,D2))))) (D0,(D1,(D0,(De,(Dc,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Db,(D4,D0))))) (D0,(D1,(D0,(Db,(D5,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D6,D0))))) (D0,(D1,(D0,(Da,(D7,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D1,D0))))) (D0,(D1,(D0,(Da,(D1,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D0,D0))))) (D0,(D1,(D0,(Da,(D0,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D9,(Db,De))))) (D0,(D1,(D0,(D9,(Db,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Da,(D1,D9))))) (D0,(D1,(D0,(Da,(D3,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D1,D5))))) (D0,(D1,(D0,(Da,(D1,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Da,(Dc,D9))))) (D0,(D1,(D0,(Da,(De,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(Dc,D0))))) (D0,(D1,(D0,(Da,(Dc,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D8,D0))))) (D0,(D1,(D0,(Da,(D9,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Db,(D0,D0))))) (D0,(D1,(D0,(Db,(D3,D5))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Dd,(D0,D0))))) (D0,(D1,(D0,(Dd,(D2,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Dc,(D0,D0))))) (D0,(D1,(D0,(Dc,(D4,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Db,(D8,D0))))) (D0,(D1,(D0,(Db,(D9,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Db,(D6,D0))))) (D0,(D1,(D0,(Db,(D7,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Dc,(Dc,D0))))) (D0,(D1,(D0,(Dc,(Df,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Dc,(D8,D0))))) (D0,(D1,(D0,(Dc,(Db,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(De,(D8,D0))))) (D0,(D1,(D0,(De,(Da,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Dd,(D6,Df))))) (D0,(D1,(D0,(Dd,(D8,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Dd,(D4,Da))))) (D0,(D1,(D0,(Dd,(D6,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(De,(Db,D0))))) (D0,(D1,(D0,(De,(Db,D1))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D0,(Dd,D0))))) (D0,(D1,(D1,(D0,(De,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Df,(De,D0))))) (D0,(D1,(D0,(Df,(Df,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Df,(D3,D0))))) (D0,(D1,(D0,(Df,(D4,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Df,(D2,D7))))) (D0,(D1,(D0,(Df,(D2,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Df,(D0,D0))))) (D0,(D1,(D0,(Df,(D1,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Df,(Db,D0))))) (D0,(D1,(D0,(Df,(Dc,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Df,(D7,D0))))) (D0,(D1,(D0,(Df,(D8,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D0,(D7,D5))))) (D0,(D1,(D1,(D0,(D7,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D0,(D7,D1))))) (D0,(D1,(D1,(D0,(D7,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D0,(D0,D3))))) (D0,(D1,(D1,(D0,(D3,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D0,(D8,D3))))) (D0,(D1,(D1,(D0,(Da,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D1,(D7,D6))))) (D0,(D1,(D1,(D1,(D7,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(D4,D7))))) (D0,(D1,(D1,(D1,(D4,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(D4,D4))))) (D0,(D1,(D1,(D1,(D4,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(D0,D3))))) (D0,(D1,(D1,(D1,(D2,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D1,(D5,D0))))) (D0,(D1,(D1,(D1,(D7,D2))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D1,(Dd,Da))))) (D0,(D1,(D1,(D1,(Dd,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(Dc,D1))))) (D0,(D1,(D1,(D1,(Dc,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(D8,D3))))) (D0,(D1,(D1,(D1,(Db,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D1,(Dd,Dc))))) (D0,(D1,(D1,(D1,(Dd,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(Db,D7))))) (D0,(D1,(D1,(D3,(Db,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D1,D3))))) (D0,(D1,(D1,(D3,(D2,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D8,Df))))) (D0,(D1,(D1,(D2,(D9,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D8,D0))))) (D0,(D1,(D1,(D2,(D8,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D3,Df))))) (D0,(D1,(D1,(D2,(D4,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D1,D3))))) (D0,(D1,(D1,(D2,(D2,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D2,(D8,Da))))) (D0,(D1,(D1,(D2,(D8,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D8,D8))))) (D0,(D1,(D1,(D2,(D8,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D0,D5))))) (D0,(D1,(D1,(D3,(D0,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(Db,D0))))) (D0,(D1,(D1,(D2,(Dd,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D9,Df))))) (D0,(D1,(D1,(D2,(Da,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D0,Df))))) (D0,(D1,(D1,(D3,(D1,D0))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D5,Dd))))) (D0,(D1,(D1,(D3,(D6,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D3,D5))))) (D0,(D1,(D1,(D3,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D3,D2))))) (D0,(D1,(D1,(D3,(D3,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D2,Da))))) (D0,(D1,(D1,(D3,(D3,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D5,D0))))) (D0,(D1,(D1,(D3,(D5,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D3,Dd))))) (D0,(D1,(D1,(D3,(D3,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D8,De))))) (D0,(D1,(D1,(D3,(D8,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D8,Db))))) (D0,(D1,(D1,(D3,(D8,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D8,D0))))) (D0,(D1,(D1,(D3,(D8,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D9,D0))))) (D0,(D1,(D1,(D3,(Db,D5))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D6,(D0,D0))))) (D0,(D1,(D1,(D6,(D2,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D4,(D8,D0))))) (D0,(D1,(D1,(D4,(Da,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D4,(D0,D0))))) (D0,(D1,(D1,(D4,(D3,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(Dd,D3))))) (D0,(D1,(D1,(D3,(Dd,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(Dd,D1))))) (D0,(D1,(D1,(D3,(Dd,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D4,(D5,Df))))) (D0,(D1,(D1,(D4,(D6,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D4,(D4,D7))))) (D0,(D1,(D1,(D4,(D4,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D5,(D8,D0))))) (D0,(D1,(D1,(D5,(Da,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D4,(Dc,D7))))) (D0,(D1,(D1,(D4,(Dc,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D4,(Dc,D4))))) (D0,(D1,(D1,(D4,(Dc,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D5,(Dd,D8))))) (D0,(D1,(D1,(D5,(Dd,Db))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D7,(D4,D0))))) (D0,(D1,(D1,(D7,(D4,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D6,(Db,D8))))) (D0,(D1,(D1,(D6,(Db,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D6,(D8,D0))))) (D0,(D1,(D1,(D6,(Da,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D6,(D4,D4))))) (D0,(D1,(D1,(D6,(D4,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D7,(D0,D0))))) (D0,(D1,(D1,(D7,(D1,Da))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D8,(Df,Df))))) (D0,(D1,(D1,(D9,(D0,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D8,(Da,D0))))) (D0,(D1,(D1,(D8,(Dd,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D8,(D0,D0))))) (D0,(D1,(D1,(D8,(D2,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D9,(D0,D9))))) (D0,(D1,(D1,(D9,(D0,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(Dc,D5))))) (D0,(D1,(Dd,(D5,(D0,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(D8,(D0,D0))))) (D0,(D1,(D6,(Da,(D3,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D0,D8))))) (D0,(D1,(D1,(Dd,(D0,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Da,(D3,Da))))) (D0,(D1,(D1,(Da,(D3,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(Da,Da))))) (D0,(D1,(D1,(D9,(Dd,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(D3,Df))))) (D0,(D1,(D1,(D9,(D3,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(D1,D8))))) (D0,(D1,(D1,(D9,(D2,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(D1,D5))))) (D0,(D1,(D1,(D9,(D1,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D9,(Da,D0))))) (D0,(D1,(D1,(D9,(Da,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(D4,D1))))) (D0,(D1,(D1,(D9,(D4,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Da,(D0,D0))))) (D0,(D1,(D1,(Da,(D0,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(De,D3))))) (D0,(D1,(D1,(D9,(De,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(De,D1))))) (D0,(D1,(D1,(D9,(De,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Da,(D0,Db))))) (D0,(D1,(D1,(Da,(D3,D2))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dc,(D0,D0))))) (D0,(D1,(D1,(Dc,(D0,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Da,(D9,Dd))))) (D0,(D1,(D1,(Da,(D9,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Da,(D5,Dc))))) (D0,(D1,(D1,(Da,(D8,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Da,(D5,D0))))) (D0,(D1,(D1,(Da,(D5,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Db,(Dc,D0))))) (D0,(D1,(D1,(Db,(De,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Da,(Db,D0))))) (D0,(D1,(D1,(Da,(Df,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dc,(D7,D2))))) (D0,(D1,(D1,(Dc,(D8,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dc,(D4,D0))))) (D0,(D1,(D1,(Dc,(D4,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dc,(D0,Da))))) (D0,(D1,(D1,(Dc,(D2,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dd,(D0,D0))))) (D0,(D1,(D1,(Dd,(D0,D6))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Df,(D1,D2))))) (D0,(D1,(D1,(Df,(D3,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D9,D8))))) (D0,(D1,(D1,(Dd,(D9,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D6,D0))))) (D0,(D1,(D1,(Dd,(D6,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D4,D6))))) (D0,(D1,(D1,(Dd,(D4,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D0,Db))))) (D0,(D1,(D1,(Dd,(D3,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dd,(D6,Da))))) (D0,(D1,(D1,(Dd,(D8,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D6,D7))))) (D0,(D1,(D1,(Dd,(D6,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Df,(D0,D2))))) (D0,(D1,(D1,(Df,(D0,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(De,(De,D0))))) (D0,(D1,(D1,(De,(Df,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(Db,D0))))) (D0,(D1,(D1,(Dd,(Dd,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Df,(D0,D4))))) (D0,(D1,(D1,(Df,(D1,D0))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D3,(D0,(D0,D0))))) (D0,(D1,(D3,(D4,(D2,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D2,(D4,(D0,D0))))) (D0,(D1,(D2,(D4,(D6,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D2,(D0,(D0,D0))))) (D0,(D1,(D2,(D3,(D9,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Df,(Db,D0))))) (D0,(D1,(D1,(Df,(Db,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D2,(Df,(D9,D0))))) (D0,(D1,(D2,(Df,(Df,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D2,(D4,(D8,D0))))) (D0,(D1,(D2,(D5,(D4,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D4,(D4,(D0,D0))))) (D0,(D1,(D4,(D6,(D4,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D3,(D4,(D6,D0))))) (D0,(D1,(D4,(D3,(Df,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D3,(D4,(D4,D1))))) (D0,(D1,(D3,(D4,(D4,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(D1,(D0,D0))))) (D0,(D1,(D6,(D1,(D1,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Da,(Df,(Df,D5))))) (D0,(D1,(Da,(Df,(Df,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(De,(Db,Db))))) (D0,(D1,(D6,(De,(Dd,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Db,(D6,D3))))) (D0,(D1,(D6,(Db,(D7,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Da,(Dd,D0))))) (D0,(D1,(D6,(Da,(De,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Da,(D7,D0))))) (D0,(D1,(D6,(Da,(Db,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Da,(D4,D0))))) (D0,(D1,(D6,(Da,(D5,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Db,(D4,D0))))) (D0,(D1,(D6,(Db,(D4,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Db,(D0,D0))))) (D0,(D1,(D6,(Db,(D2,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(De,(D4,D0))))) (D0,(D1,(D6,(De,(D7,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Dd,(D4,D0))))) (D0,(D1,(D6,(Dd,(D6,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Db,(D7,Dd))))) (D0,(D1,(D6,(Db,(D8,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(De,(Da,D0))))) (D0,(D1,(D6,(De,(Db,D8))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Df,(Df,D2))))) (D0,(D1,(D6,(Df,(Df,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Df,(D9,D3))))) (D0,(D1,(D6,(Df,(D9,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Df,(D5,D0))))) (D0,(D1,(D6,(Df,(D5,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Df,(D0,D0))))) (D0,(D1,(D6,(Df,(D4,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Df,(De,D3))))) (D0,(D1,(D6,(Df,(De,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Df,(De,D0))))) (D0,(D1,(D6,(Df,(De,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D8,(Dd,(D8,D0))))) (D0,(D1,(D8,(Dd,(Df,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D8,(Dc,(Df,Df))))) (D0,(D1,(D8,(Dd,(D1,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D7,(D0,(D0,D0))))) (D0,(D1,(D8,(Dc,(Dd,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Da,(Df,(Df,D0))))) (D0,(D1,(Da,(Df,(Df,D3))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Db,(Dc,(D9,D0))))) (D0,(D1,(Db,(Dc,(D9,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(D1,(D6,D4))))) (D0,(D1,(Db,(D1,(D6,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(D1,(D3,D2))))) (D0,(D1,(Db,(D1,(D3,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(D0,(D0,D0))))) (D0,(D1,(Db,(D1,(D2,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Da,(Df,(Df,Dd))))) (D0,(D1,(Da,(Df,(Df,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Db,(D1,(D5,D5))))) (D0,(D1,(Db,(D1,(D5,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(D1,(D5,D0))))) (D0,(D1,(Db,(D1,(D5,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Db,(Dc,(D7,D0))))) (D0,(D1,(Db,(Dc,(D7,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(Dc,(D0,D0))))) (D0,(D1,(Db,(Dc,(D6,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(D1,(D7,D0))))) (D0,(D1,(Db,(D2,(Df,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Db,(Dc,(D8,D0))))) (D0,(D1,(Db,(Dc,(D8,D8))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(Da,D5))))) (D0,(D1,(Dd,(D4,(Da,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(D9,De))))) (D0,(D1,(Dd,(D4,(D9,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(D5,D6))))) (D0,(D1,(Dd,(D4,(D9,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(D0,D0))))) (D0,(D1,(Dd,(D4,(D5,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(Da,D2))))) (D0,(D1,(Dd,(D4,(Da,D2))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(Db,Db))))) (D0,(D1,(Dd,(D4,(Db,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(Da,De))))) (D0,(D1,(Dd,(D4,(Db,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(Da,D9))))) (D0,(D1,(Dd,(D4,(Da,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(Db,Dd))))) (D0,(D1,(Dd,(D4,(Dc,D3))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D9,(D0,D0))))) (D0,(D1,(De,(D9,(D4,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(Df,(D2,D5))))) (D0,(D1,(Dd,(Df,(D2,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D6,(Dc,D2))))) (D0,(D1,(Dd,(D6,(Dd,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D4,D0))))) (D0,(D1,(Dd,(D5,(D4,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D1,D6))))) (D0,(D1,(Dd,(D5,(D1,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D0,Dd))))) (D0,(D1,(Dd,(D5,(D1,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D0,D7))))) (D0,(D1,(Dd,(D5,(D0,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D5,(D3,Db))))) (D0,(D1,(Dd,(D5,(D3,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D1,De))))) (D0,(D1,(Dd,(D5,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D5,(D5,D2))))) (D0,(D1,(Dd,(D6,(Da,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D4,Da))))) (D0,(D1,(Dd,(D5,(D5,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D4,D6))))) (D0,(D1,(Dd,(D5,(D4,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D6,(Da,D8))))) (D0,(D1,(Dd,(D6,(Dc,D0))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D7,(D7,D0))))) (D0,(D1,(Dd,(D7,(D8,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D7,(D1,D6))))) (D0,(D1,(Dd,(D7,(D3,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D6,(Df,Dc))))) (D0,(D1,(Dd,(D7,(D1,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D6,(Dd,Dc))))) (D0,(D1,(Dd,(D6,(Df,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D7,(D5,D0))))) (D0,(D1,(Dd,(D7,(D6,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D7,(D3,D6))))) (D0,(D1,(Dd,(D7,(D4,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D7,(Dc,D4))))) (D0,(D1,(Dd,(D7,(Dc,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D7,(Da,Da))))) (D0,(D1,(Dd,(D7,(Dc,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D7,(D8,Da))))) (D0,(D1,(Dd,(D7,(Da,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(Df,(D0,D0))))) (D0,(D1,(Dd,(Df,(D1,De))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D6,(De,D0))))) (D0,(D1,(De,(D6,(De,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D2,(Dc,D0))))) (D0,(D1,(De,(D2,(De,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D1,(D3,D7))))) (D0,(D1,(De,(D1,(D3,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D1,(D0,D0))))) (D0,(D1,(De,(D1,(D2,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D0,(D3,D0))))) (D0,(D1,(De,(D0,(D6,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D2,(D9,D0))))) (D0,(D1,(De,(D2,(Da,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D1,(D4,De))))) (D0,(D1,(De,(D1,(D4,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D5,(Df,D0))))) (D0,(D1,(De,(D5,(Df,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D5,(Dd,D0))))) (D0,(D1,(De,(D5,(De,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D4,(Dd,D0))))) (D0,(D1,(De,(D4,(De,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D6,(Dc,D0))))) (D0,(D1,(De,(D6,(Dd,De))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D7,(De,D0))))) (D0,(D1,(De,(D7,(De,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D6,(Df,D0))))) (D0,(D1,(De,(D6,(Df,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D6,(De,D7))))) (D0,(D1,(De,(D6,(De,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D6,(De,D4))))) (D0,(D1,(De,(D6,(De,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D6,(Df,De))))) (D0,(D1,(De,(D6,(Df,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D7,(Df,D0))))) (D0,(D1,(De,(D7,(Df,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D7,(De,Dd))))) (D0,(D1,(De,(D7,(De,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D7,(De,D8))))) (D0,(D1,(De,(D7,(De,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D8,(D0,D0))))) (D0,(D1,(De,(D8,(Dc,D4))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D5,Df))))) (D0,(D1,(De,(De,(D5,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D4,D2))))) (D0,(D1,(De,(De,(D4,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D2,D7))))) (D0,(D1,(De,(De,(D2,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D0,D5))))) (D0,(D1,(De,(De,(D1,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D0,D0))))) (D0,(D1,(De,(De,(D0,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D9,(D4,Db))))) (D0,(D1,(De,(D9,(D4,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D2,D4))))) (D0,(D1,(De,(De,(D2,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D2,D1))))) (D0,(D1,(De,(De,(D2,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D3,D9))))) (D0,(D1,(De,(De,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D3,D4))))) (D0,(D1,(De,(De,(D3,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D2,D9))))) (D0,(D1,(De,(De,(D3,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D3,Db))))) (D0,(D1,(De,(De,(D3,Db))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D5,D4))))) (D0,(D1,(De,(De,(D5,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D4,Db))))) (D0,(D1,(De,(De,(D4,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D4,D9))))) (D0,(D1,(De,(De,(D4,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D4,D7))))) (D0,(D1,(De,(De,(D4,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D5,D1))))) (D0,(D1,(De,(De,(D5,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D4,Dd))))) (D0,(D1,(De,(De,(D4,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D5,Db))))) (D0,(D1,(De,(De,(D5,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D5,D9))))) (D0,(D1,(De,(De,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D5,D7))))) (D0,(D1,(De,(De,(D5,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D5,Dd))))) (D0,(D1,(De,(De,(D5,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(Da,D5))))) (D0,(D1,(De,(De,(Da,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D7,D9))))) (D0,(D1,(De,(De,(D7,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D6,D7))))) (D0,(D1,(De,(De,(D6,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D6,D4))))) (D0,(D1,(De,(De,(D6,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D6,D1))))) (D0,(D1,(De,(De,(D6,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D7,D4))))) (D0,(D1,(De,(De,(D7,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D6,Dc))))) (D0,(D1,(De,(De,(D7,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D8,Db))))) (D0,(D1,(De,(De,(D9,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D8,D0))))) (D0,(D1,(De,(De,(D8,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D7,De))))) (D0,(D1,(De,(De,(D7,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(Da,D1))))) (D0,(D1,(De,(De,(Da,D3))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D2,(Dc,(De,(Db,D0))))) (D0,(D2,(De,(Db,(De,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D2,(Da,(D7,(D0,D0))))) (D0,(D2,(Db,(D8,(D1,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D2,(D0,(D0,(D0,D0))))) (D0,(D2,(Da,(D6,(Dd,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(Da,Db))))) (D0,(D1,(De,(De,(Db,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D2,(Db,(D8,(D2,D0))))) (D0,(D2,(Dc,(De,(Da,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D3,(D0,(D0,(D0,D0))))) (D0,(D3,(D1,(D3,(D4,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D2,(Df,(D8,(D0,D0))))) (D0,(D2,(Df,(Da,(D1,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D2,(De,(Db,(Df,D0))))) (D0,(D2,(De,(De,(D5,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D3,(D1,(D3,(D5,D0))))) (D0,(D3,(D3,(D4,(D7,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  end)
  end)
  end)
  end)
  end)
  end)
  end).


Definition is_xid_start (x : utf8_codepoint) : bool :=
  match x with
  | ascii b =>
    (* a-z or A-Z *)
    (byte_leb "a" b && byte_leb b "z") ||
    (byte_leb "A" b && byte_leb b "Z")
  | codepoint u v w x y z => is_xid_start' u v w x y z
  end.



(* XID_Continue property *)
Timeout 5 Definition is_xid_continue' (u v w x y z : hex_digit) : bool :=
  if negb (hex_eqb u D0) then false else (* No code points over U+0e01ef *)
  let c := (u,(v,(w,(x,(y,z))))) in
  (match compare_range c (D0,(D0,(Df,(Db,(D3,D8))))) (D0,(D0,(Df,(Db,(D3,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(D4,D9))))) (D0,(D0,(D0,(Df,(D6,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(De,D6))))) (D0,(D0,(D0,(Da,(De,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D6,D0))))) (D0,(D0,(D0,(D8,(D6,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D4,(D8,Da))))) (D0,(D0,(D0,(D5,(D2,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D2,(De,D0))))) (D0,(D0,(D0,(D2,(De,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Db,D7))))) (D0,(D0,(D0,(D0,(Db,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(D6,D1))))) (D0,(D0,(D0,(D0,(D7,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(D4,D1))))) (D0,(D0,(D0,(D0,(D5,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(D3,D0))))) (D0,(D0,(D0,(D0,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D0,(D5,Df))))) (D0,(D0,(D0,(D0,(D5,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D0,(Db,D5))))) (D0,(D0,(D0,(D0,(Db,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Da,Da))))) (D0,(D0,(D0,(D0,(Da,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D0,(Dd,D8))))) (D0,(D0,(D0,(D0,(Df,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Dc,D0))))) (D0,(D0,(D0,(D0,(Dd,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Db,Da))))) (D0,(D0,(D0,(D0,(Db,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D2,(Dc,D6))))) (D0,(D0,(D0,(D2,(Dd,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D0,(Df,D8))))) (D0,(D0,(D0,(D2,(Dc,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D3,(D8,D6))))) (D0,(D0,(D0,(D3,(D8,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(D7,D6))))) (D0,(D0,(D0,(D3,(D7,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D2,(De,De))))) (D0,(D0,(D0,(D2,(De,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D2,(De,Dc))))) (D0,(D0,(D0,(D2,(De,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D3,(D0,D0))))) (D0,(D0,(D0,(D3,(D7,D4))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D3,(D7,Df))))) (D0,(D0,(D0,(D3,(D7,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(D7,Db))))) (D0,(D0,(D0,(D3,(D7,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D3,(Da,D3))))) (D0,(D0,(D0,(D3,(Df,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(D8,De))))) (D0,(D0,(D0,(D3,(Da,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(D8,Dc))))) (D0,(D0,(D0,(D3,(D8,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D4,(D8,D3))))) (D0,(D0,(D0,(D4,(D8,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D3,(Df,D7))))) (D0,(D0,(D0,(D4,(D8,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D6,(D6,De))))) (D0,(D0,(D0,(D6,(Dd,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(Dc,D4))))) (D0,(D0,(D0,(D5,(Dc,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(D9,D1))))) (D0,(D0,(D0,(D5,(Db,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(D5,D9))))) (D0,(D0,(D0,(D5,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(D3,D1))))) (D0,(D0,(D0,(D5,(D5,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D5,(D6,D0))))) (D0,(D0,(D0,(D5,(D8,D8))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D5,(Dc,D1))))) (D0,(D0,(D0,(D5,(Dc,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(Db,Df))))) (D0,(D0,(D0,(D5,(Db,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D5,(De,Df))))) (D0,(D0,(D0,(D5,(Df,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(Dd,D0))))) (D0,(D0,(D0,(D5,(De,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D5,(Dc,D7))))) (D0,(D0,(D0,(D5,(Dc,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D6,(D2,D0))))) (D0,(D0,(D0,(D6,(D6,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(D1,D0))))) (D0,(D0,(D0,(D6,(D1,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D7,(D4,Dd))))) (D0,(D0,(D0,(D7,(Db,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(De,Da))))) (D0,(D0,(D0,(D6,(Df,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(Dd,Df))))) (D0,(D0,(D0,(D6,(De,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(Dd,D5))))) (D0,(D0,(D0,(D6,(Dd,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D7,(D1,D0))))) (D0,(D0,(D0,(D7,(D4,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D6,(Df,Df))))) (D0,(D0,(D0,(D6,(Df,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D7,(Df,Dd))))) (D0,(D0,(D0,(D7,(Df,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D7,(Df,Da))))) (D0,(D0,(D0,(D7,(Df,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D7,(Dc,D0))))) (D0,(D0,(D0,(D7,(Df,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D8,(D4,D0))))) (D0,(D0,(D0,(D8,(D5,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D0,D0))))) (D0,(D0,(D0,(D8,(D2,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D1,D3))))) (D0,(D0,(D0,(Da,(D2,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Db,Dc))))) (D0,(D0,(D0,(D9,(Dc,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(D8,D5))))) (D0,(D0,(D0,(D9,(D8,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(De,D3))))) (D0,(D0,(D0,(D9,(D6,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D8,D9))))) (D0,(D0,(D0,(D8,(D8,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D8,(D7,D0))))) (D0,(D0,(D0,(D8,(D8,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D8,(D9,D7))))) (D0,(D0,(D0,(D8,(De,D1))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(D7,D1))))) (D0,(D0,(D0,(D9,(D8,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(D6,D6))))) (D0,(D0,(D0,(D9,(D6,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(Da,Da))))) (D0,(D0,(D0,(D9,(Db,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(D9,D3))))) (D0,(D0,(D0,(D9,(Da,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(D8,Df))))) (D0,(D0,(D0,(D9,(D9,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(Db,D6))))) (D0,(D0,(D0,(D9,(Db,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Db,D2))))) (D0,(D0,(D0,(D9,(Db,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(De,D6))))) (D0,(D0,(D0,(D9,(Df,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Dd,D7))))) (D0,(D0,(D0,(D9,(Dd,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Dc,Db))))) (D0,(D0,(D0,(D9,(Dc,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Dc,D7))))) (D0,(D0,(D0,(D9,(Dc,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(D9,(Dd,Df))))) (D0,(D0,(D0,(D9,(De,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Dd,Dc))))) (D0,(D0,(D0,(D9,(Dd,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D0,D1))))) (D0,(D0,(D0,(Da,(D0,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Df,De))))) (D0,(D0,(D0,(D9,(Df,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(D9,(Df,Dc))))) (D0,(D0,(D0,(D9,(Df,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D0,Df))))) (D0,(D0,(D0,(Da,(D1,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D0,D5))))) (D0,(D0,(D0,(Da,(D0,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D8,D1))))) (D0,(D0,(D0,(Da,(D8,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D4,D7))))) (D0,(D0,(D0,(Da,(D4,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D3,D8))))) (D0,(D0,(D0,(Da,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D3,D2))))) (D0,(D0,(D0,(Da,(D3,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D2,Da))))) (D0,(D0,(D0,(Da,(D3,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D3,D5))))) (D0,(D0,(D0,(Da,(D3,D6))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D3,De))))) (D0,(D0,(D0,(Da,(D4,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D3,Dc))))) (D0,(D0,(D0,(Da,(D3,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D5,D9))))) (D0,(D0,(D0,(Da,(D5,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D5,D1))))) (D0,(D0,(D0,(Da,(D5,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D4,Db))))) (D0,(D0,(D0,(Da,(D4,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(D6,D6))))) (D0,(D0,(D0,(Da,(D7,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D5,De))))) (D0,(D0,(D0,(Da,(D5,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(Db,D5))))) (D0,(D0,(D0,(Da,(Db,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D9,D3))))) (D0,(D0,(D0,(Da,(Da,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D8,Df))))) (D0,(D0,(D0,(Da,(D9,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(D8,D5))))) (D0,(D0,(D0,(Da,(D8,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(Db,D2))))) (D0,(D0,(D0,(Da,(Db,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(Da,Da))))) (D0,(D0,(D0,(Da,(Db,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(Dc,Db))))) (D0,(D0,(D0,(Da,(Dc,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(Dc,D7))))) (D0,(D0,(D0,(Da,(Dc,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(Db,Dc))))) (D0,(D0,(D0,(Da,(Dc,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Da,(De,D0))))) (D0,(D0,(D0,(Da,(De,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(Dd,D0))))) (D0,(D0,(D0,(Da,(Dd,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(Db,Dc))))) (D0,(D0,(D0,(Dc,(Dc,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(Da,De))))) (D0,(D0,(D0,(Db,(Db,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D5,Dc))))) (D0,(D0,(D0,(Db,(D5,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D3,D2))))) (D0,(D0,(D0,(Db,(D3,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D0,Df))))) (D0,(D0,(D0,(Db,(D1,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D0,D1))))) (D0,(D0,(D0,(Db,(D0,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Da,(Df,D9))))) (D0,(D0,(D0,(Da,(Df,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D0,D5))))) (D0,(D0,(D0,(Db,(D0,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D2,Da))))) (D0,(D0,(D0,(Db,(D3,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D1,D3))))) (D0,(D0,(D0,(Db,(D2,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D4,D7))))) (D0,(D0,(D0,(Db,(D4,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D3,Dc))))) (D0,(D0,(D0,(Db,(D4,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D3,D5))))) (D0,(D0,(D0,(Db,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D5,D5))))) (D0,(D0,(D0,(Db,(D5,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D4,Db))))) (D0,(D0,(D0,(Db,(D4,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D9,D2))))) (D0,(D0,(D0,(Db,(D9,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D8,D2))))) (D0,(D0,(D0,(Db,(D8,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D6,D6))))) (D0,(D0,(D0,(Db,(D6,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D5,Df))))) (D0,(D0,(D0,(Db,(D6,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D7,D1))))) (D0,(D0,(D0,(Db,(D7,D1))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D8,De))))) (D0,(D0,(D0,(Db,(D9,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D8,D5))))) (D0,(D0,(D0,(Db,(D8,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(D9,De))))) (D0,(D0,(D0,(Db,(D9,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D9,Dc))))) (D0,(D0,(D0,(Db,(D9,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(D9,D9))))) (D0,(D0,(D0,(Db,(D9,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(Da,D8))))) (D0,(D0,(D0,(Db,(Da,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(Da,D3))))) (D0,(D0,(D0,(Db,(Da,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D4,Da))))) (D0,(D0,(D0,(Dc,(D4,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D0,D0))))) (D0,(D0,(D0,(Dc,(D0,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(Dd,D0))))) (D0,(D0,(D0,(Db,(Dd,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(Dc,D6))))) (D0,(D0,(D0,(Db,(Dc,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(Db,De))))) (D0,(D0,(D0,(Db,(Dc,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(Dc,Da))))) (D0,(D0,(D0,(Db,(Dc,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Db,(De,D6))))) (D0,(D0,(D0,(Db,(De,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Db,(Dd,D7))))) (D0,(D0,(D0,(Db,(Dd,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D2,Da))))) (D0,(D0,(D0,(Dc,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D1,D2))))) (D0,(D0,(D0,(Dc,(D2,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D0,De))))) (D0,(D0,(D0,(Dc,(D1,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D4,D6))))) (D0,(D0,(D0,(Dc,(D4,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D3,Dc))))) (D0,(D0,(D0,(Dc,(D4,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D8,D0))))) (D0,(D0,(D0,(Dc,(D8,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D5,Dc))))) (D0,(D0,(D0,(Dc,(D5,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D5,D8))))) (D0,(D0,(D0,(Dc,(D5,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D5,D5))))) (D0,(D0,(D0,(Dc,(D5,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D6,D6))))) (D0,(D0,(D0,(Dc,(D6,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D6,D0))))) (D0,(D0,(D0,(Dc,(D6,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(D9,D2))))) (D0,(D0,(D0,(Dc,(Da,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D8,De))))) (D0,(D0,(D0,(Dc,(D9,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(D8,D5))))) (D0,(D0,(D0,(Dc,(D8,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(Db,D5))))) (D0,(D0,(D0,(Dc,(Db,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(Da,Da))))) (D0,(D0,(D0,(Dc,(Db,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(Dd,D6))))) (D0,(D0,(D0,(Dd,(Dd,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D5,D4))))) (D0,(D0,(D0,(Dd,(D5,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(Df,D1))))) (D0,(D0,(D0,(Dc,(Df,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(Dd,Dc))))) (D0,(D0,(D0,(Dc,(Dd,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(Dc,Da))))) (D0,(D0,(D0,(Dc,(Dc,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(Dc,D6))))) (D0,(D0,(D0,(Dc,(Dc,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(Dd,D5))))) (D0,(D0,(D0,(Dc,(Dd,D6))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dc,(De,D6))))) (D0,(D0,(D0,(Dc,(De,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dc,(De,D0))))) (D0,(D0,(D0,(Dc,(De,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(D1,D2))))) (D0,(D0,(D0,(Dd,(D4,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D0,De))))) (D0,(D0,(D0,(Dd,(D1,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D0,D0))))) (D0,(D0,(D0,(Dd,(D0,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(D4,Da))))) (D0,(D0,(D0,(Dd,(D4,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D4,D6))))) (D0,(D0,(D0,(Dd,(D4,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(D9,Da))))) (D0,(D0,(D0,(Dd,(Db,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D7,Da))))) (D0,(D0,(D0,(Dd,(D7,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D6,D6))))) (D0,(D0,(D0,(Dd,(D6,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D5,Df))))) (D0,(D0,(D0,(Dd,(D6,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(D8,D5))))) (D0,(D0,(D0,(Dd,(D9,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(D8,D1))))) (D0,(D0,(D0,(Dd,(D8,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(Dc,D0))))) (D0,(D0,(D0,(Dd,(Dc,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(Db,Dd))))) (D0,(D0,(D0,(Dd,(Db,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(Db,D3))))) (D0,(D0,(D0,(Dd,(Db,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(Dc,Df))))) (D0,(D0,(D0,(Dd,(Dd,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(Dc,Da))))) (D0,(D0,(D0,(Dd,(Dc,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(De,(Dc,D0))))) (D0,(D0,(D0,(De,(Dc,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D8,D1))))) (D0,(D0,(D0,(De,(D8,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D0,D1))))) (D0,(D0,(D0,(De,(D3,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(De,D6))))) (D0,(D0,(D0,(Dd,(De,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Dd,(Dd,D8))))) (D0,(D0,(D0,(Dd,(Dd,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Dd,(Df,D2))))) (D0,(D0,(D0,(Dd,(Df,D3))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(De,(D5,D0))))) (D0,(D0,(D0,(De,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D4,D0))))) (D0,(D0,(D0,(De,(D4,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(De,(D8,Dc))))) (D0,(D0,(D0,(De,(Da,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D8,D6))))) (D0,(D0,(D0,(De,(D8,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(D8,D4))))) (D0,(D0,(D0,(De,(D8,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(De,(Da,D7))))) (D0,(D0,(D0,(De,(Db,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(Da,D5))))) (D0,(D0,(D0,(De,(Da,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Df,(D1,D8))))) (D0,(D0,(D0,(Df,(D1,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(Dd,D0))))) (D0,(D0,(D0,(De,(Dd,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(Dc,D8))))) (D0,(D0,(D0,(De,(Dc,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(Dc,D6))))) (D0,(D0,(D0,(De,(Dc,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Df,(D0,D0))))) (D0,(D0,(D0,(Df,(D0,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(De,(Dd,Dc))))) (D0,(D0,(D0,(De,(Dd,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Df,(D3,D7))))) (D0,(D0,(D0,(Df,(D3,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(D3,D5))))) (D0,(D0,(D0,(Df,(D3,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(D2,D0))))) (D0,(D0,(D0,(Df,(D2,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Df,(D3,De))))) (D0,(D0,(D0,(Df,(D4,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(D3,D9))))) (D0,(D0,(D0,(Df,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D0,(D3,Df))))) (D0,(D0,(D2,(D0,(D4,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D8,(Db,D0))))) (D0,(D0,(D1,(D8,(Df,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D3,(D1,D8))))) (D0,(D0,(D1,(D3,(D5,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D5,D0))))) (D0,(D0,(D1,(D2,(D5,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(Da,D0))))) (D0,(D0,(D1,(D0,(Dc,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(Dc,D6))))) (D0,(D0,(D0,(Df,(Dc,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(D8,D6))))) (D0,(D0,(D0,(Df,(D9,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D0,(Df,(D7,D1))))) (D0,(D0,(D0,(Df,(D8,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D0,(Df,(D9,D9))))) (D0,(D0,(D0,(Df,(Db,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D0,(D5,D0))))) (D0,(D0,(D1,(D0,(D9,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(D0,D0))))) (D0,(D0,(D1,(D0,(D4,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D0,(Dd,D0))))) (D0,(D0,(D1,(D0,(Df,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(Dc,Dd))))) (D0,(D0,(D1,(D0,(Dc,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(Dc,D7))))) (D0,(D0,(D1,(D0,(Dc,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D2,(D4,Da))))) (D0,(D0,(D1,(D2,(D4,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D0,(Df,Dc))))) (D0,(D0,(D1,(D2,(D4,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D2,(Db,D8))))) (D0,(D0,(D1,(D2,(Db,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D8,Da))))) (D0,(D0,(D1,(D2,(D8,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D5,Da))))) (D0,(D0,(D1,(D2,(D5,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D5,D8))))) (D0,(D0,(D1,(D2,(D5,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D2,(D6,D0))))) (D0,(D0,(D1,(D2,(D8,D8))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D2,(Db,D2))))) (D0,(D0,(D1,(D2,(Db,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(D9,D0))))) (D0,(D0,(D1,(D2,(Db,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D2,(Dc,D8))))) (D0,(D0,(D1,(D2,(Dd,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(Dc,D2))))) (D0,(D0,(D1,(D2,(Dc,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(Dc,D0))))) (D0,(D0,(D1,(D2,(Dc,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D3,(D1,D2))))) (D0,(D0,(D1,(D3,(D1,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D2,(Dd,D8))))) (D0,(D0,(D1,(D3,(D1,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D7,(D4,D0))))) (D0,(D0,(D1,(D7,(D5,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D6,(D6,Df))))) (D0,(D0,(D1,(D6,(D7,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D3,(Da,D0))))) (D0,(D0,(D1,(D3,(Df,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D3,(D6,D9))))) (D0,(D0,(D1,(D3,(D7,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D3,(D5,Dd))))) (D0,(D0,(D1,(D3,(D5,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D3,(D8,D0))))) (D0,(D0,(D1,(D3,(D8,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D4,(D0,D1))))) (D0,(D0,(D1,(D6,(D6,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D3,(Df,D8))))) (D0,(D0,(D1,(D3,(Df,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D6,(De,De))))) (D0,(D0,(D1,(D6,(Df,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D6,(Da,D0))))) (D0,(D0,(D1,(D6,(De,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D6,(D8,D1))))) (D0,(D0,(D1,(D6,(D9,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D7,(D1,Df))))) (D0,(D0,(D1,(D7,(D3,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D0,D0))))) (D0,(D0,(D1,(D7,(D1,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D7,(Dd,Dc))))) (D0,(D0,(D1,(D7,(Dd,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D7,D2))))) (D0,(D0,(D1,(D7,(D7,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D6,De))))) (D0,(D0,(D1,(D7,(D7,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D6,D0))))) (D0,(D0,(D1,(D7,(D6,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D7,(Dd,D7))))) (D0,(D0,(D1,(D7,(Dd,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(D8,D0))))) (D0,(D0,(D1,(D7,(Dd,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D8,(D0,Df))))) (D0,(D0,(D1,(D8,(D1,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D8,(D0,Db))))) (D0,(D0,(D1,(D8,(D0,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D7,(De,D0))))) (D0,(D0,(D1,(D7,(De,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D8,(D8,D0))))) (D0,(D0,(D1,(D8,(Da,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D8,(D2,D0))))) (D0,(D0,(D1,(D8,(D7,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Dc,(D8,D0))))) (D0,(D0,(D1,(Dc,(D8,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Da,(D9,D0))))) (D0,(D0,(D1,(Da,(D9,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D9,(Db,D0))))) (D0,(D0,(D1,(D9,(Dc,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D9,(D4,D6))))) (D0,(D0,(D1,(D9,(D6,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D9,(D2,D0))))) (D0,(D0,(D1,(D9,(D2,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D9,(D0,D0))))) (D0,(D0,(D1,(D9,(D1,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D9,(D3,D0))))) (D0,(D0,(D1,(D9,(D3,Db))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(D9,(D8,D0))))) (D0,(D0,(D1,(D9,(Da,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D9,(D7,D0))))) (D0,(D0,(D1,(D9,(D7,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Da,(D2,D0))))) (D0,(D0,(D1,(Da,(D5,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Da,(D0,D0))))) (D0,(D0,(D1,(Da,(D1,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(D9,(Dd,D0))))) (D0,(D0,(D1,(D9,(Dd,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Da,(D7,Df))))) (D0,(D0,(D1,(Da,(D8,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Da,(D6,D0))))) (D0,(D0,(D1,(Da,(D7,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Db,(D5,D0))))) (D0,(D0,(D1,(Db,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Da,(Db,Df))))) (D0,(D0,(D1,(Da,(Dd,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Da,(Db,D0))))) (D0,(D0,(D1,(Da,(Db,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Da,(Da,D7))))) (D0,(D0,(D1,(Da,(Da,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Db,(D0,D0))))) (D0,(D0,(D1,(Db,(D4,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Da,(De,D0))))) (D0,(D0,(D1,(Da,(De,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Dc,(D0,D0))))) (D0,(D0,(D1,(Dc,(D3,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Db,(D8,D0))))) (D0,(D0,(D1,(Db,(Df,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Db,(D6,Db))))) (D0,(D0,(D1,(Db,(D7,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Dc,(D4,Dd))))) (D0,(D0,(D1,(Dc,(D7,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(D4,D0))))) (D0,(D0,(D1,(Dc,(D4,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(D5,Df))))) (D0,(D0,(D1,(Df,(D7,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D2,D0))))) (D0,(D0,(D1,(Df,(D4,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(Dd,D4))))) (D0,(D0,(D1,(Dc,(Df,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(Db,Dd))))) (D0,(D0,(D1,(Dc,(Db,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dc,(D9,D0))))) (D0,(D0,(D1,(Dc,(Db,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Dc,(Dd,D0))))) (D0,(D0,(D1,(Dc,(Dd,D2))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(D1,D8))))) (D0,(D0,(D1,(Df,(D1,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Dd,(D0,D0))))) (D0,(D0,(D1,(Df,(D1,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(D5,D9))))) (D0,(D0,(D1,(Df,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D5,D0))))) (D0,(D0,(D1,(Df,(D5,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D4,D8))))) (D0,(D0,(D1,(Df,(D4,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(D5,Dd))))) (D0,(D0,(D1,(Df,(D5,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D5,Db))))) (D0,(D0,(D1,(Df,(D5,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(Dd,D0))))) (D0,(D0,(D1,(Df,(Dd,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Db,De))))) (D0,(D0,(D1,(Df,(Db,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Db,D6))))) (D0,(D0,(D1,(Df,(Db,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(D8,D0))))) (D0,(D0,(D1,(Df,(Db,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(Dc,D6))))) (D0,(D0,(D1,(Df,(Dc,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Dc,D2))))) (D0,(D0,(D1,(Df,(Dc,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D1,(Df,(Df,D2))))) (D0,(D0,(D1,(Df,(Df,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(De,D0))))) (D0,(D0,(D1,(Df,(De,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Dd,D6))))) (D0,(D0,(D1,(Df,(Dd,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D0,(D0,Dc))))) (D0,(D0,(D2,(D0,(D0,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D1,(Df,(Df,D6))))) (D0,(D0,(D1,(Df,(Df,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D4,(De,(D0,D0))))) (D0,(D0,(Da,(D4,(D8,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(D3,D0))))) (D0,(D0,(D2,(Dd,(D6,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D2,D4))))) (D0,(D0,(D2,(D1,(D2,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D0,(De,D5))))) (D0,(D0,(D2,(D0,(Df,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D0,(D9,D0))))) (D0,(D0,(D2,(D0,(D9,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D0,(D7,D1))))) (D0,(D0,(D2,(D0,(D7,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D0,(D5,D4))))) (D0,(D0,(D2,(D0,(D5,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D0,(D7,Df))))) (D0,(D0,(D2,(D0,(D7,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D0,(De,D1))))) (D0,(D0,(D2,(D0,(De,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D0,(Dd,D0))))) (D0,(D0,(D2,(D0,(Dd,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D0,Da))))) (D0,(D0,(D2,(D1,(D1,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D0,D7))))) (D0,(D0,(D2,(D1,(D0,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D0,D2))))) (D0,(D0,(D2,(D1,(D0,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D1,D8))))) (D0,(D0,(D2,(D1,(D1,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D1,D5))))) (D0,(D0,(D2,(D1,(D1,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D6,D0))))) (D0,(D0,(D2,(D1,(D8,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D3,Dc))))) (D0,(D0,(D2,(D1,(D3,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D2,D8))))) (D0,(D0,(D2,(D1,(D2,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D2,D6))))) (D0,(D0,(D2,(D1,(D2,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D2,Da))))) (D0,(D0,(D2,(D1,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(D1,(D4,De))))) (D0,(D0,(D2,(D1,(D4,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(D1,(D4,D5))))) (D0,(D0,(D2,(D1,(D4,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dd,(D0,D0))))) (D0,(D0,(D2,(Dd,(D2,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dc,(De,Db))))) (D0,(D0,(D2,(Dc,(Df,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dc,(D0,D0))))) (D0,(D0,(D2,(Dc,(De,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dd,(D2,Dd))))) (D0,(D0,(D2,(Dd,(D2,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(D2,D7))))) (D0,(D0,(D2,(Dd,(D2,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D0,(D2,D1))))) (D0,(D0,(D3,(D0,(D2,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Dc,D0))))) (D0,(D0,(D2,(Dd,(Dc,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Da,D8))))) (D0,(D0,(D2,(Dd,(Da,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(D7,Df))))) (D0,(D0,(D2,(Dd,(D9,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(D6,Df))))) (D0,(D0,(D2,(Dd,(D6,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dd,(Da,D0))))) (D0,(D0,(D2,(Dd,(Da,D6))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dd,(Db,D8))))) (D0,(D0,(D2,(Dd,(Db,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Db,D0))))) (D0,(D0,(D2,(Dd,(Db,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D2,(Dd,(Dd,D8))))) (D0,(D0,(D2,(Dd,(Dd,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Dd,D0))))) (D0,(D0,(D2,(Dd,(Dd,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(Dc,D8))))) (D0,(D0,(D2,(Dd,(Dc,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D0,(D0,D5))))) (D0,(D0,(D3,(D0,(D0,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D2,(Dd,(De,D0))))) (D0,(D0,(D2,(Dd,(Df,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D0,(Da,D1))))) (D0,(D0,(D3,(D0,(Df,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D0,(D4,D1))))) (D0,(D0,(D3,(D0,(D9,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D0,(D3,D8))))) (D0,(D0,(D3,(D0,(D3,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D0,(D3,D1))))) (D0,(D0,(D3,(D0,(D3,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D0,(D9,Dd))))) (D0,(D0,(D3,(D0,(D9,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D0,(D9,D9))))) (D0,(D0,(D3,(D0,(D9,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D1,(Da,D0))))) (D0,(D0,(D3,(D1,(Db,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D1,(D3,D1))))) (D0,(D0,(D3,(D1,(D8,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D1,(D0,D5))))) (D0,(D0,(D3,(D1,(D2,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(D3,(D4,(D0,D0))))) (D0,(D0,(D4,(Dd,(Db,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(D3,(D1,(Df,D0))))) (D0,(D0,(D3,(D1,(Df,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Da,(D5,D0))))) (D0,(D0,(Da,(Da,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(D8,D0))))) (D0,(D0,(Da,(D8,(Dc,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D7,(D1,D7))))) (D0,(D0,(Da,(D7,(D1,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D6,(D4,D0))))) (D0,(D0,(Da,(D6,(D6,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D5,(D0,D0))))) (D0,(D0,(Da,(D6,(D0,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D4,(Dd,D0))))) (D0,(D0,(Da,(D4,(Df,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D6,(D1,D0))))) (D0,(D0,(Da,(D6,(D2,Db))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D6,(D7,Df))))) (D0,(D0,(Da,(D6,(Df,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D6,(D7,D4))))) (D0,(D0,(Da,(D6,(D7,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D7,(Df,D1))))) (D0,(D0,(Da,(D8,(D2,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D7,(D8,Db))))) (D0,(D0,(Da,(D7,(Dd,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D7,(D2,D2))))) (D0,(D0,(Da,(D7,(D8,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D8,(D4,D0))))) (D0,(D0,(Da,(D8,(D7,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(D2,Dc))))) (D0,(D0,(Da,(D8,(D2,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D9,(D6,D0))))) (D0,(D0,(Da,(D9,(D7,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(Df,Db))))) (D0,(D0,(Da,(D8,(Df,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(De,D0))))) (D0,(D0,(Da,(D8,(Df,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(Dd,D0))))) (D0,(D0,(Da,(D8,(Dd,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D9,(D3,D0))))) (D0,(D0,(Da,(D9,(D5,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D8,(Df,Dd))))) (D0,(D0,(Da,(D9,(D2,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(D9,(De,D0))))) (D0,(D0,(Da,(D9,(Df,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D9,(Dc,Df))))) (D0,(D0,(Da,(D9,(Dd,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(D9,(D8,D0))))) (D0,(D0,(Da,(D9,(Dc,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Da,(D4,D0))))) (D0,(D0,(Da,(Da,(D4,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(D0,D0))))) (D0,(D0,(Da,(Da,(D3,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Db,(D7,D0))))) (D0,(D0,(Da,(Db,(De,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Db,(D0,D9))))) (D0,(D0,(Da,(Db,(D0,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(De,D0))))) (D0,(D0,(Da,(Da,(De,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(D7,Da))))) (D0,(D0,(Da,(Da,(Dc,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(D6,D0))))) (D0,(D0,(Da,(Da,(D7,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Da,(Dd,Db))))) (D0,(D0,(Da,(Da,(Dd,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Db,(D0,D1))))) (D0,(D0,(Da,(Db,(D0,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Da,(Df,D2))))) (D0,(D0,(Da,(Da,(Df,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Db,(D2,D8))))) (D0,(D0,(Da,(Db,(D2,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Db,(D2,D0))))) (D0,(D0,(Da,(Db,(D2,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Db,(D1,D1))))) (D0,(D0,(Da,(Db,(D1,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Da,(Db,(D5,Dc))))) (D0,(D0,(Da,(Db,(D6,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Db,(D3,D0))))) (D0,(D0,(Da,(Db,(D5,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(D9,(D0,D0))))) (D0,(D0,(Df,(Da,(D6,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Dc,(D0,D0))))) (D0,(D0,(Dd,(D7,(Da,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Db,(Df,D0))))) (D0,(D0,(Da,(Db,(Df,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Da,(Db,(De,Dc))))) (D0,(D0,(Da,(Db,(De,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Dd,(D7,(Dc,Db))))) (D0,(D0,(Dd,(D7,(Df,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Dd,(D7,(Db,D0))))) (D0,(D0,(Dd,(D7,(Dc,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Db,(D1,D3))))) (D0,(D0,(Df,(Db,(D1,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D0,D0))))) (D0,(D0,(Df,(Db,(D0,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Da,(D7,D0))))) (D0,(D0,(Df,(Da,(Dd,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Db,(D2,Da))))) (D0,(D0,(Df,(Db,(D3,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D1,Dd))))) (D0,(D0,(Df,(Db,(D2,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Da,(D4,D7))))) (D0,(D1,(D1,(Da,(D4,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Dc,(D8,D0))))) (D0,(D1,(D0,(Dc,(Db,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D4,(Db,D0))))) (D0,(D1,(D0,(D4,(Dd,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(Dc,D2))))) (D0,(D0,(Df,(Df,(Dc,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D4,Dd))))) (D0,(D0,(Df,(De,(D4,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Dd,(D5,D0))))) (D0,(D0,(Df,(Dd,(D8,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D4,D6))))) (D0,(D0,(Df,(Db,(Db,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D4,D0))))) (D0,(D0,(Df,(Db,(D4,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(D3,De))))) (D0,(D0,(Df,(Db,(D3,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Db,(D4,D3))))) (D0,(D0,(Df,(Db,(D4,D4))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Dc,(D6,D4))))) (D0,(D0,(Df,(Dd,(D3,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Db,(Dd,D3))))) (D0,(D0,(Df,(Dc,(D5,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(De,(D0,D0))))) (D0,(D0,(Df,(De,(D0,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Dd,(Df,D0))))) (D0,(D0,(Df,(Dd,(Df,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Dd,(D9,D2))))) (D0,(D0,(Df,(Dd,(Dc,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(De,(D3,D3))))) (D0,(D0,(Df,(De,(D3,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D2,D0))))) (D0,(D0,(Df,(De,(D2,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(De,(D7,Df))))) (D0,(D0,(Df,(De,(Df,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,D9))))) (D0,(D0,(Df,(De,(D7,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,D3))))) (D0,(D0,(Df,(De,(D7,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,D1))))) (D0,(D0,(Df,(De,(D7,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(Df,(De,(D7,D7))))) (D0,(D0,(Df,(De,(D7,D7))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(De,(D7,Dd))))) (D0,(D0,(Df,(De,(D7,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(De,(D7,Db))))) (D0,(D0,(Df,(De,(D7,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Df,(D3,Df))))) (D0,(D0,(Df,(Df,(D3,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(D2,D1))))) (D0,(D0,(Df,(Df,(D3,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(D1,D0))))) (D0,(D0,(Df,(Df,(D1,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Df,(D6,D5))))) (D0,(D0,(Df,(Df,(Db,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(D4,D1))))) (D0,(D0,(Df,(Df,(D5,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D2,(D8,D0))))) (D0,(D1,(D0,(D2,(D9,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D0,(D3,Dc))))) (D0,(D1,(D0,(D0,(D3,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D0,(D0,D0))))) (D0,(D1,(D0,(D0,(D0,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(Dd,D2))))) (D0,(D0,(Df,(Df,(Dd,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D0,(Df,(Df,(Dc,Da))))) (D0,(D0,(Df,(Df,(Dc,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D0,(Df,(Df,(Dd,Da))))) (D0,(D0,(Df,(Df,(Dd,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D0,(D2,D8))))) (D0,(D1,(D0,(D0,(D3,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D0,(D0,Dd))))) (D0,(D1,(D0,(D0,(D2,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D0,(D8,D0))))) (D0,(D1,(D0,(D0,(Df,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D0,(D5,D0))))) (D0,(D1,(D0,(D0,(D5,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D0,(D3,Df))))) (D0,(D1,(D0,(D0,(D4,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D1,(Df,Dd))))) (D0,(D1,(D0,(D1,(Df,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D1,(D4,D0))))) (D0,(D1,(D0,(D1,(D7,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D3,(D8,D0))))) (D0,(D1,(D0,(D3,(D9,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D3,(D0,D0))))) (D0,(D1,(D0,(D3,(D1,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D2,(De,D0))))) (D0,(D1,(D0,(D2,(De,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D2,(Da,D0))))) (D0,(D1,(D0,(D2,(Dd,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D3,(D5,D0))))) (D0,(D1,(D0,(D3,(D7,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D3,(D2,Dd))))) (D0,(D1,(D0,(D3,(D4,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D3,(Dd,D1))))) (D0,(D1,(D0,(D3,(Dd,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D3,(Dc,D8))))) (D0,(D1,(D0,(D3,(Dc,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D3,(Da,D0))))) (D0,(D1,(D0,(D3,(Dc,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D4,(Da,D0))))) (D0,(D1,(D0,(D4,(Da,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D4,(D0,D0))))) (D0,(D1,(D0,(D4,(D9,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(D6,D0))))) (D0,(D1,(D0,(D8,(D7,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D6,(D0,D0))))) (D0,(D1,(D0,(D7,(D3,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D9,D4))))) (D0,(D1,(D0,(D5,(D9,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D7,D0))))) (D0,(D1,(D0,(D5,(D7,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D0,D0))))) (D0,(D1,(D0,(D5,(D2,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D4,(Dd,D8))))) (D0,(D1,(D0,(D4,(Df,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D5,(D3,D0))))) (D0,(D1,(D0,(D5,(D6,D3))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D5,(D8,Dc))))) (D0,(D1,(D0,(D5,(D9,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D7,Dc))))) (D0,(D1,(D0,(D5,(D8,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D5,(Db,D3))))) (D0,(D1,(D0,(D5,(Db,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(Da,D3))))) (D0,(D1,(D0,(D5,(Db,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(D9,D7))))) (D0,(D1,(D0,(D5,(Da,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D5,(Dc,D0))))) (D0,(D1,(D0,(D5,(Df,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D5,(Db,Db))))) (D0,(D1,(D0,(D5,(Db,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(D0,D0))))) (D0,(D1,(D0,(D8,(D0,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D7,(D8,D0))))) (D0,(D1,(D0,(D7,(D8,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D7,(D6,D0))))) (D0,(D1,(D0,(D7,(D6,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D7,(D4,D0))))) (D0,(D1,(D0,(D7,(D5,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D7,(Db,D2))))) (D0,(D1,(D0,(D7,(Db,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D7,(D8,D7))))) (D0,(D1,(D0,(D7,(Db,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(D3,D7))))) (D0,(D1,(D0,(D8,(D3,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(D0,Da))))) (D0,(D1,(D0,(D8,(D3,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(D0,D8))))) (D0,(D1,(D0,(D8,(D0,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(D3,Df))))) (D0,(D1,(D0,(D8,(D5,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(D3,Dc))))) (D0,(D1,(D0,(D8,(D3,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Da,(D1,D9))))) (D0,(D1,(D0,(Da,(D3,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D9,(D8,D0))))) (D0,(D1,(D0,(D9,(Db,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D9,(D0,D0))))) (D0,(D1,(D0,(D9,(D1,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(De,D0))))) (D0,(D1,(D0,(D8,(Df,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D8,(D8,D0))))) (D0,(D1,(D0,(D8,(D9,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D8,(Df,D4))))) (D0,(D1,(D0,(D8,(Df,D5))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(D9,(D4,D0))))) (D0,(D1,(D0,(D9,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D9,(D2,D0))))) (D0,(D1,(D0,(D9,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Da,(D0,D5))))) (D0,(D1,(D0,(Da,(D0,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D0,D0))))) (D0,(D1,(D0,(Da,(D0,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(D9,(Db,De))))) (D0,(D1,(D0,(D9,(Db,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Da,(D1,D5))))) (D0,(D1,(D0,(Da,(D1,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D0,Dc))))) (D0,(D1,(D0,(Da,(D1,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Da,(Dc,D9))))) (D0,(D1,(D0,(Da,(De,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D6,D0))))) (D0,(D1,(D0,(Da,(D7,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D3,Df))))) (D0,(D1,(D0,(Da,(D3,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D3,D8))))) (D0,(D1,(D0,(Da,(D3,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Da,(Dc,D0))))) (D0,(D1,(D0,(Da,(Dc,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Da,(D8,D0))))) (D0,(D1,(D0,(Da,(D9,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Db,(D6,D0))))) (D0,(D1,(D0,(Db,(D7,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Db,(D4,D0))))) (D0,(D1,(D0,(Db,(D5,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Db,(D0,D0))))) (D0,(D1,(D0,(Db,(D3,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Dc,(D0,D0))))) (D0,(D1,(D0,(Dc,(D4,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Db,(D8,D0))))) (D0,(D1,(D0,(Db,(D9,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D4,Db))))) (D0,(D1,(D1,(D3,(D4,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(D5,D0))))) (D0,(D1,(D1,(D1,(D7,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Df,(D3,D0))))) (D0,(D1,(D0,(Df,(D5,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(De,(D8,D0))))) (D0,(D1,(D0,(De,(Da,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Dd,(D4,D0))))) (D0,(D1,(D0,(Dd,(D6,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Dd,(D0,D0))))) (D0,(D1,(D0,(Dd,(D2,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Dc,(Dc,D0))))) (D0,(D1,(D0,(Dc,(Df,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Dd,(D3,D0))))) (D0,(D1,(D0,(Dd,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Dd,(D6,Df))))) (D0,(D1,(D0,(Dd,(D8,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Dd,(D6,D9))))) (D0,(D1,(D0,(Dd,(D6,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(De,(Dc,D2))))) (D0,(D1,(D0,(De,(Dc,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(De,(Db,D0))))) (D0,(D1,(D0,(De,(Db,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(De,(Da,Db))))) (D0,(D1,(D0,(De,(Da,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Df,(D2,D7))))) (D0,(D1,(D0,(Df,(D2,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(De,(Df,Da))))) (D0,(D1,(D0,(Df,(D1,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D0,(Dc,D2))))) (D0,(D1,(D1,(D0,(Dc,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D0,(D0,D0))))) (D0,(D1,(D1,(D0,(D4,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Df,(Db,D0))))) (D0,(D1,(D0,(Df,(Dc,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D0,(Df,(D7,D0))))) (D0,(D1,(D0,(Df,(D8,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D0,(Df,(De,D0))))) (D0,(D1,(D0,(Df,(Df,D6))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D0,(D7,Df))))) (D0,(D1,(D1,(D0,(Db,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D0,(D6,D6))))) (D0,(D1,(D1,(D0,(D7,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D1,(D0,D0))))) (D0,(D1,(D1,(D1,(D3,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D0,(Df,D0))))) (D0,(D1,(D1,(D0,(Df,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D0,(Dd,D0))))) (D0,(D1,(D1,(D0,(De,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D1,(D4,D4))))) (D0,(D1,(D1,(D1,(D4,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(D3,D6))))) (D0,(D1,(D1,(D1,(D3,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D2,(D9,Df))))) (D0,(D1,(D1,(D2,(Da,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D1,D3))))) (D0,(D1,(D1,(D2,(D3,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(Dc,De))))) (D0,(D1,(D1,(D1,(Dd,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(D8,D0))))) (D0,(D1,(D1,(D1,(Dc,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(D7,D6))))) (D0,(D1,(D1,(D1,(D7,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D1,(Dc,D9))))) (D0,(D1,(D1,(D1,(Dc,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D2,(D0,D0))))) (D0,(D1,(D1,(D2,(D1,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D1,(Dd,Dc))))) (D0,(D1,(D1,(D1,(Dd,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D2,(D8,D8))))) (D0,(D1,(D1,(D2,(D8,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D8,D0))))) (D0,(D1,(D1,(D2,(D8,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D3,De))))) (D0,(D1,(D1,(D2,(D4,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D2,(D8,Df))))) (D0,(D1,(D1,(D2,(D9,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(D8,Da))))) (D0,(D1,(D1,(D2,(D8,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D1,D3))))) (D0,(D1,(D1,(D3,(D2,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D0,D0))))) (D0,(D1,(D1,(D3,(D0,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(Df,D0))))) (D0,(D1,(D1,(D2,(Df,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D2,(Db,D0))))) (D0,(D1,(D1,(D2,(De,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D0,Df))))) (D0,(D1,(D1,(D3,(D1,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D0,D5))))) (D0,(D1,(D1,(D3,(D0,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D3,D5))))) (D0,(D1,(D1,(D3,(D3,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D3,D2))))) (D0,(D1,(D1,(D3,(D3,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D2,Da))))) (D0,(D1,(D1,(D3,(D3,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D4,D7))))) (D0,(D1,(D1,(D3,(D4,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D3,Db))))) (D0,(D1,(D1,(D3,(D4,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D6,(D0,D0))))) (D0,(D1,(D1,(D6,(D4,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(Dc,D7))))) (D0,(D1,(D1,(D3,(Dc,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D8,Db))))) (D0,(D1,(D1,(D3,(D8,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D6,D6))))) (D0,(D1,(D1,(D3,(D6,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D5,D7))))) (D0,(D1,(D1,(D3,(D5,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D5,D0))))) (D0,(D1,(D1,(D3,(D5,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D5,Dd))))) (D0,(D1,(D1,(D3,(D6,D3))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(D8,D0))))) (D0,(D1,(D1,(D3,(D8,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D7,D0))))) (D0,(D1,(D1,(D3,(D7,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(Db,D7))))) (D0,(D1,(D1,(D3,(Dc,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D9,D0))))) (D0,(D1,(D1,(D3,(Db,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(D8,De))))) (D0,(D1,(D1,(D3,(D8,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D3,(Dc,D5))))) (D0,(D1,(D1,(D3,(Dc,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(Dc,D2))))) (D0,(D1,(D1,(D3,(Dc,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D4,(D8,D0))))) (D0,(D1,(D1,(D4,(Dc,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D4,(D0,D0))))) (D0,(D1,(D1,(D4,(D4,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(De,D1))))) (D0,(D1,(D1,(D3,(De,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D3,(Dc,Dc))))) (D0,(D1,(D1,(D3,(Dd,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D4,(D5,De))))) (D0,(D1,(D1,(D4,(D6,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D4,(D5,D0))))) (D0,(D1,(D1,(D4,(D5,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D5,(D8,D0))))) (D0,(D1,(D1,(D5,(Db,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D4,(Dd,D0))))) (D0,(D1,(D1,(D4,(Dd,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D4,(Dc,D7))))) (D0,(D1,(D1,(D4,(Dc,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D5,(Dd,D8))))) (D0,(D1,(D1,(D5,(Dd,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D5,(Db,D8))))) (D0,(D1,(D1,(D5,(Dc,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D9,(D0,D9))))) (D0,(D1,(D1,(D9,(D0,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D7,(D1,Dd))))) (D0,(D1,(D1,(D7,(D2,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D6,(Dc,D0))))) (D0,(D1,(D1,(D6,(Dc,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D6,(D5,D0))))) (D0,(D1,(D1,(D6,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D6,(D4,D4))))) (D0,(D1,(D1,(D6,(D4,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D6,(D8,D0))))) (D0,(D1,(D1,(D6,(Db,D8))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D7,(D0,D0))))) (D0,(D1,(D1,(D7,(D1,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D6,(Dd,D0))))) (D0,(D1,(D1,(D6,(De,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D8,(D0,D0))))) (D0,(D1,(D1,(D8,(D3,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D7,(D4,D0))))) (D0,(D1,(D1,(D7,(D4,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D7,(D3,D0))))) (D0,(D1,(D1,(D7,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D8,(Df,Df))))) (D0,(D1,(D1,(D9,(D0,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D8,(Da,D0))))) (D0,(D1,(D1,(D8,(De,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D9,(D5,D0))))) (D0,(D1,(D1,(D9,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(D1,D8))))) (D0,(D1,(D1,(D9,(D3,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(D1,D5))))) (D0,(D1,(D1,(D9,(D1,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(D0,Dc))))) (D0,(D1,(D1,(D9,(D1,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D9,(D3,Db))))) (D0,(D1,(D1,(D9,(D4,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(D3,D7))))) (D0,(D1,(D1,(D9,(D3,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(D9,(Dd,Da))))) (D0,(D1,(D1,(D9,(De,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(Da,Da))))) (D0,(D1,(D1,(D9,(Dd,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(Da,D0))))) (D0,(D1,(D1,(D9,(Da,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Da,(D0,D0))))) (D0,(D1,(D1,(Da,(D3,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(D9,(De,D3))))) (D0,(D1,(D1,(D9,(De,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(Db,Dd))))) (D0,(D1,(Dd,(D4,(Dc,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Db,(D0,D0))))) (D0,(D1,(D6,(Db,(D3,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(Da,D0))))) (D0,(D1,(D1,(Dd,(Da,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dc,(Da,D9))))) (D0,(D1,(D1,(Dc,(Db,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dc,(D0,D0))))) (D0,(D1,(D1,(Dc,(D0,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Db,(D6,D0))))) (D0,(D1,(D1,(Db,(D6,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Da,(D9,Dd))))) (D0,(D1,(D1,(Da,(D9,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Da,(D5,D0))))) (D0,(D1,(D1,(Da,(D9,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Da,(Db,D0))))) (D0,(D1,(D1,(Da,(Df,D8))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Db,(Df,D0))))) (D0,(D1,(D1,(Db,(Df,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Db,(Dc,D0))))) (D0,(D1,(D1,(Db,(De,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dc,(D5,D0))))) (D0,(D1,(D1,(Dc,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dc,(D3,D8))))) (D0,(D1,(D1,(Dc,(D4,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dc,(D0,Da))))) (D0,(D1,(D1,(Dc,(D3,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dc,(D9,D2))))) (D0,(D1,(D1,(Dc,(Da,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dc,(D7,D2))))) (D0,(D1,(D1,(Dc,(D8,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dd,(D5,D0))))) (D0,(D1,(D1,(Dd,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D3,Da))))) (D0,(D1,(D1,(Dd,(D3,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D0,D8))))) (D0,(D1,(D1,(Dd,(D0,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D0,D0))))) (D0,(D1,(D1,(Dd,(D0,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dd,(D0,Db))))) (D0,(D1,(D1,(Dd,(D3,D6))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dd,(D3,Df))))) (D0,(D1,(D1,(Dd,(D4,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D3,Dc))))) (D0,(D1,(D1,(Dd,(D3,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dd,(D6,Da))))) (D0,(D1,(D1,(Dd,(D8,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D6,D7))))) (D0,(D1,(D1,(Dd,(D6,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D6,D0))))) (D0,(D1,(D1,(Dd,(D6,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Dd,(D9,D3))))) (D0,(D1,(D1,(Dd,(D9,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(D9,D0))))) (D0,(D1,(D1,(Dd,(D9,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D3,(D0,(D0,D0))))) (D0,(D1,(D3,(D4,(D2,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Df,(D5,D0))))) (D0,(D1,(D1,(Df,(D5,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Df,(D0,D0))))) (D0,(D1,(D1,(Df,(D1,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(De,D0))))) (D0,(D1,(D1,(Dd,(De,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Dd,(Db,D0))))) (D0,(D1,(D1,(Dd,(Dd,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D1,(De,(De,D0))))) (D0,(D1,(D1,(De,(Df,D6))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D1,(Df,(D3,De))))) (D0,(D1,(D1,(Df,(D4,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Df,(D1,D2))))) (D0,(D1,(D1,(Df,(D3,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D2,(D4,(D0,D0))))) (D0,(D1,(D2,(D4,(D6,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D2,(D0,(D0,D0))))) (D0,(D1,(D2,(D3,(D9,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D1,(Df,(Db,D0))))) (D0,(D1,(D1,(Df,(Db,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D2,(Df,(D9,D0))))) (D0,(D1,(D2,(Df,(Df,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D2,(D4,(D8,D0))))) (D0,(D1,(D2,(D5,(D4,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Da,(D4,D0))))) (D0,(D1,(D6,(Da,(D5,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D4,(D4,(D0,D0))))) (D0,(D1,(D4,(D6,(D4,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D3,(D4,(D6,D0))))) (D0,(D1,(D4,(D3,(Df,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D3,(D4,(D4,D0))))) (D0,(D1,(D3,(D4,(D5,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(D8,(D0,D0))))) (D0,(D1,(D6,(Da,(D3,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(D1,(D0,D0))))) (D0,(D1,(D6,(D1,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Da,(Dc,D0))))) (D0,(D1,(D6,(Da,(Dc,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Da,(D7,D0))))) (D0,(D1,(D6,(Da,(Db,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Da,(D6,D0))))) (D0,(D1,(D6,(Da,(D6,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Da,(Df,D0))))) (D0,(D1,(D6,(Da,(Df,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Da,(Dd,D0))))) (D0,(D1,(D6,(Da,(De,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Db,(D1,(D5,D5))))) (D0,(D1,(Db,(D1,(D5,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Df,(De,D0))))) (D0,(D1,(D6,(Df,(De,D1))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(De,(D4,D0))))) (D0,(D1,(D6,(De,(D7,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Db,(D7,Dd))))) (D0,(D1,(D6,(Db,(D8,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Db,(D5,D0))))) (D0,(D1,(D6,(Db,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Db,(D4,D0))))) (D0,(D1,(D6,(Db,(D4,D3))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Db,(D6,D3))))) (D0,(D1,(D6,(Db,(D7,D7))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Dd,(D7,D0))))) (D0,(D1,(D6,(Dd,(D7,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Dd,(D4,D0))))) (D0,(D1,(D6,(Dd,(D6,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Df,(D0,D0))))) (D0,(D1,(D6,(Df,(D4,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(De,(Db,Db))))) (D0,(D1,(D6,(De,(Dd,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(De,(Da,D0))))) (D0,(D1,(D6,(De,(Db,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D6,(Df,(D8,Df))))) (D0,(D1,(D6,(Df,(D9,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Df,(D4,Df))))) (D0,(D1,(D6,(Df,(D8,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Da,(Df,(Df,D0))))) (D0,(D1,(Da,(Df,(Df,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D7,(D0,(D0,D0))))) (D0,(D1,(D8,(Dc,(Dd,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Df,(Df,D0))))) (D0,(D1,(D6,(Df,(Df,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D6,(Df,(De,D3))))) (D0,(D1,(D6,(Df,(De,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(D8,(Dd,(D8,D0))))) (D0,(D1,(D8,(Dd,(Df,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(D8,(Dc,(Df,Df))))) (D0,(D1,(D8,(Dd,(D1,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Db,(D0,(D0,D0))))) (D0,(D1,(Db,(D1,(D2,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Da,(Df,(Df,Dd))))) (D0,(D1,(Da,(Df,(Df,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Da,(Df,(Df,D5))))) (D0,(D1,(Da,(Df,(Df,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Db,(D1,(D5,D0))))) (D0,(D1,(Db,(D1,(D5,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(D1,(D3,D2))))) (D0,(D1,(Db,(D1,(D3,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D1,(D7,Db))))) (D0,(D1,(Dd,(D1,(D8,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(Dc,(D9,Dd))))) (D0,(D1,(Db,(Dc,(D9,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(Dc,(D7,D0))))) (D0,(D1,(Db,(Dc,(D7,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(D1,(D7,D0))))) (D0,(D1,(Db,(D2,(Df,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(D1,(D6,D4))))) (D0,(D1,(Db,(D1,(D6,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(Db,(Dc,(D0,D0))))) (D0,(D1,(Db,(Dc,(D6,Da))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Db,(Dc,(D9,D0))))) (D0,(D1,(Db,(Dc,(D9,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Db,(Dc,(D8,D0))))) (D0,(D1,(Db,(Dc,(D8,D8))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dc,(Df,(D3,D0))))) (D0,(D1,(Dc,(Df,(D4,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dc,(Df,(D0,D0))))) (D0,(D1,(Dc,(Df,(D2,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dc,(Dc,(Df,D0))))) (D0,(D1,(Dc,(Dc,(Df,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D1,(D6,Dd))))) (D0,(D1,(Dd,(D1,(D7,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D1,(D6,D5))))) (D0,(D1,(Dd,(D1,(D6,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(D9,De))))) (D0,(D1,(Dd,(D4,(D9,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D2,(D4,D2))))) (D0,(D1,(Dd,(D2,(D4,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D1,(Da,Da))))) (D0,(D1,(Dd,(D1,(Da,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D1,(D8,D5))))) (D0,(D1,(Dd,(D1,(D8,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(D5,D6))))) (D0,(D1,(Dd,(D4,(D9,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(D0,D0))))) (D0,(D1,(Dd,(D4,(D5,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(Da,D9))))) (D0,(D1,(Dd,(D4,(Da,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(Da,D5))))) (D0,(D1,(Dd,(D4,(Da,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(Da,D2))))) (D0,(D1,(Dd,(D4,(Da,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D4,(Db,Db))))) (D0,(D1,(Dd,(D4,(Db,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(Da,De))))) (D0,(D1,(Dd,(D4,(Db,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D7,(De,D8))))) (D0,(D1,(De,(D7,(De,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(Da,(D7,D5))))) (D0,(D1,(Dd,(Da,(D7,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D6,(Dd,Dc))))) (D0,(D1,(Dd,(D6,(Df,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D4,D0))))) (D0,(D1,(Dd,(D5,(D4,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D1,D6))))) (D0,(D1,(Dd,(D5,(D1,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D0,D7))))) (D0,(D1,(Dd,(D5,(D0,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D4,(Dc,D5))))) (D0,(D1,(Dd,(D5,(D0,D5))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D5,(D0,Dd))))) (D0,(D1,(Dd,(D5,(D1,D4))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D5,(D3,Db))))) (D0,(D1,(Dd,(D5,(D3,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D1,De))))) (D0,(D1,(Dd,(D5,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D5,(D5,D2))))) (D0,(D1,(Dd,(D6,(Da,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D4,Da))))) (D0,(D1,(Dd,(D5,(D5,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D5,(D4,D6))))) (D0,(D1,(Dd,(D5,(D4,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D6,(Dc,D2))))) (D0,(D1,(Dd,(D6,(Dd,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D6,(Da,D8))))) (D0,(D1,(Dd,(D6,(Dc,D0))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D7,(D8,Da))))) (D0,(D1,(Dd,(D7,(Da,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D7,(D3,D6))))) (D0,(D1,(Dd,(D7,(D4,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D7,(D1,D6))))) (D0,(D1,(Dd,(D7,(D3,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D6,(Df,Dc))))) (D0,(D1,(Dd,(D7,(D1,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D7,(D7,D0))))) (D0,(D1,(Dd,(D7,(D8,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D7,(D5,D0))))) (D0,(D1,(Dd,(D7,(D6,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(D7,(Dc,De))))) (D0,(D1,(Dd,(D7,(Df,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D7,(Dc,D4))))) (D0,(D1,(Dd,(D7,(Dc,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(D7,(Da,Da))))) (D0,(D1,(Dd,(D7,(Dc,D2))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(Da,(D3,Db))))) (D0,(D1,(Dd,(Da,(D6,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(Da,(D0,D0))))) (D0,(D1,(Dd,(Da,(D3,D6))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D1,(D0,D0))))) (D0,(D1,(De,(D1,(D2,Dc))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D0,(D0,D8))))) (D0,(D1,(De,(D0,(D1,D8))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(Df,(D0,D0))))) (D0,(D1,(Dd,(Df,(D1,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(Da,(D9,Db))))) (D0,(D1,(Dd,(Da,(D9,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(Da,(D8,D4))))) (D0,(D1,(Dd,(Da,(D8,D4))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(Dd,(Da,(Da,D1))))) (D0,(D1,(Dd,(Da,(Da,Df))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D0,(D0,D0))))) (D0,(D1,(De,(D0,(D0,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Dd,(Df,(D2,D5))))) (D0,(D1,(Dd,(Df,(D2,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D0,(D2,D6))))) (D0,(D1,(De,(D0,(D2,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D0,(D2,D3))))) (D0,(D1,(De,(D0,(D2,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D0,(D1,Db))))) (D0,(D1,(De,(D0,(D2,D1))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D0,(D8,Df))))) (D0,(D1,(De,(D0,(D8,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D0,(D3,D0))))) (D0,(D1,(De,(D0,(D6,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D4,(Dd,D0))))) (D0,(D1,(De,(D4,(Df,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D1,(D4,De))))) (D0,(D1,(De,(D1,(D4,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D1,(D4,D0))))) (D0,(D1,(De,(D1,(D4,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D1,(D3,D0))))) (D0,(D1,(De,(D1,(D3,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D2,(Dc,D0))))) (D0,(D1,(De,(D2,(Df,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D2,(D9,D0))))) (D0,(D1,(De,(D2,(Da,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D6,(De,D0))))) (D0,(D1,(De,(D6,(Df,D5))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D6,(Dc,D0))))) (D0,(D1,(De,(D6,(Dd,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D5,(Dd,D0))))) (D0,(D1,(De,(D5,(Df,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D7,(De,D0))))) (D0,(D1,(De,(D7,(De,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D6,(Df,De))))) (D0,(D1,(De,(D6,(Df,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D5,Db))))) (D0,(D1,(De,(De,(D5,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D3,D4))))) (D0,(D1,(De,(De,(D3,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D0,D0))))) (D0,(D1,(De,(De,(D0,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D8,(Dd,D0))))) (D0,(D1,(De,(D8,(Dd,D6))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D7,(Df,D0))))) (D0,(D1,(De,(D7,(Df,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D7,(De,Dd))))) (D0,(D1,(De,(D7,(De,De))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(De,(D8,(D0,D0))))) (D0,(D1,(De,(D8,(Dc,D4))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(D9,(D5,D0))))) (D0,(D1,(De,(D9,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(D9,(D0,D0))))) (D0,(D1,(De,(D9,(D4,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D2,D4))))) (D0,(D1,(De,(De,(D2,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D2,D1))))) (D0,(D1,(De,(De,(D2,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D0,D5))))) (D0,(D1,(De,(De,(D1,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D2,D9))))) (D0,(D1,(De,(De,(D3,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D2,D7))))) (D0,(D1,(De,(De,(D2,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D4,Db))))) (D0,(D1,(De,(De,(D4,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D4,D2))))) (D0,(D1,(De,(De,(D4,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D3,Db))))) (D0,(D1,(De,(De,(D3,Db))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D3,D9))))) (D0,(D1,(De,(De,(D3,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D4,D9))))) (D0,(D1,(De,(De,(D4,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D4,D7))))) (D0,(D1,(De,(De,(D4,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D5,D4))))) (D0,(D1,(De,(De,(D5,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D5,D1))))) (D0,(D1,(De,(De,(D5,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D4,Dd))))) (D0,(D1,(De,(De,(D4,Df))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D5,D9))))) (D0,(D1,(De,(De,(D5,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D5,D7))))) (D0,(D1,(De,(De,(D5,D7))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(Da,D5))))) (D0,(D1,(De,(De,(Da,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D7,D4))))) (D0,(D1,(De,(De,(D7,D7))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D6,D4))))) (D0,(D1,(De,(De,(D6,D4))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D5,Df))))) (D0,(D1,(De,(De,(D5,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D5,Dd))))) (D0,(D1,(De,(De,(D5,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D6,D1))))) (D0,(D1,(De,(De,(D6,D2))))) with | Eq => true | Gt => false | Lt => false end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D6,Dc))))) (D0,(D1,(De,(De,(D7,D2))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D6,D7))))) (D0,(D1,(De,(De,(D6,Da))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(D8,D0))))) (D0,(D1,(De,(De,(D8,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D7,De))))) (D0,(D1,(De,(De,(D7,De))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D7,D9))))) (D0,(D1,(De,(De,(D7,Dc))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D1,(De,(De,(Da,D1))))) (D0,(D1,(De,(De,(Da,D3))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(D8,Db))))) (D0,(D1,(De,(De,(D9,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  | Lt => (match compare_range c (D0,(D2,(Dc,(De,(Db,D0))))) (D0,(D2,(De,(Db,(De,D0))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D2,(D0,(D0,(D0,D0))))) (D0,(D2,(Da,(D6,(Dd,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(Df,(Db,(Df,D0))))) (D0,(D1,(Df,(Db,(Df,D9))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D1,(De,(De,(Da,Db))))) (D0,(D1,(De,(De,(Db,Db))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(D2,(Db,(D8,(D2,D0))))) (D0,(D2,(Dc,(De,(Da,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D2,(Da,(D7,(D0,D0))))) (D0,(D2,(Db,(D8,(D1,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  | Lt => (match compare_range c (D0,(D3,(D0,(D0,(D0,D0))))) (D0,(D3,(D1,(D3,(D4,Da))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D2,(Df,(D8,(D0,D0))))) (D0,(D2,(Df,(Da,(D1,Dd))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D2,(De,(Db,(Df,D0))))) (D0,(D2,(De,(De,(D5,Dd))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  | Lt => (match compare_range c (D0,(De,(D0,(D1,(D0,D0))))) (D0,(De,(D0,(D1,(De,Df))))) with
  | Eq => true
  | Gt => (match compare_range c (D0,(D3,(D1,(D3,(D5,D0))))) (D0,(D3,(D3,(D4,(D7,D9))))) with | Eq => true | Gt => false | Lt => false end)
  | Lt => false
  end)
  end)
  end)
  end)
  end)
  end)
  end)
  end)
  end).


Definition is_xid_continue (x : utf8_codepoint) : bool :=
  match x with
  | ascii b =>
    (* a-z or A-Z or 0-9 or _ *)
    (byte_leb "a" b && byte_leb b "z") ||
    (byte_leb "A" b && byte_leb b "Z") ||
    (byte_leb "0" b && byte_leb b "9") ||
    (byte_eqb b "_")
  | codepoint u v w x y z => is_xid_continue' u v w x y z
  end.
