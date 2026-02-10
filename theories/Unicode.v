From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From Stdlib Require Import Strings.Byte.
From Stdlib Require Import NArith.BinNat.

Import MRMonadNotation.

Local Open Scope bs_scope.



(* https://www.unicode.org/versions/Unicode17.0.0/ *)

Inductive hex_digit :=
| D0
| D1
| D2
| D3
| D4
| D5
| D6
| D7
| D8
| D9
| Da
| Db
| Dc
| Dd
| De
| Df.

Local Declare Scope bits.
Local Delimit Scope bits with bits.
Local Notation "0" := false : bits.
Local Notation "1" := true : bits.

Definition hex_to_bits (x : hex_digit) : (bool * (bool * (bool * bool))) :=
  match x with
  | D0 => (0, (0, (0, 0)))
  | D1 => (1, (0, (0, 0)))
  | D2 => (0, (1, (0, 0)))
  | D3 => (1, (1, (0, 0)))
  | D4 => (0, (0, (1, 0)))
  | D5 => (1, (0, (1, 0)))
  | D6 => (0, (1, (1, 0)))
  | D7 => (1, (1, (1, 0)))
  | D8 => (0, (0, (0, 1)))
  | D9 => (1, (0, (0, 1)))
  | Da => (0, (1, (0, 1)))
  | Db => (1, (1, (0, 1)))
  | Dc => (0, (0, (1, 1)))
  | Dd => (1, (0, (1, 1)))
  | De => (0, (1, (1, 1)))
  | Df => (1, (1, (1, 1)))
  end%bits.

Definition hex_of_bits (x : (bool * (bool * (bool * bool)))) : hex_digit :=
  match x with
  | (0, (0, (0, 0))) => D0
  | (1, (0, (0, 0))) => D1
  | (0, (1, (0, 0))) => D2
  | (1, (1, (0, 0))) => D3
  | (0, (0, (1, 0))) => D4
  | (1, (0, (1, 0))) => D5
  | (0, (1, (1, 0))) => D6
  | (1, (1, (1, 0))) => D7
  | (0, (0, (0, 1))) => D8
  | (1, (0, (0, 1))) => D9
  | (0, (1, (0, 1))) => Da
  | (1, (1, (0, 1))) => Db
  | (0, (0, (1, 1))) => Dc
  | (1, (0, (1, 1))) => Dd
  | (0, (1, (1, 1))) => De
  | (1, (1, (1, 1))) => Df
  end%bits.

Module HexN.
  Local Open Scope N_scope.

  Definition N0  : N := 0.
  Definition N1  : N := 1.
  Definition N2  : N := 2.
  Definition N3  : N := 3.
  Definition N4  : N := 4.
  Definition N5  : N := 5.
  Definition N6  : N := 6.
  Definition N7  : N := 7.
  Definition N8  : N := 8.
  Definition N9  : N := 9.
  Definition N10 : N := 10.
  Definition N11 : N := 11.
  Definition N12 : N := 12.
  Definition N13 : N := 13.
  Definition N14 : N := 14.
  Definition N15 : N := 15.

  Definition to_N (x : hex_digit) : N :=
    match x with
    | D0 => N0
    | D1 => N1
    | D2 => N2
    | D3 => N3
    | D4 => N4
    | D5 => N5
    | D6 => N6
    | D7 => N7
    | D8 => N8
    | D9 => N9
    | Da => N10
    | Db => N11
    | Dc => N12
    | Dd => N13
    | De => N14
    | Df => N15
    end.

  Definition of_N (x : N) : hex_digit :=
    match x with
    | 0  => D0
    | 1  => D1
    | 2  => D2
    | 3  => D3
    | 4  => D4
    | 5  => D5
    | 6  => D6
    | 7  => D7
    | 8  => D8
    | 9  => D9
    | 10 => Da
    | 11 => Db
    | 12 => Dc
    | 13 => Dd
    | 14 => De
    | _  => Df (* Anything over 15 becomes 0xF *)
    end.

End HexN.

Definition hex_eqb (x y : hex_digit) : bool :=
  N.eqb (HexN.to_N x) (HexN.to_N y).

Definition hex_compare (x y : hex_digit) : comparison :=
  N.compare (HexN.to_N x) (HexN.to_N y).

Definition hex_leb (x y : hex_digit) : bool :=
  match hex_compare x y with
  | Gt => false
  | _ => true
  end.

Definition byte_leb (x y : byte) : bool :=
  match ByteCompare.compare x y with
  | Gt => false
  | _ => true
  end.

Definition byte_ltb (x y : byte) : bool :=
  match ByteCompare.compare x y with
  | Gt | Eq => false
  | _ => true
  end.

Definition byte_eqb (x y : byte) : bool :=
  ByteCompare.eqb x y.


Inductive utf8_codepoint :=
| ascii (b : byte) (* don't convert ascii chars *)
| codepoint (u v w x y z : hex_digit).

Inductive utf8_string :=
| EmptyString
| String (x : utf8_codepoint) (xs : utf8_string).


Definition codepoint' : Type :=
  (hex_digit * (hex_digit * (hex_digit * (hex_digit * (hex_digit * hex_digit))))).

Definition codepoint_eqb (x y : codepoint') : bool :=
  let '(x0,(x1,(x2,(x3,(x4,x5))))) := x in
  let '(y0,(y1,(y2,(y3,(y4,y5))))) := y in
  hex_eqb x0 y0 &&
  hex_eqb x1 y1 &&
  hex_eqb x2 y2 &&
  hex_eqb x3 y3 &&
  hex_eqb x4 y4 &&
  hex_eqb x5 y5.

Definition codepoint_compare (x y : codepoint') : comparison :=
  let '(x0,(x1,(x2,(x3,(x4,x5))))) := x in
  let '(y0,(y1,(y2,(y3,(y4,y5))))) := y in
  match hex_compare x0 y0 with
  | Gt => Gt
  | Lt => Lt
  | Eq =>
    match hex_compare x1 y1 with
    | Gt => Gt
    | Lt => Lt
    | Eq =>
      match hex_compare x2 y2 with
      | Gt => Gt
      | Lt => Lt
      | Eq =>
        match hex_compare x3 y3 with
        | Gt => Gt
        | Lt => Lt
        | Eq =>
          match hex_compare x4 y4 with
          | Gt => Gt
          | Lt => Lt
          | Eq =>
            match hex_compare x5 y5 with
            | Gt => Gt
            | Lt => Lt
            | Eq => Eq
            end
          end
        end
      end
    end
  end.

Definition codepoint_leb (x y : codepoint') : bool :=
  match codepoint_compare x y with
  | Gt => false
  | _ => true
  end.

Definition codepoint_ltb (x y : codepoint') : bool :=
  match codepoint_compare x y with
  | Gt | Eq => false
  | _ => true
  end.

Definition compare_range (c l h : codepoint') :=
  if codepoint_ltb c l then Gt else
  if codepoint_ltb h c then Lt else
  Eq.



Definition is_ascii (x : utf8_codepoint) : bool :=
  match x with
  | codepoint D0 D0 D0 D0 y _ =>
    (* Is at most U+00007F *)
    hex_leb y D7
  | ascii _ => true
  | _ => false
  end.

Definition is_valid (x : utf8_codepoint) : bool :=
  match x with
  | codepoint u v _ _ _ _ =>
    (* Is at most U+10FFFF *)
    hex_eqb u D0 || (hex_eqb u D1 && hex_eqb v D0)
  | ascii _ => true
  end.



Local Notation "x :: y" := (String.String x y) : bs_scope.

Definition codepoint_to_string (x : utf8_codepoint) : string :=
  match x with
  | ascii b => (* 1 byte *)
    String.String b String.EmptyString
  | codepoint D0 D0 w x y z =>
    let '(w0,(w1,(w2,w3))) := hex_to_bits w in
    let '(x0,(x1,(x2,x3))) := hex_to_bits x in
    let '(y0,(y1,(y2,y3))) := hex_to_bits y in
    let '(z0,(z1,(z2,z3))) := hex_to_bits z in
    if (hex_eqb w D0 && hex_leb x D7)%bool
    then (* 2 bytes *)
      let b1 := Byte.of_bits (y2,(y3,(x0,(x1,(x2,(0,(1,1))))))) in (* start byte *)
      let b2 := Byte.of_bits (z0,(z1,(z2,(z3,(y0,(y1,(0,1))))))) in (* continuation byte 1 *)
      (b1 :: b2 :: "")%bs
    else (* 3 bytes *)
      let b1 := Byte.of_bits (w0,(w1,(w2,(w3,(0,(1,(1,1))))))) in (* start byte *)
      let b2 := Byte.of_bits (y2,(y3,(x0,(x1,(x2,(x3,(0,1))))))) in (* continuation byte 1 *)
      let b3 := Byte.of_bits (z0,(z1,(z2,(z3,(y0,(y1,(0,1))))))) in (* continuation byte 2 *)
      (b1 :: b2 :: b3 :: "")%bs
  | codepoint u v w x y z => (* 4 bytes *)
    let '(u0,(_,(_,_))) := hex_to_bits u in
    let '(v0,(v1,(v2,v3))) := hex_to_bits v in
    let '(w0,(w1,(w2,w3))) := hex_to_bits w in
    let '(x0,(x1,(x2,x3))) := hex_to_bits x in
    let '(y0,(y1,(y2,y3))) := hex_to_bits y in
    let '(z0,(z1,(z2,z3))) := hex_to_bits z in
    let b1 := Byte.of_bits (v2,(v3,(u0,(0,(1,(1,(1,1))))))) in (* start byte *)
    let b2 := Byte.of_bits (w0,(w1,(w2,(w3,(v0,(v1,(0,1))))))) in (* continuation byte 1 *)
    let b3 := Byte.of_bits (y2,(y3,(x0,(x1,(x2,(x3,(0,1))))))) in (* continuation byte 2 *)
    let b4 := Byte.of_bits (z0,(z1,(z2,(z3,(y0,(y1,(0,1))))))) in (* continuation byte 3 *)
    (b1 :: b2 :: b3 :: b4 :: "")%bs
  end%bits.

Fixpoint to_string (x : utf8_string) : string :=
  match x with
  | EmptyString => String.EmptyString
  | String x xs => (codepoint_to_string x) ++ (to_string xs)
  end.

Definition is_ascii_b (b : byte) :=
  byte_leb b x7f.

Definition is_continue (b7 b6 : bool) : bool :=
  b7 && (negb b6).

Definition is_start_byte (b3 b4 b5 b6 b7 : bool) : nat :=
  match (b7,(b6,(b5,(b4,b3)))) with
  | (1,(1,(0,(_,_))))%bits => 1
  | (1,(1,(1,(0,_))))%bits => 2
  | (1,(1,(1,(1,0))))%bits => 3
  | _ => 0
  end.

#[local]
Existing Instance Monad_result.

Definition of_string (s : string) : result utf8_string string :=
  let fix aux s :=
    match s with
    | String.EmptyString => Ok EmptyString
    | (a :: xs)%bs =>
      if is_ascii_b a then
        xs <- aux xs;;
        Ok (String (ascii a) xs)
      else
        let '(a0,(a1,(a2,(a3,(a4,(a5,(a6,a7))))))) := Byte.to_bits a in
        match is_start_byte a3 a4 a5 a6 a7 with
        | 3 =>
          match xs with
          | (b :: c :: d :: xs)%bs =>
            let '(b0,(b1,(b2,(b3,(b4,(b5,(b6,b7))))))) := Byte.to_bits b in
            let '(c0,(c1,(c2,(c3,(c4,(c5,(c6,c7))))))) := Byte.to_bits c in
            let '(d0,(d1,(d2,(d3,(d4,(d5,(d6,d7))))))) := Byte.to_bits d in
            if is_continue b7 b6 && is_continue c7 c6 && is_continue d7 d6
            then
              let z := hex_of_bits (d0,(d1,(d2,d3)))%bits in
              let y := hex_of_bits (d4,(d5,(c0,c1)))%bits in
              let x := hex_of_bits (c2,(c3,(c4,c5)))%bits in
              let w := hex_of_bits (b0,(b1,(b2,b3)))%bits in
              let v := hex_of_bits (b4,(b5,(a0,a1)))%bits in
              let u := hex_of_bits (a2,(0,(0,0)))%bits in
              xs <- aux xs;;
              Ok (String (codepoint u v w x y z) xs)
            else Err "Invalid continuation byte"
          | _ => Err "Unclosed codepoint"
          end
        | 2 =>
          match xs with
          | (b :: c :: xs)%bs =>
            let '(b0,(b1,(b2,(b3,(b4,(b5,(b6,b7))))))) := Byte.to_bits b in
            let '(c0,(c1,(c2,(c3,(c4,(c5,(c6,c7))))))) := Byte.to_bits c in
            if is_continue b7 b6 && is_continue c7 c6
            then
              let z := hex_of_bits (c0,(c1,(c2,c3)))%bits  in
              let y := hex_of_bits (c4,(c5,(b0,b1)))%bits in
              let x := hex_of_bits (b2,(b3,(b4,b5)))%bits in
              let w := hex_of_bits (a0,(a1,(a2,a3)))%bits in
              let v := D0 in
              let u := D0 in
              xs <- aux xs;;
              Ok (String (codepoint u v w x y z) xs)
            else Err "Invalid continuation byte"
          | _ => Err "Unclosed codepoint"
          end
        | 1 =>
          match xs with
          | (b :: xs)%bs =>
            let '(b0,(b1,(b2,(b3,(b4,(b5,(b6,b7))))))) := Byte.to_bits b in
            if is_continue b7 b6
            then
              let z := hex_of_bits (b0,(b1,(b2,b3)))%bits in
              let y := hex_of_bits (b4,(b5,(a0,a1)))%bits in
              let x := hex_of_bits (a2,(a3,(a4,0)))%bits in
              let w := D0 in
              let v := D0 in
              let u := D0 in
              xs <- aux xs;;
              Ok (String (codepoint u v w x y z) xs)
            else Err "Invalid continuation byte"
          | _ => Err "Unclosed codepoint"
          end
        | _ => Err "Invalid UTF-8 start byte"
        end
    end
  in aux s.
