From Malfunction Require Import Malfunction.
From Ceres Require Import Ceres.
From Stdlib Require Import List.
From MetaRocq.Utils Require Import bytestring.
Import ListNotations.

Local Open Scope list.
Local Open Scope bs_scope.

#[export] Instance Deserialize_Ident : Deserialize Ident.t :=
  fun l e =>
    match e with
    | Atom_ (Raw (String.String sym s)) => if String.eqb (String.String sym String.EmptyString) "$" then
                             inr s else inl (DeserError l "identifier needs to start with an $")
    | List _ => inl (DeserError l "could not read 'ident', got list")
    | _ => inl (DeserError l "could not read 'ident', got non-string atom")
    end.

#[export] Instance SemiIntegral_int : SemiIntegral int :=
  fun n => Some (Int63.of_Z n).

(* #[export] Instance Deserialize_int : Serialize int := *)
(*   fun i => to_sexp (Int63.to_Z i). *)

Definition Deserialize_tag : Deserialize int :=
  Deser.match_con "tag" nil
                  [ ("tag", Deser.con1 (fun x => x) _from_sexp ) ].

Notation con2c f := (Deser.con2 (fun x y => f (x, y))).

#[export] Instance Deserialize_case : Deserialize case :=
  fun l c =>
    match c with
    | Atom_ "_" => inr Deftag
    | List [e1; e2] => match from_sexp (A := int) e1, from_sexp (A := int) e2 with
                       | inr i1, inr i2 => inr (Intrange (i1, i2))
                       | inl e, _ => inl e
                      | _, inl e => inl e
                       end
    | _ => match from_sexp (A := int) c with inr i => inr (Tag i) | inl e => inl e end
    end.


Definition int_of_nat n := Int63.of_Z (Stdlib.ZArith.BinInt.Z.of_nat n).

Definition Mif c e1 e2 := Mswitch (c, [ ([ Tag (int_of_nat 0) ], e1 ); ([Deftag ], e2) ]). (* TODO: tag _ is allowed?? *)

Definition splitlast {A} (a : A) (l : list A) : (list A * A) :=
  match rev l with
  | b :: l => (a :: rev l, b)
  | _ => ([], a)
  end.

Definition splitfirst (l : list binding) : (list binding * t) :=
  match rev l with
  | Unnamed b :: l => (rev l, b)
  | _ => (nil, (Mvar (("ERROR"))))
  end.

(* From ReductionEffect Require Import PrintingEffect. *)

#[bypass_check(guard)]
Fixpoint ds (l : loc) (e : sexp) {struct e} : error + t :=
  match Deserialize_Ident l e with inr i => inr (Mvar i) | _ =>
    match _from_sexp (A := int) l e with inr i => inr (Mnum (numconst_Int i)) | _ =>
    Deser.match_con "t" nil
                    [
                      ("lambda", con2c Mlambda Deserialize_list ds);
                      ("apply", fun l f e => match _sexp_to_list ds [] 0 l e with
                                             | inr (x :: l) => inr (Mapply (x, l))
                                             | inr [] => inl (DeserError l (MsgStr "application without function"))
                                             | inl er => inl er
                                             end);

                      ("let", fun l f e => match e with
                                           | x :: e =>
                                              let (e, last) := splitlast x e in
                                              match _sexp_to_list dsb [] 0 l e, ds l last with
                                              | inr bds, inr body => inr (Mlet (bds, body))
                                              | inl er, _ => inl er
                                              | _, inl er => inl er
                                              end
                                           | _ => inl (DeserError l (MsgStr "let without body"))
                                           end);

                      ("switch", con2c Mswitch ds (@Deserialize_list _ (@Deserialize_prod _ _ _ ds)));
                      ("if", Deser.con3 Mif ds ds ds);
                      ("lazy", Deser.con1 Mlazy ds);
                      ("force", Deser.con1 Mlazy ds);
                      ("block", con2c Mblock Deserialize_tag (@Deserialize_list t ds));
                      ("field", con2c Mfield _from_sexp ds);
                      ("==", Deser.con2 (fun x1 x2 => Mnumop2 (embed_binary_comparison Eq, embed_inttype Int, x1, x2)) ds ds)
                    ] l e
    end end
with dsb (l : loc) (e : sexp) {struct e} : error + binding :=
  match Deser.match_con "binding" nil
                    [
                      ("_", Deser.con1 Unnamed ds );
                      ("rec",
                      fun l f e => match _sexp_to_list (@Deserialize_prod _ _ _ ds) [] 0 l e with inr l => inr (Recursive l) | inl er => inl er end)
                    ] l e
  with inr r => inr r
  | _ => match e with
         | List [ id; x ] => match Deserialize_Ident l id, ds l x with
                             | inr id, inr r => inr (Named (id, r))
                             | _, _ => match ds l e with inr r => inr (Unnamed r) | inl e => inl e end
                             end
         | _ => match ds l e with inr r => inr (Unnamed r) | inl e => inl e end (* this is a hack: we pass the last argument of a  *)
         end
  end.

#[export] Instance Deserialize_t : Deserialize t := ds.
#[export] Instance Deserialize_binding : Deserialize binding := dsb.
(*
Definition test input :=
  match parse_sexp input with
  | inr e => from_sexp e
  | _ => inr (Mvar "ERROR")
  end.

Definition testb input :=
  match parse_sexp input with
  | inr e => from_sexp e
  | _ => inr (Unnamed (Mvar "ERROR"))
  end.

Compute test "(force $a)".
Compute test "(lambda ($x) (if (== $x 42) 100 (force $a)))".
Compute test "(let
(rec
  ($a (lazy (apply $f 42)))
  ($f (lambda ($x) (if (== $x 42) 100 (force $a)))))
(apply $f 17))". *)
