From MetaRocq.Utils Require Import bytestring ReflectEq utils.
From MetaRocq.Common Require Kernames.

From Stdlib Require Import String Ascii Bool Arith.
Require Import Malfunction.Malfunction.
Require Import Malfunction.Serialize_util.

Set Warnings "-masking-absolute-name".
Require Import Ceres.Ceres.
Require Import Ceres.CeresString.
Require Import Ceres.CeresFormat Ceres.CeresSerialize.

Local Open Scope sexp.
Local Open Scope bs_scope.

(* Compute match "'"%bs with bytestring.String.String b _ => b | _ => Byte.x00 end. *)

Fixpoint _escape_ident (_end s : String.t) : String.t :=
  match s with
  | ""%bs => _end
  |  String.String c s' =>
       if (c == "'"%byte) || (c == " "%byte) || (c == "."%byte) then String.String "_" (_escape_ident _end s')
       else match s' with
            | String.String c2 s'' =>
                if (String.String c (String.String c2 String.EmptyString)) == "Γ"%bs
                   then ("Gamma" ++ _escape_ident _end s'')%bs
                else if (String.String c (String.String c2 String.EmptyString)) == "φ"%bs
                   then ("Phi" ++ _escape_ident _end s'')%bs
                else if (String.String c (String.String c2 String.EmptyString)) == "Δ"%bs
                   then ("Delta" ++ _escape_ident _end s'')%bs
                else if (String.String c (String.String c2 String.EmptyString)) == "π"%bs
                   then ("pi" ++ _escape_ident _end s'')%bs
                else if (String.String c (String.String c2 String.EmptyString)) == "ρ"%bs
                   then ("rho" ++ _escape_ident _end s'')%bs
                else if (String.String c (String.String c2 String.EmptyString)) == "Σ"%bs
                   then ("Sigma" ++ _escape_ident _end s'')%bs
                else String.String c (_escape_ident _end s')
            | _ => String.String c (_escape_ident _end s')
            end
  end.

#[export] Instance Serialize_Ident : Serialize Ident.t :=
  fun a => Atom ("$" ++ (_escape_ident ""%bs a)).

From Stdlib Require Sint63.

Definition sint_to_Z := Sint63.to_Z.

#[export] Instance Serialize_int : Serialize int :=
   fun i => to_sexp (sint_to_Z i).

Import SpecFloat.
From Stdlib Require Numbers.HexadecimalString.
Definition string_of_specfloat (f : SpecFloat.spec_float) : String.t :=
  match f with
  | S754_zero sign => if sign then "-0.0" else "0.0"
  | S754_infinity sign => if sign then "neg_infinity" else "infinity"
  | S754_nan => "nan"
  | S754_finite sign p z =>
    let abs :=
    "0x" ++ String.of_string (HexadecimalString.NilZero.string_of_uint (Pos.to_hex_uint p)) ++ "p" ++
      String.of_string (DecimalString.NilZero.string_of_int (Z.to_int z))
    in
    if sign then "-" ++ abs else abs
  end%bs.

#[export] Instance Serialize_numconst : Serialize numconst :=
  fun a => match a with
        | numconst_Int i => to_sexp (sint_to_Z i)
        | numconst_Bigint x => Atom ((CeresString.string_of_Z x) ++ ".ibig")
        | numconst_Float64 x => Atom ((string_of_specfloat (FloatOps.Prim2SF x)) ++ ".f64")
        end.

Definition Cons x (l : sexp) :=
  match l with
  | List l => List (x :: l)
  | x => x
  end.

Definition App (l1 : sexp) (l2 : sexp) :=
  match l1, l2 with
  | List l1, List l2 => List (l1 ++ l2)
  | _x, y => y
  end.

Definition rawapp (s : sexp) (a : String.t) :=
  match s with
  | Atom_ (Raw s) => Atom (Raw (s ++ a))
  | x => x
  end.

#[export] Instance Serialize_case : Serialize case :=
  fun a => match a with
        | Tag tag => [Atom "tag"; Atom (sint_to_Z tag)]
        | Deftag => [Atom "tag"; Atom "_"]
        | Intrange (i1, i2) => if uint_leb i1 i2 then [ to_sexp i1 ; to_sexp i2  ] else Atom "_"
        end.

#[export] Instance Serialize_unary_num_op : Serialize unary_num_op :=
  fun a => match a with Neg => Atom "neg" | Not => Atom "not" end.

Definition numtype_to_string (n : numtype) :=
  match n with
  | embed_inttype x => match x with
                      | Int => ""
                      | Int32 => ".i32"
                      | Int64 => ".i64"
                      | Bigint => ".ibig"
                      end
  | Float64 => ""
  end.

Definition vector_type_to_string (n : vector_type) :=
  match n with
  | Array => ""
  | Bytevec => ".byte"
  end.

#[export] Instance Serialize_binary_arith_op : Serialize binary_arith_op :=
  fun a => Atom match a with
        | Add => "+"
        | Sub => "-"
        | Mul => "*"
        | Div => "/"
        | Mod => "%"
        end.

#[export] Instance Serialize_binary_bitwise_op : Serialize binary_bitwise_op :=
  fun a => Atom match a with
             | And => "&"
             | Or => "|"
             | Xor => "^"
             | Lsl => "<<"
             | Lsr => ">>"
             | Asr => "a>>"
             end.

#[export] Instance Serialize_binary_comparison : Serialize binary_comparison :=
  fun a => Atom match a with
             | Lt => "<"
             | Gt => ">"
             | Lte => "<="
             | Gte => ">="
             | Eq => "=="
             end.

#[export] Instance Serialize_binary_num_op : Serialize binary_num_op :=
  fun a => match a with
        | embed_binary_arith_op x => to_sexp x
        | embed_binary_bitwise_op x => to_sexp x
        | embed_binary_comparison x => to_sexp x
        end.

Definition Serialize_singleton_list {A} `{Serialize A} : Serialize (list A)
  := fun xs => match xs with cons x nil => to_sexp x | xs =>List (List.map to_sexp xs) end.

Fixpoint split_dot accl accw (s : String.t) :=
  match s with
  | String.EmptyString => (string_reverse accl, string_reverse accw)
  | String.String c s =>
      if (c =? ".")%char2 then
        let accl' := match accl with String.EmptyString => accw
                                | accl => (accw ++ "." ++ accl)
                     end in
        split_dot accl' String.EmptyString s
      else
        split_dot accl (String.String c accw) s
  end.
Definition before_dot s := fst (split_dot String.EmptyString String.EmptyString s).
Definition after_dot s := snd (split_dot String.EmptyString String.EmptyString s).

Fixpoint to_sexp_t (a : t) : sexp :=
  match a with
  | Mvar x => to_sexp x
  | Mlambda (ids, x) => [ Atom "lambda" ; to_sexp ids ; to_sexp_t x ]
  | Mapply (x, args) => List (Atom "apply" :: to_sexp_t x :: List.map to_sexp_t args)
  | Mlet (binds, x) => List (Atom "let" :: List.map to_sexp_binding binds ++ (to_sexp_t x :: nil))
  | Mnum x => to_sexp x
  | Mstring x => Atom (Str x)
  | Mglobal x => (* [Atom "global" ; Atom ("$Top") ; *) to_sexp ("def_" ++ x)%bs  (* ] *)
  | Mswitch (x, sels) =>
      (* let sels := match List.rev sels with *)
      (*              | cons last rest => List.rev ((Deftag :: (Intrange (Uint63.of_Z (BinNums.Zpos (BinNums.xI BinNums.xH)), Uint63.of_Z BinNums.Z0) :: nil) %list, snd last) :: rest)%list *)
      (*              | nil => nil *)
      (*              end in *)
      Cons (Atom "switch") (Cons (to_sexp_t x) (@Serialize_list _ (fun '(sel, t) => App (to_sexp sel) ([to_sexp_t t]) ) sels))
  | Mnumop1 (op, num, x) => [ rawapp (to_sexp op) (numtype_to_string num) ; to_sexp_t x ]
  | Mnumop2 (op, num, x1, x2) => [ rawapp (to_sexp op) (numtype_to_string num) ; to_sexp_t x1 ; to_sexp_t x2 ]
  | Mconvert (from, to, x) => [rawapp (rawapp (Atom "convert") (numtype_to_string from)) (numtype_to_string to) ; to_sexp_t x]
  | Mvecnew (ty, x1, x2) => [ Atom ("makevec" ++ (vector_type_to_string ty)) ; to_sexp_t x1 ; to_sexp_t x2 ]
  | Mvecget (ty, x1, x2) => [ Atom ("load" ++ (vector_type_to_string ty)) ; to_sexp_t x1 ; to_sexp_t x2 ]
  | Mvecset (ty, x1, x2, x3) => [ Atom ("store" ++ (vector_type_to_string ty)) ; to_sexp_t x1 ; to_sexp_t x2; to_sexp_t x3 ]
  | Mveclen (ty, x) => [ Atom ("load" ++ (vector_type_to_string ty)) ; to_sexp_t x ]
  | Mlazy x => [Atom "lazy"; to_sexp_t x]
  | Mforce x => [Atom "force"; to_sexp_t x]
  | Mblock (tag, xs) => List (Atom "block" :: [Atom "tag"; Atom (sint_to_Z tag)] :: List.map to_sexp_t xs)
  | Mfield (i, x) => [ Atom "field"; to_sexp i; to_sexp_t x]
  end
with
to_sexp_binding (a : binding) : sexp :=
  match a with
  | Unnamed x => [ Atom "_"; to_sexp_t x ]
  | Named (id, x) => [ to_sexp id ; to_sexp_t x ]
  | Recursive x => Cons (Atom "rec") (@Serialize_list _ (@Serialize_product _ _ _ to_sexp_t) x)
  end.

#[export] Instance Serialize_t : Serialize t := to_sexp_t.
#[export] Instance Serialize_binding : Serialize binding := to_sexp_binding.

(* Fixpoint string_map (f : ascii -> ascii) (s : string) : string := *)
(*   match s with *)
(*   | EmptyString => EmptyString *)
(*   | String c s => String (f c)< (string_map f s) *)
(*   end. *)

(* Definition dot_to_underscore (id : string) := *)
(*   string_map (fun c =>  *)
(*     match c with *)
(*     | "."%char => "_"%char *)
(*     | _ => c *)
(*     end) id. *)

Definition uncapitalize_char (c : Byte.byte) : Byte.byte :=
  let n := Byte.to_nat c in
  if (65 <=? n)%nat && (n <=? 90)%nat then match Byte.of_nat (n + 32) with Some c => c | _ => c end
  else c.

Definition uncapitalize (s : bytestring.string) : bytestring.string :=
  match s with
  | bytestring.String.EmptyString => bytestring.String.EmptyString
  | bytestring.String.String c s => bytestring.String.String (uncapitalize_char c) s
  end.

Definition encode_name (s : bytestring.string) : bytestring.string :=
  _escape_ident ""%bs s.

Definition exports (m : list (Ident.t * option t)) : list (Ident.t * option t) :=
  List.map (fun '(x, v) => (("def_" ++ encode_name x)%bs, Some (Mglobal x))) m.


Definition bytestring_atom s :=
  ("$" :: s).

Fixpoint find_prim (id : Ident.t) (prims : primitives) : option (prim_def String.t) :=
  match prims with
  | nil%list => None
  | ((kn, primdef) :: prims)%list =>
    if ReflectEq.eqb id kn then
      match primdef with
      | Global modname label => Some (Global (bytestring_atom modname) (bytestring_atom label))
      | Primitive symbol arity => Some (Primitive symbol arity)
      | Erased => Some Erased
      end
    else find_prim id prims
  end.

Section binders.
  Context (x : bytestring.string).

  Definition add_suffix n := (x ++ MRString.string_of_nat n)%bs.

  Fixpoint binders n acc :=
    match n with
    | 0 => acc
    | S n => binders n (add_suffix n :: acc)%list
    end.
End binders.

Definition mk_eta_exp n s :=
  let binders := binders "x"%bs n nil in
  [ Atom "lambda" ; to_sexp binders ; List (Atom s :: List.map to_sexp binders) ].

Definition global_serializer (prims : primitives) : Serialize (Ident.t * option t) :=
  fun '(i, b) =>
  match b with
  | Some x => to_sexp ("def_" ++ i, x)%bs
  | None =>
    match find_prim i prims with
    | Some (Global modname label) =>
      let na := (uncapitalize ("def_" ++ encode_name i)%bs) in
      List ( Atom (Raw ("$" :: na)) :: [Atom "global" ; Atom (Raw modname) ; Atom (Raw label)] :: nil)
    | Some (Primitive symbol arity) =>
      let na := (uncapitalize ("def_" ++ encode_name i)%bs) in
      List ( Atom (Raw ("$" :: na)) ::
      mk_eta_exp arity (Raw (symbol)) :: nil)
    | Some Erased
    | None =>
    let na := (uncapitalize ("def_" ++ encode_name i)%bs) in
      List ( Atom (Raw ("$" :: na)) :: [Atom "global" ; Atom (Raw ("$Axioms")) ; Atom (Raw ("$" :: na)) ]
             :: nil)
    end
  end.

Fixpoint filter_erased_prims prims (l : list (Ident.t * option t)) : list (Ident.t * option t) :=
  match l with
  | nil => nil
  | cons ((id, Some _) as x) xs => x :: filter_erased_prims prims xs
  | cons ((id, None) as x) xs =>
    match find_prim id prims with
    | Some Erased => filter_erased_prims prims xs
    | _ => x :: filter_erased_prims prims xs
    end
  end.

Fixpoint thename a (s : bytestring.String.t) :=
  match s with
  | String.EmptyString => bytestring.String.of_string (string_of_list_byte (List.rev a))
  | String.String b s => if b == "."%byte
                        then thename nil s
                        else thename (b :: a)%list s
  end.


Variant program_type : Set :=
  | Standalone
  | Shared_lib (modname : bytestring.String.t) (register : bytestring.String.t). (* Reference to a plugin registration function*)

(* Eval compute in to_sexp (Mapply (Mglobal "foo"%bs, [Mglobal "bar"%bs]%list)). *)

Definition shared_lib_register modname label '(name, export) :=
  let code := (List [Atom "apply"; List [Atom "global" ;
  Atom ("$" ++ modname)%bs ; Atom ("$" ++ label)%bs]%list;
  Atom (Str (name));
  Atom ("$" ++ export)]) in
  Cons (Atom "_") (List (code :: nil)).

(* Eval compute in
  to_string (shared_lib_register "malfunction"%bs "register"%bs ("foo.test", "test")%bs). *)

Definition Serialize_module prims (pt : program_type) (names : list bytestring.string): Serialize program :=
  fun '(m, x) =>
    let name : Ident.t  := match m with
                           | (x :: l)%list => fst x
                           | nil => ""%bs
                           end in
    let main := "main"%bs in
    let names := (names ++ ["main"%bs])%list in
    let shortnames : list Ident.t := List.map (fun name => uncapitalize (thename nil name)) names in
    let longnames : list sexp := List.map (fun name => (to_sexp ("def_" ++ name)%bs)) names in
    let allnames := List.combine shortnames longnames in
    let exports : list sexp := List.map (fun shortname => Atom ("$" ++ shortname)%bs)
      shortnames in
    let m := filter_erased_prims prims m in
    let linkopt :=
      match pt return list sexp with
      | Standalone => nil
      | Shared_lib modname label =>
        List.map (shared_lib_register modname label) (List.combine names shortnames)
      end
    in
    match
      Cons (Atom "module") (@Serialize_list _ (global_serializer prims)
        (List.rev ((main, Some x) :: m)%list))
    with
      List l =>
        List (l                 (* the extracted functions *)
              ++ List.map (fun '(shortname,longname) => Cons (Atom ("$" ++ shortname)%bs)
                             (List (longname :: nil))) allnames
              ++ linkopt
              ++ (Cons (Atom "export") (List exports) :: nil))%list (* export *)
    | x => x
    end.
