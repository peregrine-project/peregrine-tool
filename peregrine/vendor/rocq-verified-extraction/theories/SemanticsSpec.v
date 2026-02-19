From Stdlib Require Import ZArith Array.PArray List Floats Lia.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect.
From Malfunction Require Import Malfunction utils_array.
From MetaRocq.PCUIC Require Import PCUICAst PCUICFirstorder.

From MetaRocq.Utils Require Import bytestring.
Import ListNotations.

Open Scope bs. 


Set Default Goal Selector "!".

Class Pointer := {pointer : Type}.

Class Heap `{Pointer} := {
  heapGen : forall (value : Type), Type;
  fresh : forall {value : Type}, heapGen value -> pointer -> heapGen value -> Prop;
  deref : forall {value : Type}, heapGen value -> pointer -> list value -> Prop;
  update : forall {value : Type}, heapGen value -> pointer -> list value -> heapGen value -> Prop
}.

Definition CanonicalPointer : Pointer := {| pointer := int |}.

Definition CanonicalHeap : @Heap CanonicalPointer := 
{| heapGen := fun value => (int * (int -> list value)) % type;
   fresh :=  fun _ '(ptr,h) (fresh_ptr : @pointer CanonicalPointer) '(ptr',h') => Int63.ltb ptr fresh_ptr = true /\ fresh_ptr = ptr' /\ h = h' ;
   deref := fun _ '(_,h) ptr val => h ptr = val;
   update := fun _ '(max_ptr,h) ptr arr '(max_ptr',h') => 
     max_ptr' = int_of_nat (max (int_to_nat max_ptr) (int_to_nat ptr)) /\ forall ptr', h' ptr' = if Int63.eqb ptr ptr' then arr else h ptr |}. 

Inductive rec_value `{Pointer} := 
  | RFunc of Ident.t * t
  | RThunk of pointer
  | Bad_recursive_value.

Inductive value `{Pointer} :=
| Block of int * list value
| Vec of vector_type * pointer
| Func of @Ident.Map.t value * Ident.t *  t
| RClos of @Ident.Map.t value * list Ident.t * list rec_value * nat
| Lazy of @Ident.Map.t value * t
| value_Int of inttype * Z
| Float of float
| Thunk of pointer
| fail of string
| not_evaluated
.

Definition heap `{Heap} := heapGen value.

 From Stdlib Require Import Uint63.

 Definition list_of_array {A : Type} (a:array A) : list A :=
   (fix go (n : nat) (i : int) (acc : list A) :=
   match n with
   | 0 => acc
   | S n => go n (i - 1)%uint63 (cons a.[i] acc)
   end) (Z.to_nat (Uint63.to_Z (PArray.length a))) (PArray.length a - 1)%uint63 nil.
 
Definition isFunction `{Heap} (s : value) : bool :=
  match s with
  | Func _ => true
  | RClos _ => true
  | Lazy _ => true
  | _ => false
  end. 

Definition isThunk `{Heap} (s : value) : bool :=
  match s with
  | Thunk _ => true
  | _ => false
  end. 

Definition isBlock `{Heap} (s : value) : bool :=
  match s with
  | Block _ => true
  | _ => false
  end. 

Definition isNotEvaluated `{Heap} (s : value) : bool :=
  match s with
  | not_evaluated => true
  | _ => false
  end.  

Definition fail_def {A} (a : A) (s : string) : A.
  exact a.
Qed.

Definition fail_float := fail_def infinity.
Definition fail_Z := fail_def Z.zero.

Definition bitwidth := fun t =>
match t with
| Int => 63
| Int32 => 32
| Int64 => 64
| Bigint => fail_Z "no bitwidth for bigint"
end%Z.

Definition truncate `{Pointer} ty n :=
  value_Int (ty, match ty with
                 | Bigint => n
                 | ty =>
                     let width := bitwidth ty in
                     let range := Z.shiftl (Z.of_nat 1) width in
                     let masked := Z.land n (Z.sub range (Z.of_nat 1)) in
                     let min_int := Z.shiftr range 1 in
                     if Z.ltb masked min_int then masked else
                       Z.sub masked range
                 end). 

Definition inttype_eqb (t1 t2 : inttype) :=
  match t1, t2 with
  | Int, Int
  | Int32, Int32
  | Int64, Int64
  | Bigint, Bigint => true
  | _, _ => false
  end.

Definition as_ty `{Pointer} ty := fun ty2 =>
  match ty2 with
  | value_Int (ty', n) => if inttype_eqb ty ty' then n else fail_Z "integer type missmatch"
  | _ => fail_Z "expected integer"
  end.

Definition as_float `{Pointer} x := match x with
  | Float f => f
  | _ => fail_float "expected float64"
end.

Definition cond `{Pointer} scr case : bool := 
  (match case, scr with
    | Tag n, Block (n', _) => Int63.eqb n n'
    | Deftag, Block _ => true
    | Intrange (min, max), value_Int (Int, n) => Z.leb (Int63.to_Z min) n && Z.leb n (Int63.to_Z max)
    | _, _ => false end).

Fixpoint find_match `{Pointer} scr x : option t := match x with 
                                        | (cases, e) :: rest =>
                                            if List.existsb (cond scr) cases then
                                              Some e
                                            else
                                              find_match scr rest
                                        | [] => None end.


Definition Mklambda binders e :=
  match binders with [] => e | _ => Mlambda (binders, e) end.

Definition RFunc_build `{Pointer} recs := 
    map (fun t =>
      match t with 
      Mlambda ([x], e) => RFunc (x , e)
    | Mlambda (x :: xs , e) => RFunc (x , Mlambda (xs , e))
    | _ => Bad_recursive_value
    end) 
    recs.

Definition add_recs `{Pointer} locals (self : list Ident.t) rfunc := 
  List.mapi (fun n x => (x , RClos (locals, self, rfunc, n))) self.

Definition add_self `{Pointer} self rfunc locals := 
  List.fold_right (fun '(x,t) l => Ident.Map.add x t l) locals (add_recs locals self rfunc) .

Definition comparison_eqb x1 x2 :=
  match x1, x2 with
  | Datatypes.Lt, Datatypes.Lt | Datatypes.Gt, Datatypes.Gt | Datatypes.Eq, Datatypes.Eq => true
  | _, _ => false
  end.

Definition binary_comparison_eqb op cmp := 
  match op with
  | Lt => comparison_eqb cmp Datatypes.Lt
  | Gt => comparison_eqb cmp Datatypes.Gt
  | Lte => negb (comparison_eqb cmp Datatypes.Gt)
  | Gte => negb (comparison_eqb cmp Datatypes.Lt)
  | Eq => comparison_eqb cmp Datatypes.Eq
  end.

Definition binary_op_to_float (op : binary_arith_op) v1 v2 : float := 
  match op with
   | Sub => v1 - v2
   | Mul => v1 * v2
   | Div => v1 / v2
   | Mod => fail_float "mod on floats not supported" 
   | Add => v1 + v2 
   end.

Definition binary_comparison_to_bool op e1 e2 :=
  match op with
  | Lt => PrimFloat.ltb e1 e2
  | Gt => PrimFloat.ltb e2 e2
  | Lte => PrimFloat.leb e1 e2
  | Gte => PrimFloat.leb e2 e1
  | Eq => PrimFloat.eqb e1 e2
  end.

Definition option_def {A} (a : A) (x : option A) : A :=
  match x with
  | None => a
  | Some a => a
  end.

Definition vector_type_eqb (t1 t2 : vector_type) :=
  match t1, t2 with
  | Array, Array
  | Bytevec, Bytevec => true
  | _, _ => false
  end.

Fixpoint get (n : nat) (s : string) {struct s} : option Byte.byte :=
  match s with
  | MetaRocq.Utils.bytestring.String.EmptyString => None
  | MetaRocq.Utils.bytestring.String.String c s' =>
	  match n with
      | 0 => Some c
      | S n' => get n' s'
      end
  end.

Definition empty_locals `{Pointer} : Ident.Map.t := fun _ => fail "notfound".

Section eval.

Variable _Pointer:Pointer.
Variable _Heap:Heap.
Variable globals : list (Ident.t * value).

Unset Elimination Schemes.
Inductive eval (locals : @Ident.Map.t value) : heap -> t -> heap -> value -> Prop := 
| eval_lambda_sing h x e :
  eval locals h (Mlambda ([x], e)) h (Func (locals, x , e))
| eval_lambda h x ids e :
  List.length ids > 0 ->
  eval locals h (Mlambda (x :: ids, e)) h (Func (locals, x, Mlambda (ids, e)))
| eval_app_sing h h1 h2 h3 x locals' e e2 v2 e1 v :
  eval locals h e1 h1 (Func (locals', x , e)) -> 
  eval locals h1 e2 h2 v2 ->
  eval (Ident.Map.add x v2 locals') h2 e h3 v ->
  eval locals h (Mapply (e1, [e2])) h3 v
| eval_app_sing_rec h h1 h2 h3 mfix self n y e locals' e2 v2 e1 v : 
  eval locals h e1 h1 (RClos (locals', self, mfix , n)) -> 
  eval locals h1 e2 h2 v2 ->
  nth n mfix Bad_recursive_value = RFunc (y , e) -> 
  eval (Ident.Map.add y v2 (add_self self mfix locals')) h2 e h3 v ->
  eval locals h (Mapply (e1, [e2])) h3 v
| eval_app_fail h h1 e2 e1 v :
  eval locals h e1 h1 v ->
  isFunction v = false ->
  eval locals h (Mapply (e1, [e2])) h1 (fail "not a function:  evaluated to: ")
| eval_app h h1 e3 e2 e1 v es :
  eval locals h (Mapply (Mapply (e1, [e2]), e3 :: es)) h1 v ->
  eval locals h (Mapply (e1, e2 :: e3 :: es)) h1 v
| eval_var h id :
  eval locals h (Mvar id) h (Ident.Map.find id locals)
| eval_let_body h h1 e v : 
  eval locals h e h1 v -> eval locals h (Mlet ([], e)) h1 v
| eval_let_unnamed h h1 h2 e1 v1 lts e2 v :
  eval locals h e1 h1 v1 ->
  eval locals h1 (Mlet (lts, e2)) h2 v ->
  eval locals h (Mlet (Unnamed e1 :: lts, e2)) h2 v 
| eval_let_named h h1 h2 x e1 v1 lts e2 v :
  eval locals h e1 h1 v1 ->
  eval (Ident.Map.add x v1 locals) h1 (Mlet (lts, e2)) h2 v ->
  eval locals h (Mlet (Named (x,e1) :: lts, e2)) h2 v 
| eval_let_rec h h1 recs lts e2 v :
  let self := map fst recs in
  let rfunc := RFunc_build (map snd recs) in
    eval (add_self self rfunc locals) h (Mlet (lts, e2)) h1 v ->
    eval locals h (Mlet (Recursive recs :: lts, e2)) h1 v 
| eval_switch h h1 h2 scr cases v v' e :
  eval locals h scr h1 v' ->
  find_match v' cases = Some e ->
  eval locals h1 e h2 v ->
  eval locals h (Mswitch (scr, cases)) h2 v
| eval_block tag h h' es vals :
  Forall2_acc (eval locals) h es  h' vals ->
  List.length vals < int_to_nat max_length ->
  eval locals h (Mblock (tag, es)) h' (Block (tag, vals))
| eval_field h h' idx b vals tag :
  eval locals h b h' (Block (tag, vals)) ->
  Datatypes.length vals <= int_to_nat max_length ->
  int_to_nat idx < List.length vals ->
  eval locals h (Mfield (idx, b)) h' (nth (int_to_nat idx) vals (fail ""))
| eval_field_fail h h' idx b v :
  eval locals h b h' v ->
  isBlock v = false ->
  eval locals h (Mfield (idx, b)) h' (fail "not a block")
| eval_thunk h h' h'' ptr e :
  let arr := [not_evaluated; Lazy (locals , e)] in
  fresh h ptr h' -> 
  update h' ptr arr h'' ->
  eval locals h (Mlazy e) h'' (Thunk ptr) 
| eval_force_done h h' e ptr vals lazy :
  eval locals h e h' (Thunk ptr) ->
  deref h' ptr vals ->
  List.length vals > 1 -> 
  nth 0 vals (fail "") = lazy ->
  isNotEvaluated lazy = false ->
  eval locals h (Mforce e) h' lazy 
| eval_force h h' h'' h''' ptr vals locals' e v :
  eval locals h e h' (Thunk ptr) ->
  deref h' ptr vals ->
  List.length vals = 2 ->
  isNotEvaluated (nth 0 vals (fail "")) = true -> 
  nth 1 vals (fail "") = Lazy (locals' , e) ->
  eval locals' h' e h'' v ->
  update h'' ptr [v; Lazy (locals' , e)] h''' ->
  eval locals h (Mforce e) h''' v  
| eval_force_fail h h' e v :
  eval locals h e h' v ->
  isThunk v = false ->
  eval locals h (Mforce e) h' (fail "not a lazy value")
| eval_global h nm v :
  In (nm, v) globals ->
  eval locals h (Mglobal nm) h v
| eval_num_int n h : eval locals h (Mnum (numconst_Int n)) h (value_Int (Int, Int63.to_Z n))
| eval_num_bigint n h : eval locals h (Mnum (numconst_Bigint n)) h  (value_Int (Bigint, n))
| eval_num_float f h : eval locals h (Mnum (numconst_Float64 f)) h  (Float f)
| eval_string s h h' h'' ptr : 
  String.length s < int_to_nat max_length ->
  let str := List.init (String.length s)
    (fun i => value_Int (Int, Z.of_nat (Byte.to_nat (option_def (Ascii.byte_of_ascii Ascii.Space) (get i s))))) in
  fresh h ptr h' -> 
  update h' ptr str h'' ->
  eval locals h (Mstring s) h'' (Vec (Bytevec, ptr))
| eval_numop1 op ty e h h' v : 
   eval locals h e h' v -> 
   let n := as_ty ty v in
   eval locals h (Mnumop1 (op, embed_inttype ty, e)) h' (truncate ty (match op with Malfunction.Neg => Z.mul (-1) n | Not => Z.lnot n end))
| eval_numop2 op ty e1 e2 v1 v2 h h1 h2 :
      eval locals h e1 h1 v1 ->
      eval locals h1 e2 h2 v2 ->
      eval locals h (Mnumop2 (op, embed_inttype ty, e1, e2)) h2  
      match op with
      | embed_binary_arith_op op =>
          let f := match op with
                   | Sub => Z.sub | Mul => Z.mul | Div => Z.div | Mod => Z.rem | Add => Z.add 
                   end in
          truncate ty (f (as_ty ty v1) (as_ty ty v2))
      | embed_binary_bitwise_op op =>
          let n := as_ty ty v1 in
          let c := as_ty Int v2 in
          (* TODO is this test necessary? *)
          truncate ty (match op with
          | And => Z.land (as_ty ty v1) (as_ty ty v2)
          | Or => Z.lor (as_ty ty v1) (as_ty ty v2)
          | Xor => Z.lxor (as_ty ty v1) (as_ty ty v2)
          | Lsl => Z.shiftl n c
          | Asr => Z.shiftr n c
          | Lsr => 
              let n := match ty with
                       | Bigint => n
                       | _ =>
                           let w := bitwidth ty in
                           Z.land n (Z.sub (Z.shiftl (Z.of_nat 1) w) (Z.of_nat 1)) end in
              Z.shiftr n c end)
      | embed_binary_comparison op =>
          let cmp := Z.compare (as_ty ty v1) (as_ty ty v2) in
          let res := binary_comparison_eqb op cmp in
          value_Int (Int, if res then 1%Z else 0%Z)
      end
| eval_numop1_neg e h h' v :  
    eval locals h e h' v ->
    eval locals h (Mnumop1 (Malfunction.Neg, Float64, e)) h' (Float (- as_float v))
| eval_numop1_float_fail h x : 
  eval locals h (Mnumop1 (Not, Float64, x)) 
              h (fail "invalid bitwise float operation")
| eval_numop2_float_fail h x y n : 
    eval locals h (Mnumop2 (embed_binary_bitwise_op n, Float64, x, y)) 
                h (fail "invalid bitwise float operation")
| eval_numop2_float h h1 h2 op e1 e2 v1 v2 :
      eval locals h e1 h1 v1 ->
      eval locals h1 e2 h2 v2 ->
      let v1' := as_float v1 in
      let v2' := as_float v2 in
      eval locals h (Mnumop2 (embed_binary_arith_op op, Float64, e1, e2))
                  h2 (Float (binary_op_to_float op v1' v2'))
| eval_numop2_embed_float h h1 h2 op e1 e2 v1 v2 :
      eval locals h e1 h1 v1 ->
      eval locals h1 e2 h2 v2 ->
      let v1' := as_float v1 in
      let v2' := as_float v2 in
      let res := binary_comparison_to_bool op v1' v2' in
      eval locals h (Mnumop2 (embed_binary_comparison op, Float64, e1, e2))
                  h2 (value_Int (Int, if res then 1%Z else 0%Z))
| eval_convert_int h h' e v src dst : 
      eval locals h e h' v ->
      eval locals h (Mconvert (embed_inttype src, embed_inttype dst, e))
                  h' (truncate dst (as_ty src v))
| eval_convert_float h h' e v src :
      eval locals h e h' v ->
      eval locals h (Mconvert (embed_inttype src, Float64, e))
                  h' (Float (PrimFloat.of_uint63 (Int63.of_Z (as_ty src v))))
| eval_convert_float_float h h' v e :
      eval locals h e h' v ->
      eval locals h (Mconvert (Float64, Float64, e)) 
                  h' (Float (as_float v))                                              
| eval_vecnew_array h h1 h2 h3 h4 len len' def def' ptr : 
      eval locals h len h1 (value_Int (Int, len')) -> 
      (0 <= len')%Z ->
      Z.to_nat len' <= int_to_nat max_length ->
      eval locals h1 def h2 def' ->
      fresh h2 ptr h3 -> 
      update h3 ptr (List.init (Z.to_nat len') (fun _ => def')) h4 ->
      eval locals h (Mvecnew (Array, len, def)) h4 (Vec (Array, ptr))
| eval_vecnew_bytevec h h1 h2 h3 h4 len len' def k ptr : 
      eval locals h len h1 (value_Int (Int, len')) -> 
      (0 <= len')%Z ->
      Z.to_nat len' <= int_to_nat max_length ->
      eval locals h1 def h2 (value_Int (Int, k)) ->
      is_true (Z.leb 0%Z k && Z.ltb k 256) ->
      fresh h2 ptr h3 -> 
      update h3 ptr (List.init (Z.to_nat len') (fun _ => (value_Int (Int, k)))) h4 ->
      eval locals h (Mvecnew (Bytevec, len, def)) 
                  h4 (if Z.leb 0%Z k && Z.ltb k 256 
                      then Vec (Bytevec, ptr)
                      else fail "bad vector creation")
| eval_vecget h h1 h2 vec ty' idx idx' ty ptr arr : 
    eval locals h vec h1 (Vec (ty', ptr)) -> 
    eval locals h1 idx h2 idx' ->
    deref h ptr arr ->
    eval locals h (Mvecget (ty, vec, idx)) 
                h2 (match idx' with
       | value_Int (Int,i) =>
           if vector_type_eqb ty ty' then
             if Z.leb 0 i && Z.ltb i (Z.of_nat (List.length arr)) then
               nth (Z.to_nat i) arr (fail "")
             else
               fail "index out of bounds: %d"
           else
             fail "wrong vector type"
       | _ => fail "wrong vector type"
       end)
  | eval_vecset h h1 h2 h3 h4 vec ty ty' ptr idx i e v arr :  
    eval locals h vec h1 (Vec (ty', ptr)) -> 
    eval locals h1 idx h2 (value_Int (Int, i)) ->
    eval locals h2 e h3 v ->
    deref h ptr arr -> 
    update h3 ptr (List.set arr (Z.to_nat i) v) h4 ->
    eval locals h (Mvecset (ty, vec, idx, e)) 
        (if vector_type_eqb ty ty' then 
           if Z.leb 0 i && Z.ltb i (Z.of_nat (List.length arr)) then 
             match ty, v with 
              | Array, _ => h4
              | Bytevec, value_Int (Int, val) => 
                if (Z.leb 0 val) && (Z.ltb val 256)
                then h4
                else h3
              | Bytevec, _ => h3
              end 
            else h3
          else h3)
        (if vector_type_eqb ty ty' then 
           if Z.leb 0 i && Z.ltb i (Z.of_nat (List.length arr)) then 
             match ty, v with 
              | Array, _ => value_Int (Int, 0%Z)
              | Bytevec, value_Int (Int, val) => 
                  if (Z.leb 0 val) && (Z.ltb val 256)
                  then value_Int (Int, 0%Z)
                  else fail "not a byte"
              | Bytevec, _ => fail "not a byte"
            end 
           else fail "index out of bounds: %d"
         else fail "wrong vector type")  
| eval_veclen h h' vec ty' ptr ty arr : 
  eval locals h vec h' (Vec (ty', ptr)) -> 
  deref h ptr arr -> 
  eval locals h (Mveclen (ty, vec)) 
              h' (if vector_type_eqb ty ty' then value_Int (Int, Z.of_nat (List.length arr))
                                    else fail "wrong vector type")
.

Lemma eval_ind :
forall P : Ident.Map.t -> heap -> t -> heap -> value -> Prop,
       (forall (locals : Ident.Map.t) (h : heap) (x : Ident.t) (e : t),
        P locals h (Mlambda ([x], e)) h (Func (locals, x, e))) ->
       (forall (locals : Ident.Map.t) (h : heap) (x : Ident.t)
          (ids : list Ident.t) (e : t),
        Datatypes.length ids > 0 ->
        P locals h (Mlambda (x :: ids, e)) h
          (Func (locals, x, Mlambda (ids, e)))) ->
       (forall (locals : Ident.Map.t) (h h1 h2 h3 : heap) 
          (x : Ident.t) (locals' : Ident.Map.t) (e e2 : t) 
          (v2 : value) (e1 : t) (v : value),
        eval locals h e1 h1 (Func (locals', x, e)) ->
        P locals h e1 h1 (Func (locals', x, e)) ->
        eval locals h1 e2 h2 v2 ->
        P locals h1 e2 h2 v2 ->
        eval (Ident.Map.add x v2 locals') h2 e h3 v ->
        P (Ident.Map.add x v2 locals') h2 e h3 v ->
        P locals h (Mapply (e1, [e2])) h3 v) ->
       (forall (locals : Ident.Map.t) (h h1 h2 h3 : heap)
          (mfix : list rec_value) (n : nat) (y : Ident.t) 
          (e : t) (locals'  : Ident.Map.t) self
          (e2 : t) (v2 : value) (e1 : t) (v : value),
        eval locals h e1 h1 (RClos (locals', self, mfix, n)) ->
        P locals h e1 h1 (RClos (locals', self, mfix, n)) ->
        eval locals h1 e2 h2 v2 ->
        P locals h1 e2 h2 v2 ->
        nth n mfix Bad_recursive_value = RFunc (y, e) ->
        eval (Ident.Map.add y v2 (add_self self mfix locals')) h2 e h3 v ->
        P (Ident.Map.add y v2 (add_self self mfix locals')) h2 e h3 v ->
        P locals h (Mapply (e1, [e2])) h3 v) ->
       (forall (locals : Ident.Map.t) (h h1 : heap) (e2 e1 : t) (v : value),
        eval locals h e1 h1 v ->
        P locals h e1 h1 v ->
        isFunction v = false ->
        P locals h (Mapply (e1, [e2])) h1
          (fail "not a function:  evaluated to: ")) ->
       (forall (locals : Ident.Map.t) (h h1 : heap) 
          (e3 e2 e1 : t) (v : value) (es : list t),
        eval locals h (Mapply (Mapply (e1, [e2]), e3 :: es)) h1 v ->
        P locals h (Mapply (Mapply (e1, [e2]), e3 :: es)) h1 v ->
        P locals h (Mapply (e1, e2 :: e3 :: es)) h1 v) ->
       (forall (locals : Ident.Map.t) (h : heap) (id : Ident.t),
        P locals h (Mvar id) h (Ident.Map.find id locals)) ->
       (forall (locals : Ident.Map.t) (h h1 : heap) (e : t) (v : value),
        eval locals h e h1 v ->
        P locals h e h1 v -> P locals h (Mlet ([], e)) h1 v) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap) 
          (e1 : t) (v1 : value) (lts : list binding) 
          (e2 : t) (v : value),
        eval locals h e1 h1 v1 ->
        P locals h e1 h1 v1 ->
        eval locals h1 (Mlet (lts, e2)) h2 v ->
        P locals h1 (Mlet (lts, e2)) h2 v ->
        P locals h (Mlet (Unnamed e1 :: lts, e2)) h2 v) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap) 
          (x : Ident.t) (e1 : t) (v1 : value) (lts : list binding) 
          (e2 : t) (v : value),
        eval locals h e1 h1 v1 ->
        P locals h e1 h1 v1 ->
        eval (Ident.Map.add x v1 locals) h1 (Mlet (lts, e2)) h2 v ->
        P (Ident.Map.add x v1 locals) h1 (Mlet (lts, e2)) h2 v ->
        P locals h (Mlet (Named (x, e1) :: lts, e2)) h2 v) ->
       (forall (locals : Ident.Map.t) (h h1 : heap)
          (recs : list (Ident.t * t)) (newlocals : Ident.Map.t)
          (lts : list binding) (e2 : t) (v : value),
        let self := map fst recs in
        let rfunc := RFunc_build (map snd recs) in
        newlocals =
        fold_right (fun '(x, t) (l : Ident.Map.t)  => Ident.Map.add x t l)
          locals (add_recs locals self rfunc) ->
        eval newlocals h (Mlet (lts, e2)) h1 v ->
        P newlocals h (Mlet (lts, e2)) h1 v ->
        P locals h (Mlet (Recursive recs :: lts, e2)) h1 v) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap) 
          (scr : t) (cases : list (list case * t)) 
          (v v' : value) (e : t),
        eval locals h scr h1 v' ->
        P locals h scr h1 v' ->
        find_match v' cases = Some e ->
        eval locals h1 e h2 v ->
        P locals h1 e h2 v -> P locals h (Mswitch (scr, cases)) h2 v) ->
       (forall (locals : Ident.Map.t) (tag : Malfunction.int) 
          (h h' : heap) (es : list t) (vals : list value),
        Datatypes.length vals < int_to_nat max_length ->
        Forall2_acc (fun a b c d => eval locals a b c d /\ P locals a b c d) h es h' vals ->
        P locals h (Mblock (tag, es)) h' (Block (tag, vals))) ->
       (forall (locals : Ident.Map.t) (h h' : heap) 
          (idx : Malfunction.int) (b : t) (vals : list value)
          (tag : Malfunction.int),
        eval locals h b h' (Block (tag, vals)) ->
        P locals h b h' (Block (tag, vals)) ->
        Datatypes.length vals <= int_to_nat max_length ->
        int_to_nat idx < Datatypes.length vals ->
        P locals h (Mfield (idx, b)) h' (nth (int_to_nat idx) vals (fail ""))) ->
       (forall (locals : Ident.Map.t) (h h' : heap) 
          (idx : Malfunction.int) (b : t) (v : value),
        eval locals h b h' v ->
        P locals h b h' v ->
        isBlock v = false ->
        P locals h (Mfield (idx, b)) h' (fail "not a block")) ->
       (forall (locals : Ident.Map.t) (h h' h'' : heapGen value)
          (ptr : pointer) (e : t),
        let arr := [not_evaluated; Lazy (locals, e)] in
        fresh h ptr h' ->
        update h' ptr arr h'' -> P locals h (Mlazy e) h'' (Thunk ptr)) ->
       (forall (locals : Ident.Map.t) (h h' : heap) 
          (e : t) (ptr : pointer) (vals : list value) 
          (lazy : value),
        eval locals h e h' (Thunk ptr) ->
        P locals h e h' (Thunk ptr) ->
        deref h' ptr vals ->
        Datatypes.length vals > 1 ->
        nth 0 vals (fail "") = lazy ->
        isNotEvaluated lazy = false -> P locals h (Mforce e) h' lazy) ->
       (forall (locals : Ident.Map.t) (h h' h'' : heap)
          (h''' : heapGen value) (ptr : pointer) (vals : list value)
          (locals' : Ident.Map.t) (e : t) (v : value),
        eval locals h e h' (Thunk ptr) ->
        P locals h e h' (Thunk ptr) ->
        deref h' ptr vals ->
        Datatypes.length vals = 2 ->
        isNotEvaluated (nth 0 vals (fail "")) = true ->
        nth 1 vals (fail "") = Lazy (locals', e) ->
        eval locals' h' e h'' v ->
        P locals' h' e h'' v ->
        update h'' ptr [v; Lazy (locals', e)] h''' ->
        P locals h (Mforce e) h''' v) ->
       (forall (locals : Ident.Map.t) (h h' : heap) (e : t) (v : value),
        eval locals h e h' v ->
        P locals h e h' v ->
        isThunk v = false ->
        P locals h (Mforce e) h' (fail "not a lazy value")) ->
       (forall (locals : Ident.Map.t) (h : heap) (nm : Ident.t) (v : value),
        In (nm, v) globals -> P locals h (Mglobal nm) h v) ->
       (forall (locals : Ident.Map.t) (n : Malfunction.int) (h : heap),
        P locals h (Mnum (numconst_Int n)) h (value_Int (Int, φ (n)%uint63))) ->
       (forall (locals : Ident.Map.t) (n : Z) (h : heap),
        P locals h (Mnum (numconst_Bigint n)) h (value_Int (Bigint, n))) ->
       (forall (locals : Ident.Map.t) (f21 : float) (h : heap),
        P locals h (Mnum (numconst_Float64 f21)) h (Float f21)) ->
       (forall (locals : Ident.Map.t) (s : string) 
          (h h' h'' : heapGen value) (ptr : pointer),
        String.length s < int_to_nat max_length ->
        let str :=
          List.init (String.length s)
            (fun i : nat =>
             value_Int
               (Int,
                Z.of_nat
                  (Byte.to_nat (option_def (Ascii.byte_of_ascii Ascii.Space) (get i s)))))
          in
        fresh h ptr h' ->
        update h' ptr str h'' ->
        P locals h (Mstring s) h'' (Vec (Bytevec, ptr))) ->
       (forall (locals : Ident.Map.t) (op : unary_num_op) 
          (ty : inttype) (e : t) (h h' : heap) (v : value),
        eval locals h e h' v ->
        P locals h e h' v ->
        let n := as_ty ty v in
        P locals h (Mnumop1 (op, embed_inttype ty, e)) h'
          (truncate ty
             match op with
             | Malfunction.Neg => -1 * n
             | Not => Z.lnot n
             end)) ->
       (forall (locals : Ident.Map.t) (op : binary_num_op) 
          (ty : inttype) (e1 e2 : t) (v1 v2 : value) 
          (h h1 h2 : heap),
        eval locals h e1 h1 v1 ->
        P locals h e1 h1 v1 ->
        eval locals h1 e2 h2 v2 ->
        P locals h1 e2 h2 v2 ->
        P locals h (Mnumop2 (op, embed_inttype ty, e1, e2)) h2
          match op with
          | embed_binary_arith_op op0 =>
              let f24 :=
                match op0 with
                | Malfunction.Add => Z.add
                | Sub => Z.sub
                | Mul => Z.mul
                | Div => Z.div
                | Mod => Z.rem
                end in
              truncate ty (f24 (as_ty ty v1) (as_ty ty v2))
          | embed_binary_bitwise_op op0 =>
              let n := as_ty ty v1 in
              let c := as_ty Int v2 in
              truncate ty
                match op0 with
                | And => Z.land (as_ty ty v1) (as_ty ty v2)
                | Or => Z.lor (as_ty ty v1) (as_ty ty v2)
                | Xor => Z.lxor (as_ty ty v1) (as_ty ty v2)
                | Lsl => Z.shiftl n c
                | Lsr =>
                    let n0 :=
                      match ty with
                      | Bigint => n
                      | _ =>
                          let w := bitwidth ty in
                          Z.land n (Z.shiftl (Z.of_nat 1) w - Z.of_nat 1)
                      end in
                    Z.shiftr n0 c
                | Asr => Z.shiftr n c
                end
          | embed_binary_comparison op0 =>
              let cmp := (as_ty ty v1 ?= as_ty ty v2)%Z in
              let res := binary_comparison_eqb op0 cmp in
              value_Int (Int, if res then 1%Z else 0%Z)
          end) ->
       (forall (locals : Ident.Map.t) (e : t) (h h' : heap) (v : value),
        eval locals h e h' v ->
        P locals h e h' v ->
        P locals h (Mnumop1 (Malfunction.Neg, Float64, e)) h'
          (Float (- as_float v))) ->
       (forall (locals : Ident.Map.t) (h : heap) (x : t),
        P locals h (Mnumop1 (Not, Float64, x)) h
          (fail "invalid bitwise float operation")) ->
       (forall (locals : Ident.Map.t) (h : heap) (x y : t)
          (n : binary_bitwise_op),
        P locals h (Mnumop2 (embed_binary_bitwise_op n, Float64, x, y)) h
          (fail "invalid bitwise float operation")) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap) 
          (op : binary_arith_op) (e1 e2 : t) (v1 v2 : value),
        eval locals h e1 h1 v1 ->
        P locals h e1 h1 v1 ->
        eval locals h1 e2 h2 v2 ->
        P locals h1 e2 h2 v2 ->
        let v1' := as_float v1 in
        let v2' := as_float v2 in
        P locals h (Mnumop2 (embed_binary_arith_op op, Float64, e1, e2)) h2
          (Float (binary_op_to_float op v1' v2'))) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap)
          (op : binary_comparison) (e1 e2 : t) (v1 v2 : value),
        eval locals h e1 h1 v1 ->
        P locals h e1 h1 v1 ->
        eval locals h1 e2 h2 v2 ->
        P locals h1 e2 h2 v2 ->
        let v1' := as_float v1 in
        let v2' := as_float v2 in
        let res := binary_comparison_to_bool op v1' v2' in
        P locals h (Mnumop2 (embed_binary_comparison op, Float64, e1, e2)) h2
          (value_Int (Int, if res then 1%Z else 0%Z))) ->
       (forall (locals : Ident.Map.t) (h h' : heap) 
          (e : t) (v : value) (src dst : inttype),
        eval locals h e h' v ->
        P locals h e h' v ->
        P locals h (Mconvert (embed_inttype src, embed_inttype dst, e)) h'
          (truncate dst (as_ty src v))) ->
       (forall (locals : Ident.Map.t) (h h' : heap) 
          (e : t) (v : value) (src : inttype),
        eval locals h e h' v ->
        P locals h e h' v ->
        P locals h (Mconvert (embed_inttype src, Float64, e)) h'
          (Float (of_uint63 (Int63.of_Z (as_ty src v))))) ->
       (forall (locals : Ident.Map.t) (h h' : heap) (v : value) (e : t),
        eval locals h e h' v ->
        P locals h e h' v ->
        P locals h (Mconvert (Float64, Float64, e)) h' (Float (as_float v))) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap)
          (h3 h4 : heapGen value) (len : t) (len' : Z) 
          (def : t) (def' : value) (ptr : pointer),
        eval locals h len h1 (value_Int (Int, len')) ->
        (0 <= len')%Z -> 
        Z.to_nat len' <= int_to_nat max_length ->
        P locals h len h1 (value_Int (Int, len')) ->
        eval locals h1 def h2 def' ->
        P locals h1 def h2 def' ->
        fresh h2 ptr h3 ->
        update h3 ptr (List.init (Z.to_nat len') (fun _ : nat => def')) h4 ->
        P locals h (Mvecnew (Array, len, def)) h4 (Vec (Array, ptr))) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap)
          (h3 h4 : heapGen value) (len : t) (len' : Z) 
          (def : t) (k : Z) (ptr : pointer),
        eval locals h len h1 (value_Int (Int, len')) ->
        (0 <= len')%Z -> 
        Z.to_nat len' <= int_to_nat max_length ->
        P locals h len h1 (value_Int (Int, len')) ->
        eval locals h1 def h2 (value_Int (Int, k)) ->
        is_true (Z.leb 0%Z k && Z.ltb k 256) ->
        P locals h1 def h2 (value_Int (Int, k)) ->
        fresh h2 ptr h3 ->
        update h3 ptr
          (List.init (Z.to_nat len') (fun _ : nat => value_Int (Int, k))) h4 ->
        P locals h (Mvecnew (Bytevec, len, def)) h4
          (if ((0 <=? k)%Z && (k <? 256)%Z)%bool
           then Vec (Bytevec, ptr)
           else fail "bad vector creation")) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap) 
          (vec : t) (ty' : vector_type) (idx : t) 
          (idx' : value) (ty : vector_type) (ptr : pointer)
          (arr : list value),
        eval locals h vec h1 (Vec (ty', ptr)) ->
        P locals h vec h1 (Vec (ty', ptr)) ->
        eval locals h1 idx h2 idx' ->
        P locals h1 idx h2 idx' ->
        deref h ptr arr ->
        P locals h (Mvecget (ty, vec, idx)) h2
          match idx' with
          | value_Int (Int, i) =>
              if vector_type_eqb ty ty'
              then
               if
                ((0 <=? i)%Z && (i <? Z.of_nat (Datatypes.length arr))%Z)%bool
               then nth (Z.to_nat i) arr (fail "")
               else fail "index out of bounds: %d"
              else fail "wrong vector type"
          | _ => fail "wrong vector type"
          end) ->
       (forall (locals : Ident.Map.t) (h h1 h2 h3 : heap)
          (h4 : heapGen value) (vec : t) (ty ty' : vector_type)
          (ptr : pointer) (idx : t) (i : Z) (e : t) 
          (v : value) (arr : list value),
        eval locals h vec h1 (Vec (ty', ptr)) ->
        P locals h vec h1 (Vec (ty', ptr)) ->
        eval locals h1 idx h2 (value_Int (Int, i)) ->
        P locals h1 idx h2 (value_Int (Int, i)) ->
        eval locals h2 e h3 v ->
        P locals h2 e h3 v ->
        deref h ptr arr ->
        update h3 ptr (List.set arr (Z.to_nat i) v) h4 ->
        P locals h (Mvecset (ty, vec, idx, e)) 
        (if vector_type_eqb ty ty' then 
           if Z.leb 0 i && Z.ltb i (Z.of_nat (List.length arr)) then 
             match ty, v with 
              | Array, _ => h4
              | Bytevec, value_Int (Int, val) => 
                if (Z.leb 0 val) && (Z.ltb val 256)
                then h4
                else h3
              | Bytevec, _ => h3
              end 
            else h3
          else h3)
        (if vector_type_eqb ty ty' then 
           if Z.leb 0 i && Z.ltb i (Z.of_nat (List.length arr)) then 
             match ty, v with 
              | Array, _ => value_Int (Int, 0%Z)
              | Bytevec, value_Int (Int, val) => 
                  if (Z.leb 0 val) && (Z.ltb val 256)
                  then value_Int (Int, 0%Z)
                  else fail "not a byte"
              | Bytevec, _ => fail "not a byte"
            end 
           else fail "index out of bounds: %d"
         else fail "wrong vector type")) ->
       (forall (locals : Ident.Map.t) (h h' : heap) 
          (vec : t) (ty' : vector_type) (ptr : pointer) 
          (ty : vector_type) (arr : list value),
        eval locals h vec h' (Vec (ty', ptr)) ->
        P locals h vec h' (Vec (ty', ptr)) ->
        deref h ptr arr ->
        P locals h (Mveclen (ty, vec)) h'
          (if vector_type_eqb ty ty'
           then value_Int (Int, Z.of_nat (Datatypes.length arr))
           else fail "wrong vector type")) ->
forall (locals : Ident.Map.t) (h : heap) (t : t) 
         (h0 : heap) (v : value), eval locals h t h0 v -> P locals h t h0 v.
Proof.
  intros. 
  revert locals h t h0 v H38.
  fix f 6. intros locals h t h' v [| | | | | | | | | | | | ? ? ? ? ? Hforall | | | | | | | | | | | | | | | | | | | | | | | | | |].
  1-12, 15-39:eauto.
  - eapply H11; eauto. induction Hforall; try econstructor; eauto. 
    eapply IHHforall. cbn in *. lia.  
  - eapply H12. 1: eauto. 1: eauto. all: lia.
Qed.
Set Elimination Schemes.

End eval.

Derive Signature for eval.
