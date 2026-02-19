From Stdlib Require Import String.
From Ceres Require Import Ceres.
Set Warnings "-masking-absolute-name".
From Malfunction Require Import Pipeline Serialize CeresFormat CeresSerialize Interpreter.

From MetaRocq Require Import ETransform Common.Transform Utils.bytestring.
From MetaRocq.Template Require All Loader TemplateMonad.
Open Scope bs.

Import Transform.

Definition Mlet_ '(l, b) :=
  match l with
  | nil => b
  | _ => Malfunction.Mlet (l, b)
  end.

Local Existing Instance SemanticsSpec.CanonicalPointer.
Local Existing Instance SemanticsSpec.CanonicalHeap.

Definition eval_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : string :=
  let p' := run (malfunction_pipeline Pipeline.default_malfunction_config) (nil, p) (MRUtils.todo "wf_env and welltyped term"%bs) in
  let t := Mlet_ (MRList.rev_map Malfunction.Named (List.flat_map (fun '(x, d) => match d with Some b => cons (x,b) nil | None => nil end) (fst p')), snd p') in
  time "Pretty printing"%bs (@to_string _ Serialize_t) t.

Definition eval_malfunction_sexp (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : Malfunction.t :=
  let p' := run (malfunction_pipeline default_malfunction_config) (nil,p) (MRUtils.todo "wf_env and welltyped term"%bs) in
  let t := Mlet_ (MRList.rev_map Malfunction.Named (List.flat_map (fun '(x, d) => match d with Some b => cons (x,b) nil | None => nil end) (fst p')), snd p') in
  time "Pretty printing"%bs id t.

Section something.

Import Loader All.
Import MRMonadNotation.

Definition extract {A : Type} (a : A) :=
  t <- tmQuoteRec a ;;
  s <- tmEval lazy (eval_malfunction t) ;;
  tmMsg s ;; tmReturn tt.

Definition extract_def {A : Type} (a : A) (nm : string) :=
  t <- tmQuoteRec a ;;
  s <- tmEval lazy (eval_malfunction_sexp t) ;;
  tmDefinition nm s.

End something.

Notation "'Extraction' a" :=
  (extract a) (at level 1, a at level 2).

Inductive three := ZERO | ONE | TWO | THREE.

MetaRocq Run Extraction (match cons THREE nil with cons x _ => x | _ => ONE end).
MetaRocq Run Extraction plus.

Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.

MetaRocq Run Extraction (ack 3 5).

MetaRocq Run Extraction (@exist nat (fun x => x = 0) 0 (@eq_refl _ 0)).

Definition vplus {n:nat} :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := Vector.hd (vplus v01 v23).

MetaRocq Run Extraction vplus0123.

Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.
Arguments leaf {A}.
Arguments fcons {A}.
Arguments node {A}.

Fixpoint tree_size (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool) : nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).

MetaRocq Run Extraction (forest_size arden).
