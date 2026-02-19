From Stdlib Require Import String List.
From Ceres Require Import Ceres.
Set Warnings "-masking-absolute-name".
From CakeML Require Import Pipeline Serialize.
From CakeML Require Import ast namespace.
From MetaRocq Require Import ETransform Common.Transform Utils.bytestring.
From MetaRocq.Template Require All Loader TemplateMonad.
Open Scope bs.
Import ListNotations.
Import Transform.

  Fixpoint Mlet_ l b :=
  match l with
  | nil => b
  | cons (name,e) xs => Let (Some (String.to_string (name))) e (Mlet_ xs b)
  end.

(* Local Existing Instance SemanticsSpec.CanonicalPointer.
Local Existing Instance SemanticsSpec.CanonicalHeap. *)


 Definition eval_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : string :=
  let p' := run (malfunction_pipeline Pipeline.default_malfunction_config) (nil, p) (MRUtils.todo "wf_env and welltyped term"%bs) in
  let t := Mlet_ (List.flat_map (fun '(x, d) => match d with Some b => cons (x,b) nil | None => nil end) (fst p')) (snd p') in
  time "Pretty printing"%bs ( @to_string _ Serialize_t) t.

Definition eval_malfunction_sexp (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : exp :=
  let p' := run (malfunction_pipeline default_malfunction_config) (nil,p) (MRUtils.todo "wf_env and welltyped term"%bs) in
  let t :=  Mlet_ (List.flat_map (fun '(x, d) => match d with Some b => cons (x,b) nil | None => nil end) (fst p')) (snd p') in
  time "Pretty printing"%bs Corelib.Init.Datatypes.id t. 

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

MetaRocq Run Extraction (match tt with tt => tt end).
(Let (SOME "discr") (Con (SOME (Short "tt")) nil)
   (Mat (Var (Short "discr"))
      (((Pcon (SOME (Short "tt")) nil) (Con (SOME (Short "tt")) nil)))))


(Let (SOME "discr") (Con (SOME (Short "Tt")) nil)
   (Mat (Var (Short "discr"))
      (((Pcon (SOME (Short "Tt")) nil) (Con (SOME (Short "Tt")) nil)))))

