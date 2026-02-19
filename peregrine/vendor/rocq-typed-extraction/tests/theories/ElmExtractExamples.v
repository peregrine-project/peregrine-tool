(** * Examples for extraction to Elm *)

(** The examples are written into files that are later processed
    and passed to the Elm compiler as part of the building process. *)

(** Warning: this file does not work in the interactive mode due to
    the problems with paths for [Redirect]. We have to stick to the path,
    relative to the project root and in the interactive mode current
    directory is different. *)
From TypedExtraction.Common Require Import StringExtra.
From TypedExtraction.Common Require Import Common.
From MetaRocq.Erasure.Typed Require Import Extraction.
From TypedExtraction.Elm Require Import ElmExtract.
From TypedExtraction.Common Require Import PrettyPrinterMonad.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import Optimize.
From MetaRocq.Erasure.Typed Require Import CertifyingEta.
From TypedExtraction.Tests Require Import ElmExtractTests.
From TypedExtraction.Tests Require Import Ack.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Template Require Import Ast.
From MetaRocq.Template Require Import TemplateMonad.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.

Import MRMonadNotation.
Local Open Scope bs_scope.

#[local]
Instance ElmBoxes : ElmPrintConfig :=
  {| term_box_symbol := "()"; (* the inhabitant of the unit type *)
     type_box_symbol := "()"; (* unit type *)
     any_type_symbol := "()"; (* unit type *)
     false_elim_def := "false_rec ()"; (* predefined function *)
     print_full_names := false (* short names for readability *)|}.

Definition no_check_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true true false false false] |} |}.

Definition result_err_bytestring A := result A bytestring.String.t.

Definition general_wrapped (p : program) (pre post : string)
  (ignore: list kername) (TT : list (kername * string)) : result_err_bytestring _ :=
  entry <- match p.2 with
           | tConst kn _ => ret kn
           | _ => Err "Expected program to be a tConst"
           end;;
  Σ <- extract_template_env
         no_check_args
         p.1
         (KernameSet.singleton entry)
         (fun k => existsb (eq_kername k) ignore);;
  let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
  '(_, s) <- (finish_print (print_env Σ TT_fun));;
  ret (pre ++ Common.nl ++ s ++ Common.nl ++ post).

Definition wrapped (p : program) (pre post : string) : result _ _ :=
  general_wrapped p pre post [] [].

Module ElmExamples.

  Import Lia.

  Definition Preambule mod_name :=
    bytestring.String.concat Common.nl
           ["module " ++ mod_name ++ " exposing (..)";
            "import Test";
            "import Html";
            "import Expect exposing (Expectation)"].

  Definition main_and_test (test : string) :=
    "main = Html.text "++
      Common.parens false ("Debug.toString " ++ Common.parens false test) ++ Common.nl ++
    "suite = Test.test (Debug.toString 1)" ++ Common.parens false ("\ _ -> " ++ test).

  (* [safe_pred] example is inspired by Letozey's A New Extraction for Rocq *)
  Definition safe_pred (n:nat) (not_zero : O<>n) : {p :nat | n=(S p)} :=
    match n as n0 return (n0 = n -> _ -> _ )with
    | O => fun heq h => False_rect _ (ltac:(cbn; intros; easy))
    | S m => fun heq h => exist m eq_refl
    end eq_refl not_zero.

  Program Definition safe_pred_full := safe_pred 1 (ltac:(easy)).
  Program Definition safe_pred_partial := safe_pred 1.

  MetaRocq Run (t <- tmQuoteRecTransp safe_pred_full false ;;
               tmDefinition "safe_pred_full_syn" t).

  (* In fully applied case the last argument of [safe_pred] is removed*)
  Redirect "elm/elm-extract/SafePredFull.elm"
  Compute general_wrapped safe_pred_full_syn
    (Preambule "SafePredFull" ++ Common.nl ++ elm_false_rec)
    (main_and_test "Expect.equal safe_pred_full (Exist O)")
    [] [].

  MetaRocq Run (t <- tmQuoteRecTransp safe_pred_partial false ;;
               mpath <- tmCurrentModPath tt;;
               Σeta <- run_transforms_list t.1
                 [template_eta (fun _ => None) true true [<%% @safe_pred_partial %%>] (fun _ => false)] ;;

               Certifying.gen_defs_and_proofs (declarations t.1) (declarations Σeta) mpath "_cert_pass"
                                              (KernameSet.singleton <%% @safe_pred_partial %%> )).

  MetaRocq Run (t <- tmQuoteRecTransp TypedExtraction_Tests_ElmExtractExamples_ElmExamples_safe_pred_partial_cert_pass false;;
               tmDefinition "safe_pred_partial_syn" t).

  (* After eta-expansion the main [safe_pred_partial] is guarded by a lambda *)

  Redirect "elm/elm-extract/SafePredPartial.elm"
  Compute general_wrapped safe_pred_partial_syn
          (Preambule "SafePredPartial" ++ Common.nl ++ elm_false_rec)
          (main_and_test "Expect.equal (typedExtraction_Tests_ElmExtractExamples_ElmExamples_safe_pred_partial_cert_pass ()) (Exist O)")
          [] [].


  MetaRocq Quote Recursively Definition rev_syn := List.rev.

  Definition ackermann := Eval compute in ack.

  MetaRocq Run (t <- tmQuoteRecTransp ackermann false ;;
               tmDefinition "ackermann_syn" t).

  Redirect "elm/elm-extract/Ackermann.elm"
  Compute wrapped ackermann_syn
          (Preambule "Ackermann")
          (main_and_test "Expect.equal (ackermann (Pair (S (S (S O))) (S (S (S O))))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))").

  Redirect "elm/elm-extract/Rev.elm"
           Compute wrapped rev_syn
           (Preambule "Rev")
           (main_and_test "Expect.equal (rev (Cons 3 (Cons 2 (Cons 1 (Cons 0 Nil))))) (Cons 0 (Cons 1 (Cons 2 (Cons 3 Nil))))").

  MetaRocq Quote Recursively Definition nth_syn := nth.

  Definition result_nth :=
    <$ "type Nat";
       "  = O";
       "  | S Nat";
       "";
       "type List a";
       "  = Nil";
       "  | Cons a (List a)";
       "";
       "nth : Nat -> List a -> a -> a";
       "nth n l default =";
       "  case n of";
       "    O ->";
       "      case l of";
       "        Nil ->";
       "          default";
       "        Cons x l2 ->";
       "          x";
       "    S m ->";
       "      case l of";
       "        Nil ->";
       "          default";
       "        Cons x l2 ->";
       "          nth m l2 default" $>.

  Example ElmExamples_nth :
    extract nth_syn = Ok result_nth.
  Proof. vm_compute. reflexivity. Qed.

  Redirect "elm/elm-extract/Nth.elm"
  Compute wrapped nth_syn
  (Preambule "Nth")
  (main_and_test "Expect.equal (nth O (Cons 1 (Cons 0 Nil)) 0) 1").

  MetaRocq Quote Recursively Definition map_syn := map.
  Definition result_map :=
    <$ "type List a";
       "  = Nil";
       "  | Cons a (List a)";
         "";
       "map : (a -> b) -> List a -> List b";
       "map f =";
       "  let";
       "    map2 l =";
       "      case l of";
       "        Nil ->";
       "          Nil";
       "        Cons a l2 ->";
       "          Cons (f a) (map2 l2)";
       "  in";
       "  map2" $>.

  Redirect "elm/elm-extract/Map.elm"
  Compute wrapped map_syn
  (Preambule "Map")
  (main_and_test "Expect.equal (map (\x->x+1) (Cons 1 (Cons 0 Nil))) (Cons 2 (Cons 1 Nil))").

  Example ElmList_map :
    extract map_syn = Ok result_map.
  Proof. vm_compute. reflexivity. Qed.

  MetaRocq Quote Recursively Definition foldl_syn := fold_left.
  Definition result_foldl :=
  <$ "type List a";
      "  = Nil";
      "  | Cons a (List a)";
        "";
      "fold_left : (a -> b -> a) -> List b -> a -> a";
      "fold_left f =";
        "  let";
      "    fold_left2 l a0 =";
      "      case l of";
      "        Nil ->";
      "          a0";
      "        Cons b l2 ->";
      "          fold_left2 l2 (f a0 b)";
      "  in";
      "  fold_left2" $>.

  Redirect "elm/elm-extract/Fold.elm"
  Compute wrapped foldl_syn
  (Preambule "Fold")
  (main_and_test "(Expect.equal (fold_left (+) (Cons 1 (Cons 0 Nil)) 0)) 1").

  Example ElmList_foldl :
    extract foldl_syn = Ok result_foldl.
  Proof. vm_compute. reflexivity. Qed.

  Local Open Scope nat.
  Program Definition inc_counter (st : nat) (inc : {z : nat | 0 <? z}) :
    {new_st : nat | st <? new_st} :=
    st + inc.
  Next Obligation.
    unfold is_true in *.
    rewrite Nat.ltb_lt in *. lia.
  Qed.

  MetaRocq Run (t <- tmQuoteRecTransp inc_counter false ;;
               tmDefinition "inc_counter_syn" t).

  Redirect "elm/elm-extract/Increment.elm"
  Compute wrapped inc_counter_syn
         (Preambule "Increment")
         (main_and_test "Expect.equal (inc_counter O (Exist (S O))) (Exist (S O))").

  MetaRocq Quote Recursively Definition last_syn := List.last.

  Redirect "elm/elm-extract/Last.elm"
  Compute wrapped last_syn
  (Preambule "Last")
  (main_and_test "Expect.equal (last (Cons 1 (Cons 10 Nil)) 0) 10").

  Program Definition safe_head {A} (non_empty_list : {l : list A | List.length l > 0}) : A :=
    match non_empty_list as l' return l' = non_empty_list -> A with
    | [] =>
      (* NOTE: we use [False_rect] to make the extracted code a bit nicer.
         It's totally possible to leave the whole branch as an obligation,
         the extraction will handle it.
         However, if the whole branch is an obligation, the proof it should
         be left transparent (using [Defined]), so the extraction could
         produce reasonable code for it. If left opaque, the body of
         the obligation will be ignored by extraction producing no
         corresponding definition *)
      fun _ => False_rect _ _
    | hd :: tl => fun _ => hd
    end eq_refl.
  Next Obligation.
    intros; cbn in*; lia.
  Qed.

  Program Definition head_of_repeat_plus_one {A} (n : nat) (a : A) : A :=
    safe_head (repeat a (1+n)).
  Next Obligation.
    intros. cbn. lia.
  Qed.

  MetaRocq Run (t <- tmQuoteRecTransp (@head_of_repeat_plus_one) false ;;
               tmDefinition "head_of_repeat_plus_one_syn" t).

  Redirect "elm/elm-extract/SafeHead.elm"
  Compute general_wrapped head_of_repeat_plus_one_syn
  (Preambule "SafeHead" ++ Common.nl ++ elm_false_rec)
  (main_and_test "Expect.equal (head_of_repeat_plus_one (S O) 1) 1")
  [] [].

End ElmExamples.
