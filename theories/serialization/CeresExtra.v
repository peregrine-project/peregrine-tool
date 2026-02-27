From Stdlib Require Import List.
From Ceres Require Import Ceres.
From Ceres Require Import CeresUtils.
From Ceres Require CeresParserUtils.
From Ceres Require CeresString.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require All_Forall.

Import ListNotations.

Local Notation "p >>= f" := (Deser.bind_field p f) (at level 50, left associativity) : deser_scope.
Local Open Scope deser_scope.



(* Helper functions for Deser.match_con *)

Definition con0 {R} (r : R)
  : FromSexpList R :=
  Deser.fields (Deser.ret r).

Definition con1
  {A R}
  (f : A -> R)
  : FromSexp A -> FromSexpList R :=
  fun pa =>
    Deser.fields (
      pa >>= fun a =>
        Deser.ret (f a)).

Definition con1_
  {A R}
  (f : A -> R)
  `{Deserialize A}
  : FromSexpList R :=
  con1 f _from_sexp.

Definition con2
  {A B R}
  (f : A -> B -> R)
  : FromSexp A -> FromSexp B -> FromSexpList R :=
  fun pa pb =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b =>
        Deser.ret (f a b)).

Definition con2_
  {A B R}
  (f : A -> B -> R)
  `{Deserialize A} `{Deserialize B}
  : FromSexpList R :=
  con2 f _from_sexp _from_sexp.

Definition con3
  {A B C R}
  (f : A -> B -> C -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexpList R :=
  fun pa pb pc =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c =>
        Deser.ret (f a b c)).

Definition con3_
  {A B C R}
  (f : A -> B -> C -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C}
  : FromSexpList R :=
  con3 f _from_sexp _from_sexp _from_sexp.

Definition con4
  {A B C D R}
  (f : A -> B -> C -> D -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexpList R :=
  fun pa pb pc pd =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d =>
        Deser.ret (f a b c d)).

Definition con4_
  {A B C D R}
  (f : A -> B -> C -> D -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D}
  : FromSexpList R :=
  con4 f _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con5
  {A B C D E R}
  (f : A -> B -> C -> D -> E -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexpList R :=
  fun pa pb pc pd pe =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
        Deser.ret (f a b c d e)).

Definition con5_
  {A B C D E R}
  (f : A -> B -> C -> D -> E -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  : FromSexpList R :=
  con5 f  _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con6
  {A B C D E F R}
  (f : A -> B -> C -> D -> E -> F -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexpList R :=
  fun pa pb pc pd pe pf =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' =>
        Deser.ret (f a b c d e f')).

Definition con6_
  {A B C D E F R}
  (f : A -> B -> C -> D -> E -> F -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F}
  : FromSexpList R :=
  con6 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con7
  {A B C D E F G R}
  (f : A -> B -> C -> D -> E -> F -> G -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexpList R :=
  fun pa pb pc pd pe pf pg =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g =>
        Deser.ret (f a b c d e f' g)).

Definition con7_
  {A B C D E F G R}
  (f : A -> B -> C -> D -> E -> F -> G -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G}
  : FromSexpList R :=
  con7 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con8
  {A B C D E F G H R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h =>
        Deser.ret (f a b c d e f' g h)).

Definition con8_
  {A B C D E F G H R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H}
  : FromSexpList R :=
  con8 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp.

Definition con9
  {A B C D E F G H I R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i =>
        Deser.ret (f a b c d e f' g h i)).

Definition con9_
  {A B C D E F G H I R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I}
  : FromSexpList R :=
  con9 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp.

Definition con10
  {A B C D E F G H I J R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
        Deser.ret (f a b c d e f' g h i j)).

Definition con10_
  {A B C D E F G H I J R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  : FromSexpList R :=
  con10 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp.

Definition con11
  {A B C D E F G H I J K R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k =>
        Deser.ret (f a b c d e f' g h i j k)).

Definition con11_
  {A B C D E F G H I J K R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K}
  : FromSexpList R :=
  con11 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con12
  {A B C D E F G H I J K L R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexp L
      -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk pl =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k => pl >>= fun l =>
        Deser.ret (f a b c d e f' g h i j k l)).

Definition con12_
  {A B C D E F G H I J K L R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K} `{Deserialize L}
  : FromSexpList R :=
  con12 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con13
  {A B C D E F G H I J K L M R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexp L
      -> FromSexp M -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk pl pm =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k => pl >>= fun l => pm >>= fun m =>
        Deser.ret (f a b c d e f' g h i j k l m)).

Definition con13_
  {A B C D E F G H I J K L M R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K} `{Deserialize L} `{Deserialize M}
  : FromSexpList R :=
  con13 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con14
  {A B C D E F G H I J K L M N R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexp L
      -> FromSexp M -> FromSexp N -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk pl pm pn =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k => pl >>= fun l => pm >>= fun m => pn >>= fun n =>
        Deser.ret (f a b c d e f' g h i j k l m n)).

Definition con14_
  {A B C D E F G H I J K L M N R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K} `{Deserialize L} `{Deserialize M} `{Deserialize N}
  : FromSexpList R :=
  con14 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con15
  {A B C D E F G H I J K L M N O R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexp L
      -> FromSexp M -> FromSexp N -> FromSexp O -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk pl pm pn po =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k => pl >>= fun l => pm >>= fun m => pn >>= fun n => po >>= fun o =>
        Deser.ret (f a b c d e f' g h i j k l m n o)).

Definition con15_
  {A B C D E F G H I J K L M N O R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K} `{Deserialize L} `{Deserialize M} `{Deserialize N} `{Deserialize O}
  : FromSexpList R :=
  con15 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con16
  {A B C D E F G H I J K L M N O P R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexp L
      -> FromSexp M -> FromSexp N -> FromSexp O -> FromSexp P -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk pl pm pn po pp =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k => pl >>= fun l => pm >>= fun m => pn >>= fun n => po >>= fun o =>
      pp >>= fun p =>
        Deser.ret (f a b c d e f' g h i j k l m n o p)).

Definition con16_
  {A B C D E F G H I J K L M N O P R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K} `{Deserialize L} `{Deserialize M} `{Deserialize N} `{Deserialize O}
  `{Deserialize P}
  : FromSexpList R :=
  con16 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp.

Definition con17
  {A B C D E F G H I J K L M N O P Q R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> Q -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexp L
      -> FromSexp M -> FromSexp N -> FromSexp O -> FromSexp P -> FromSexp Q -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk pl pm pn po pp pq =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k => pl >>= fun l => pm >>= fun m => pn >>= fun n => po >>= fun o =>
      pp >>= fun p => pq >>= fun q =>
        Deser.ret (f a b c d e f' g h i j k l m n o p q)).

Definition con17_
  {A B C D E F G H I J K L M N O P Q R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> Q -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K} `{Deserialize L} `{Deserialize M} `{Deserialize N} `{Deserialize O}
  `{Deserialize P} `{Deserialize Q}
  : FromSexpList R :=
  con17 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp.

Definition con18
  {A B C D E F G H I J K L M N O P Q S R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> Q -> S -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
    -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexp L
    -> FromSexp M -> FromSexp N -> FromSexp O -> FromSexp P -> FromSexp Q -> FromSexp S
    -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk pl pm pn po pp pq ps =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k => pl >>= fun l => pm >>= fun m => pn >>= fun n => po >>= fun o =>
      pp >>= fun p => pq >>= fun q => ps >>= fun s =>
        Deser.ret (f a b c d e f' g h i j k l m n o p q s)).

Definition con18_
  {A B C D E F G H I J K L M N O P Q S R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> Q -> S -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K} `{Deserialize L} `{Deserialize M} `{Deserialize N} `{Deserialize O}
  `{Deserialize P} `{Deserialize Q} `{Deserialize S}
  : FromSexpList R :=
  con18 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp.

Definition con19
  {A B C D E F G H I J K L M N O P Q S T R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> Q -> S -> T -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexp L
      -> FromSexp M -> FromSexp N -> FromSexp O -> FromSexp P -> FromSexp Q -> FromSexp S
      -> FromSexp T -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk pl pm pn po pp pq ps pt =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k => pl >>= fun l => pm >>= fun m => pn >>= fun n => po >>= fun o =>
      pp >>= fun p => pq >>= fun q => ps >>= fun s => pt >>= fun t =>
        Deser.ret (f a b c d e f' g h i j k l m n o p q s t)).

Definition con19_
  {A B C D E F G H I J K L M N O P Q S T R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> Q -> S -> T -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K} `{Deserialize L} `{Deserialize M} `{Deserialize N} `{Deserialize O}
  `{Deserialize P} `{Deserialize Q} `{Deserialize S} `{Deserialize T}
  : FromSexpList R :=
  con19 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con20
  {A B C D E F G H I J K L M N O P Q S T U R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> Q -> S -> T -> U -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F
      -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexp K -> FromSexp L
      -> FromSexp M -> FromSexp N -> FromSexp O -> FromSexp P -> FromSexp Q -> FromSexp S
      -> FromSexp T -> FromSexp U -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj pk pl pm pn po pp pq ps pt pu =>
    Deser.fields (
      pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
      pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
      pk >>= fun k => pl >>= fun l => pm >>= fun m => pn >>= fun n => po >>= fun o =>
      pp >>= fun p => pq >>= fun q => ps >>= fun s => pt >>= fun t => pu >>= fun u =>
        Deser.ret (f a b c d e f' g h i j k l m n o p q s t u)).

Definition con20_
  {A B C D E F G H I J K L M N O P Q S T U R}
  (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> K -> L -> M -> N -> O -> P -> Q -> S -> T -> U -> R)
  `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  `{Deserialize K} `{Deserialize L} `{Deserialize M} `{Deserialize N} `{Deserialize O}
  `{Deserialize P} `{Deserialize Q} `{Deserialize S} `{Deserialize T} `{Deserialize U}
  : FromSexpList R :=
  con20 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp
    _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.



Local Open Scope bs_scope.

(* Pretty print deserialization error messages *)

Definition string_of_loc (l : loc) : string := CeresString.comma_sep (map CeresString.string_of_nat l).

Fixpoint string_of_message (print_sexp : bool) (m : message) : string :=
  match m with
  | MsgStr s => s
  | MsgSexp e => if print_sexp then string_of_sexp e else ""
  | MsgApp m1 m2 =>
    let m1_str := string_of_message print_sexp m1 in
    let m2_str := string_of_message print_sexp m2 in
    m1_str ++ m2_str
  end.

Definition string_of_error (print_loc print_sexp : bool) (e : error) : string :=
  match e with
  (* Errors from parsing [string -> sexp] *)
  | ParseError e => CeresParserUtils.pretty_error e
  (* Errors from deserializing [sexp -> A] *)
  | DeserError l m =>
    let msg_str := string_of_message print_sexp m in
    if print_loc
    then msg_str ++ " at location " ++ string_of_loc l
    else msg_str
  end.



(* Bytestring utility functions *)

Lemma eqb_byte_refl : forall c,
  CeresString.eqb_byte c c = true.
Proof.
  intros c.
  destruct c; reflexivity.
Qed.

Lemma neqb_byte_neq : forall a b,
  a <> b -> CeresString.eqb_byte a b = false.
Proof.
  intros.
  apply CeresString.neqb_neq_byte.
  assumption.
Qed.

Lemma bytestring_of_to : forall s,
  bytestring.String.of_string (bytestring.String.to_string s) = s.
Proof.
  induction s.
  - reflexivity.
  - cbn.
    rewrite IHs.
    rewrite Ascii.byte_of_ascii_of_byte.
    reflexivity.
Qed.

Lemma bytestring_to_of : forall s,
  bytestring.String.to_string (bytestring.String.of_string s) = s.
Proof.
  induction s.
  - reflexivity.
  - cbn.
    rewrite IHs.
    rewrite Ascii.ascii_of_byte_of_ascii.
    reflexivity.
Qed.



(* Soundness and Completeness proofs for common types *)
Instance Sound_unit : @SoundClass unit Serialize_unit Deserialize_unit.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  unfold to_sexp, Serialize_unit.
  unfold _from_sexp, Deserialize_unit in He.
  destruct e; try discriminate.
  destruct a0; try discriminate.
  destruct s; try discriminate.
  destruct b; try discriminate.
  destruct s; try discriminate.
  destruct b; try discriminate.
  destruct s; try discriminate.
  reflexivity.
Qed.

Instance Complete_unit : @CompleteClass unit Serialize_unit Deserialize_unit.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn.
  destruct o.
  reflexivity.
Qed.



Local Open Scope list_scope.

(* Completeness helper lemmas *)

Lemma complete_class_list_all {A : Type}
                             `{Serialize A}
                             `{Deserialize A} :
  forall (a xs : list A) (n : nat) (l : loc),
    All_Forall.All
      (fun t : A =>
       forall l : loc, _from_sexp l (to_sexp t) = inr t) a ->
    _sexp_to_list _from_sexp xs n l (map to_sexp a) = inr (rev xs ++ a).
Proof.
  induction a; intros; cbn.
  - rewrite rev_alt, app_nil_r.
    reflexivity.
  - inversion X; subst.
    rewrite H2.
    rewrite app_cons_assoc.
    apply IHa.
    assumption.
Qed.

Lemma complete_class_all_prod {A B : Type}
                             `{Serialize A}
                             `{Deserialize A}
                             `{Serialize B}
                             `{Deserialize B} :
  forall xs,
    CompleteClass A ->
    All_Forall.All
      (fun x : A * B =>
        forall l : loc, _from_sexp l (to_sexp (snd x)) = inr (snd x)) xs ->
      All_Forall.All
        (fun x : A * B =>
        forall l : loc, _from_sexp l (to_sexp x) = inr x) xs.
Proof.
  induction xs; intros.
  - apply All_Forall.All_nil.
  - apply All_Forall.All_cons.
    + intros.
      inversion X; subst.
      cbn.
      rewrite H5.
      rewrite complete_class.
      destruct a; cbn.
      reflexivity.
    + inversion X; subst.
      apply IHxs; assumption.
Qed.



(* Strong soundness *)

Inductive SoundClassStrong (P : sexp -> Prop) : sexp -> Prop :=
| SoundAtom : forall a,
    P (Atom a) ->
    SoundClassStrong P (Atom a)
| SoundList : forall es,
    P (List es) ->
    Forall (SoundClassStrong P) es ->
    SoundClassStrong P (List es).

Lemma SoundClassStrong_implies_P {P : sexp -> Prop} :
  forall e,
    SoundClassStrong P e -> P e.
Proof.
  intros e Hss.
  inversion Hss; auto.
Qed.

Lemma SoundClassStrong_List_inv {P : sexp -> Prop} :
  forall es,
    SoundClassStrong P (List es) ->
      Forall (SoundClassStrong P) es.
Proof.
  intros es Hss.
  inversion Hss; auto.
Qed.

Lemma Forall_SoundClassStrong_Forall_P {P : sexp -> Prop} :
  forall es,
    Forall (SoundClassStrong P) es ->
      Forall P es.
Proof.
  intros es Hss.
  induction Hss as [| e es' Hss_e Hss_es' IH]; constructor.
  - apply SoundClassStrong_implies_P.
    assumption.
  - assumption.
Qed.



(* Soundness helper lemmas *)

Local Lemma sound_class_list_forall_aux {A : Type}
                                 `{Serialize A}
                                 `{Deserialize A}
                                  (es : list sexp) :
  forall xs n l a,
    Forall (fun e => forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) es ->
    _sexp_to_list _from_sexp xs n l es = inr a ->
    map to_sexp a = (map to_sexp (rev xs) ++ es).
Proof.
  induction es as [| e es IH].
  - (* nil *)
    intros xs n l ts Hall Hdes.
    cbn in Hdes.
    injection Hdes as <-.
    rewrite rev_alt.
    rewrite app_nil_r.
    reflexivity.
  - (* cons *)
    intros xs n l ts Hall Hdes.
    cbn in Hdes.
    destruct (_from_sexp _ e) as [? | t] eqn:Hdes_e; try discriminate.
    inversion Hall as [|e' es' He Hes' Heq1]; subst.
    apply IH in Hdes; auto.
    rewrite Hdes; cbn.
    rewrite map_app; cbn.
    erewrite He; eauto.
    rewrite <- app_assoc; cbn.
    reflexivity.
Qed.

Lemma sound_class_list_forall {A : Type}
                             `{Serialize A}
                             `{Deserialize A}
                              (es : list sexp) :
  forall l (xs : list A),
    Forall (fun e => forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  erewrite sound_class_list_forall_aux; eauto.
  cbn.
  reflexivity.
Qed.

Lemma sound_class_list_strong {A : Type}
     `{Serialize A}
     `{Deserialize A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es,
  Forall (SoundClassStrong P) es ->
  forall l xs,
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  erewrite sound_class_list_forall; eauto.
  apply Forall_SoundClassStrong_Forall_P in H1.
  eapply Forall_impl; [| exact H1].
  exact HP.
Qed.

Lemma sound_class_list_prod_strong {A B : Type}
     `{Serialize B} `{Deserialize B}
     `{SoundClass A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : B), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es l (xs : list (A * B)),
    Forall (SoundClassStrong P) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map (fun p => List [to_sexp (fst p); to_sexp (snd p)]) xs = es.
Proof.
  intros.
  eapply sound_class_list_forall; eauto.
  eapply Forall_impl; [| exact H4].
  intros e HPe l' t Hdes.
  destruct t as [a b].
  unfold _from_sexp, Deserialize_prod in Hdes.
  destruct e; try discriminate.
  destruct xs0; try discriminate.
  destruct xs0; try discriminate.
  destruct xs0; try discriminate.
  destruct (_from_sexp _ s) eqn:Hdesa in Hdes; try discriminate.
  destruct (_from_sexp _ s0) eqn:Hdesb in Hdes; try discriminate.
  injection Hdes as <- <-.
  apply sound_class in Hdesa as <-.
  inversion HPe as [|? HP_list Hss_inner]; subst.
  apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
  apply List.Forall_cons_iff in Hss_inner as [Hss_b _].
  apply SoundClassStrong_implies_P in Hss_b.
  eapply HP in Hss_b as <-; eauto.
  cbn. reflexivity.
Qed.

Lemma sound_class_list_sum_strong {A B : Type}
     `{Serialize B} `{Deserialize B}
     `{SoundClass A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : B), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es l (xs : list (A + B)),
    Forall (SoundClassStrong P) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  eapply sound_class_list_forall; eauto.
  eapply Forall_impl; [| exact H4].
  intros e HPe l' t Hdes.
  unfold _from_sexp, Deserialize_sum in Hdes.
  apply sound_match_con in Hdes.
  destruct Hdes as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
  - destruct Ee as [es' [<- Ea]].
    sound_field Ea.
    apply sound_class in Ea1 as <-.
    cbn. reflexivity.
  - destruct Ee as [es' [<- Ea]].
    sound_field Ea.
    inversion HPe as [|? HP_list Hss_inner]; subst.
    apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply List.Forall_cons_iff in Hss_inner as [Hss_e _].
    apply SoundClassStrong_implies_P in Hss_e.
    eapply HP in Hss_e as <-; eauto.
    cbn. reflexivity.
Qed.

Lemma sound_class_list_option_strong {A : Type}
     `{Serialize A} `{Deserialize A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es l (xs : list (option A)),
    Forall (SoundClassStrong P) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  eapply sound_class_list_forall; eauto.
  eapply Forall_impl; [| exact H1].
  intros e HPe l' t Hdes.
  unfold _from_sexp, Deserialize_option in Hdes.
  apply sound_match_con in Hdes.
  destruct Hdes as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
  - destruct Ee as [E1 E2]; subst; reflexivity.
  - destruct Ee as [es' [<- Ea]].
    sound_field Ea.
    inversion HPe as [|? HP_list Hss_inner]; subst.
    apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply List.Forall_cons_iff in Hss_inner as [Hss_e _].
    apply SoundClassStrong_implies_P in Hss_e.
    eapply HP in Hss_e as <-; eauto.
    cbn. reflexivity.
Qed.

Lemma sound_class_list_list_strong {A : Type}
     `{Serialize A} `{Deserialize A}
      (P : sexp -> Prop)
      (HP : forall e, P e -> forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) :
  forall es l (xs : list (list A)),
    Forall (SoundClassStrong P) es ->
    _sexp_to_list _from_sexp nil 0 l es = inr xs ->
    map to_sexp xs = es.
Proof.
  intros.
  eapply sound_class_list_forall; eauto.
  eapply Forall_impl; [| exact H1].
  intros e HPe l' t Hdes.
  unfold _from_sexp, Deserialize_list in Hdes.
  destruct e; try discriminate.
  unfold to_sexp, Serialize_list.
  erewrite sound_class_list_forall; eauto.
  apply SoundClassStrong_List_inv in HPe.
  eapply Forall_impl; [| exact HPe].
  intros e HPe' ? t' Hdes'.
  apply SoundClassStrong_implies_P in HPe'.
  eapply HP in HPe' as <-; eauto.
Qed.
