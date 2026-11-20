(** * Raw atoms produced by the configuration serializers are parseable *)

From Stdlib Require Import List Bool.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure Require Import EProgram.
From Malfunction Require Serialize.
From CeresBS Require Import Ceres.
From Peregrine Require Import Config ConfigUtils.
From Peregrine Require Import CeresParserComplete SerializeRawOk SerializeCommon SerializeConfig.

Local Open Scope bs_scope.

Ltac raw_ok_solve X :=
  first [ solve [raw_ok_inst X]
        | solve [let a := fresh "a" in intros a; unfold to_sexp at 1, X; raw_ok_tac] ].

#[global] Instance RawOk_rust_config : RawOk (rust_config).
Proof. raw_ok_solve Serialize_rust_config. Qed.

#[global] Instance RawOk_rust_config' : RawOk (rust_config').
Proof. raw_ok_solve Serialize_rust_config'. Qed.

#[global] Instance RawOk_elm_config : RawOk (elm_config).
Proof. raw_ok_solve Serialize_elm_config. Qed.

#[global] Instance RawOk_elm_config' : RawOk (elm_config').
Proof. raw_ok_solve Serialize_elm_config'. Qed.

#[global] Instance RawOk_certirocq_config : RawOk (certirocq_config).
Proof. raw_ok_solve Serialize_certirocq_config. Qed.

#[global] Instance RawOk_certirocq_config' : RawOk (certirocq_config').
Proof. raw_ok_solve Serialize_certirocq_config'. Qed.

#[global] Instance RawOk_program_type : RawOk (Serialize.program_type).
Proof. raw_ok_solve Serialize_program_type. Qed.

#[global] Instance RawOk_ocaml_config : RawOk (ocaml_config).
Proof. raw_ok_solve Serialize_ocaml_config. Qed.

#[global] Instance RawOk_ocaml_config' : RawOk (ocaml_config').
Proof. raw_ok_solve Serialize_ocaml_config'. Qed.

#[global] Instance RawOk_cakeml_config : RawOk (cakeml_config).
Proof. intros a; unfold to_sexp at 1, Serialize_cakeml_config. cbn -[to_sexp raw_ok]. apply raw_ok_to_sexp. Qed.

#[global] Instance RawOk_cakeml_config' : RawOk (cakeml_config').
Proof. raw_ok_solve Serialize_cakeml_config'. Qed.

#[global] Instance RawOk_lean_config : RawOk (lean_config).
Proof. raw_ok_solve Serialize_lean_config. Qed.

#[global] Instance RawOk_lean_config' : RawOk (lean_config').
Proof. raw_ok_solve Serialize_lean_config'. Qed.

#[global] Instance RawOk_fsharp_config : RawOk (fsharp_config).
Proof. raw_ok_solve Serialize_fsharp_config. Qed.

#[global] Instance RawOk_fsharp_config' : RawOk (fsharp_config').
Proof. raw_ok_solve Serialize_fsharp_config'. Qed.

#[global] Instance RawOk_eval_config : RawOk (eval_config).
Proof. raw_ok_solve Serialize_eval_config. Qed.

#[global] Instance RawOk_eval_config' : RawOk (eval_config').
Proof. raw_ok_solve Serialize_eval_config'. Qed.

#[global] Instance RawOk_ASTType : RawOk (ASTType).
Proof. raw_ok_solve Serialize_ASTType. Qed.

#[global] Instance RawOk_ASTType' : RawOk (ASTType').
Proof. raw_ok_solve Serialize_ASTType'. Qed.

#[global] Instance RawOk_ast_config : RawOk (ast_config).
Proof. raw_ok_solve Serialize_ast_config. Qed.

#[global] Instance RawOk_ast_config' : RawOk (ast_config').
Proof. raw_ok_solve Serialize_ast_config'. Qed.

#[global] Instance RawOk_koka_config : RawOk (koka_config).
Proof. raw_ok_solve Serialize_koka_config. Qed.

#[global] Instance RawOk_koka_config' : RawOk (koka_config').
Proof. raw_ok_solve Serialize_koka_config'. Qed.

#[global] Instance RawOk_backend_config : RawOk (backend_config).
Proof. raw_ok_solve Serialize_backend_config. Qed.

#[global] Instance RawOk_backend_config' : RawOk (backend_config').
Proof. raw_ok_solve Serialize_backend_config'. Qed.

#[global] Instance RawOk_remapped_inductive : RawOk (remapped_inductive).
Proof. raw_ok_solve Serialize_remapped_inductive. Qed.

#[global] Instance RawOk_remapped_constant : RawOk (remapped_constant).
Proof. raw_ok_solve Serialize_remapped_constant. Qed.

#[global] Instance RawOk_inductive_mapping : RawOk (EProgram.inductive_mapping).
Proof. intros [kn [s n]]; unfold to_sexp at 1, Serialize_inductive_mapping; raw_ok_tac. Qed.

#[global] Instance RawOk_extract_inductive : RawOk (extract_inductive).
Proof. raw_ok_solve Serialize_extract_inductive. Qed.

#[global] Instance RawOk_remap_inductive : RawOk (remap_inductive).
Proof. raw_ok_solve Serialize_remap_inductive. Qed.

#[global] Instance RawOk_custom_attribute : RawOk (custom_attribute).
Proof. raw_ok_solve Serialize_custom_attribute. Qed.

#[global] Instance RawOk_inlinings : RawOk (inlinings).
Proof. raw_ok_solve Serialize_inlinings. Qed.

#[global] Instance RawOk_constant_remappings : RawOk (constant_remappings).
Proof. raw_ok_solve Serialize_constant_remappings. Qed.

#[global] Instance RawOk_inductive_remappings : RawOk (inductive_remappings).
Proof. raw_ok_solve Serialize_inductive_remappings. Qed.

#[global] Instance RawOk_custom_attributes : RawOk (custom_attributes).
Proof. raw_ok_solve Serialize_custom_attributes. Qed.

#[global] Instance RawOk_erasure_phases : RawOk (erasure_phases).
Proof. raw_ok_solve Serialize_erasure_phases. Qed.

#[global] Instance RawOk_erasure_phases' : RawOk (erasure_phases').
Proof. raw_ok_solve Serialize_erasure_phases'. Qed.

#[global] Instance RawOk_config : RawOk (config).
Proof. raw_ok_solve Serialize_config. Qed.

#[global] Instance RawOk_config' : RawOk (config').
Proof. raw_ok_solve Serialize_config'. Qed.

#[global] Instance RawOk_attributes_config : RawOk (attributes_config).
Proof. raw_ok_solve Serialize_attributes_config. Qed.
