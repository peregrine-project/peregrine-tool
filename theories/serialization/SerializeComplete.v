From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeCommonComplete.
From Peregrine Require Import SerializeEAst.
From Peregrine Require Import SerializeEAstComplete.
From Peregrine Require Import SerializeExAst.
From Peregrine Require Import SerializeExAstComplete.
From Peregrine Require Import SerializePAst.
From Peregrine Require Import SerializePAstComplete.
From Peregrine Require Import SerializeConfig.
From Peregrine Require Import SerializeConfigComplete.
From Ceres Require Import CeresRoundtrip.



Instance Complete_PAst : CompleteClass PAst.PAst.
Proof. typeclasses eauto. Qed.

Instance Complete_config' : CompleteClass ConfigUtils.config'.
Proof. typeclasses eauto. Qed.

Instance Complete_backend_config : CompleteClass ConfigUtils.backend_config'.
Proof. typeclasses eauto. Qed.

Instance Complete_erasure_phases' : CompleteClass ConfigUtils.erasure_phases'.
Proof. typeclasses eauto. Qed.

Instance Complete_attributes_config : CompleteClass Config.attributes_config.
Proof. typeclasses eauto. Qed.
