From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeCommonSound.
From Peregrine Require Import SerializeEAst.
From Peregrine Require Import SerializeEAstSound.
From Peregrine Require Import SerializeExAst.
From Peregrine Require Import SerializeExAstSound.
From Peregrine Require Import SerializePAst.
From Peregrine Require Import SerializePAstSound.
From Peregrine Require Import SerializeConfig.
From Peregrine Require Import SerializeConfigSound.
From Ceres Require Import CeresRoundtrip.



Instance Sound_PAst : SoundClass PAst.PAst.
Proof. typeclasses eauto. Qed.

Instance Sound_config' : SoundClass ConfigUtils.config'.
Proof. typeclasses eauto. Qed.

Instance Sound_backend_config : SoundClass ConfigUtils.backend_config'.
Proof. typeclasses eauto. Qed.

Instance Sound_erasure_phases' : SoundClass ConfigUtils.erasure_phases'.
Proof. typeclasses eauto. Qed.

Instance Sound_attributes_config : SoundClass Config.attributes_config.
Proof. typeclasses eauto. Qed.
