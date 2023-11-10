From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Meta.

From Elo Require Import Definitions.


(* ------------------------------------------------------------------------- *)
(* misc. properties                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma nomut_block : forall t t' block,
  safe_spawns t ->
  t --[EF_Spawn block]--> t' ->
  no_mut block.
Proof.
  intros. induction_tstep; inv_ss; eauto.
Qed.

Lemma nomut_then_nuacc: forall m t ad,
  no_mut t ->
  unsafe_access ad m t ->
  False.
Proof.
  intros * Hnm Huacc. induction Hnm; inv_uacc; eauto.
Qed.

Theorem nuacc_spawn_block : forall m t t' block ad,
  safe_spawns t ->
  t --[EF_Spawn block]--> t' ->
  ~ unsafe_access ad m block.
Proof.
  eauto using nomut_block, nomut_then_nuacc.
Qed.

