From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import ValidAddresses.
From Elo Require Import AccessCore.
From Elo Require Import NotAccess.

(* ------------------------------------------------------------------------- *)
(* inheritance                                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma acc_subst_inheritance : forall m x Tx t t' ad,
  access ad m ([x := t'] t) ->
  access ad m <{call <{fn x Tx t}> t'}>.
Proof.
  intros. induction t; eauto using access; simpl in *;
  try (destruct string_eq_dec; eauto using access);
  inv_clear_acc; auto_specialize; do 2 inv_acc; eauto using access.
Qed.

Lemma acc_mem_add_inheritance : forall m t ad vT,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  access ad (m +++ vT) t ->
  access ad m t.
Proof.
  intros * ? Hvad Hacc.
  assert (Hnacc : ~ access (#m) m t). {
    intros F. eapply vad_then_vac in Hvad; trivial.
    specialize (Hvad (#m) F). lia.
  }
  clear Hvad. induction Hacc; inv_nacc Hnacc.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; try lia;
  simpl_array; eauto using access. simpl in *. inv_acc.
Qed.

Lemma acc_mem_set_inheritance : forall m t ad ad' v T,
  ~ access ad m v ->
  access ad m[ad' <- (v, T)] t ->
  access ad m t.
Proof.
  intros * Hnacc Hacc. remember (m[ad' <- (v, T)]) as m'.
  induction Hacc; inv Heqm'; eauto using access.
  match goal with |- access _ _ <{& ?ad :: _}> => rename ad into ad'' end.
  destruct (nat_eq_dec ad' ad''); subst; try (simpl_array; eauto using access);
  destruct (nat_eq_dec ad'' ad); subst; eauto using access.
  rewrite (get_set_eq memory_default) in IHHacc. 1: contradiction.
  eapply not_le. intros Hlen. simpl_array. 
  eapply Nat.lt_eq_cases in Hlen as [? | ?]; subst;
  simpl_array; simpl in *; inv_acc.
Qed.

(* alternative for mem_set ------------------------------------------------- *)

(* removed *)

(* tstep ------------------------------------------------------------------- *)

Lemma acc_tstep_none_inheritance  : forall m t t' ad,
  access ad m t' ->
  t --[EF_None]--> t' ->
  access ad m t.
Proof.
  intros. induction_step; try inv_acc;
  eauto using access, acc_subst_inheritance .
Qed.

Lemma acc_tstep_alloc_inheritance : forall m t t' ad v T,
  ad < #m ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  access ad (m +++ (v, T)) t' ->
  t --[EF_Alloc (#m) v T]--> t' ->
  access ad m t.
Proof.
  intros. induction_step; inversion_vad; inv_acc; eauto; try lia;
  try simpl_array; eauto using access, acc_mem_add_inheritance.
Qed.

Lemma acc_tstep_read_inheritance : forall m t t' ad ad',
  access ad m t' ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  access ad m t.
Proof.
  intros. induction_step; try inv_acc; eauto using access.
  destruct (nat_eq_dec ad' ad); subst; eauto using access.
Qed.

Lemma acc_tstep_write_inheritance : forall m t t' ad ad' v T,
  access ad m[ad' <- (v, T)] t' ->
  t --[EF_Write ad' v T]--> t' ->
  access ad m t.
Proof.
  intros. induction_step; inv_acc; eauto using access;
  destruct (acc_dec m v ad); eauto using access, acc_mem_set_inheritance;
  assert (forall t t', t --[EF_Write ad' v T]--> t' -> access ad m t)
    by (intros; induction_step; eauto using access);
  eauto using access.
Qed.

Lemma acc_tstep_spawn_inheritance : forall m t t' block ad,
  access ad m t' ->
  t --[EF_Spawn block]--> t' ->
  access ad m t.
Proof.
  intros. induction_step; inv_acc; eauto using access.
Qed.

Corollary acc_mstep_inheritance : forall m m' t t' ad e,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  ad < #m ->
  access ad m' t' ->
  m / t ==[e]==> m' / t' ->
  access ad m t.
Proof.
  intros. inversion_mstep;
  eauto using acc_tstep_none_inheritance,
    acc_tstep_alloc_inheritance,
    acc_tstep_read_inheritance,
    acc_tstep_write_inheritance.
Qed.

