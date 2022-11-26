From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Contains.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.
From Elo Require Import References.
From Elo Require Import AccessProp.
From Elo Require Import UnsafeAccess.
From Elo Require Import SafeSpawns.
From Elo Require Import SafeBlocks.

Local Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access m ths[tid1] ad ->
  access m ths[tid2] ad ->
  ~ UnsafeAccess m ths[tid1] ad.

(* ------------------------------------------------------------------------- *)
(* mstep preservation                                                        *)
(* ------------------------------------------------------------------------- *)

Local Lemma length_tid : forall t ths tid eff,
  ths[tid] --[eff]--> t ->
  tid < length ths.
Proof.
  intros * Hstep.
  decompose sum (lt_eq_lt_dec tid (length ths)); subst; trivial;
  simpl_array; try lia; inversion_step.
Qed.

Local Lemma step_write_requires_uacc : forall m t t' ad v T,
  empty |-- t is T ->
  t --[EF_Write ad v]--> t' ->
  UnsafeAccess m t ad.
Proof.
  intros. generalize dependent T.
  induction_step; intros * ?; inversion_type; eauto using UnsafeAccess.
  inversion_type. eauto using UnsafeAccess.
Qed.

Local Lemma step_write_sms_helper : forall m t ad v ths tid tid',
  tid <> tid' ->
  forall_threads ths well_typed_thread ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Write ad v]--> t ->
  ~ access m ths[tid'] ad.
Proof.
  intros * Hneq Htype Hsms ? F.
  assert (Hacc : access m ths[tid] ad) by eauto using step_write_requires_acc.
  destruct (Htype tid). specialize (Hsms _ _ _ Hneq Hacc F).
  eauto using step_write_requires_uacc.
Qed.

Local Lemma step_none_sms_preservation : forall m t ths tid,
  safe_memory_sharing m ths ->
  ths[tid] --[EF_None]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros * ? ? tid1 tid2 ? ? ? ?.
  assert (tid < length ths) by eauto using length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  do 3 simpl_array;
  eauto using step_none_preserves_nuacc, step_none_inherits_access.
Qed.

Local Lemma step_alloc_sms_preservation : forall m t v ths tid,
  forall_threads ths (valid_accesses m) ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Alloc (length m) v]--> t ->
  safe_memory_sharing (m +++ v) ths[tid <- t].
Proof.
  intros * Hva ? ? tid1 tid2 ad Hneq Hacc1 Hacc2.
  assert (tid < length ths) by eauto using length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  do 3 simpl_array;
  assert (ad <> length m)
    by eauto 6 using mem_add_acc, mem_add_uacc, uacc_then_acc,
      va_length, va_nacc_length, Nat.lt_neq;
  eauto 6 using step_alloc_inherits_acc, step_alloc_preserves_nuacc,
    mem_add_acc, va_nacc_length;
  intros Huacc; eapply mem_add_uacc in Huacc; eauto using va_nacc_length;
  specialize Huacc as ?; contradict Huacc;
  eauto using step_alloc_inherits_acc, mem_add_acc,
    uacc_then_acc, va_nacc_length.
Qed.

Local Lemma step_read_sms_preservation : forall m t ad ths tid,
  forall_memory m value ->
  forall_threads ths well_typed_thread ->
  forall_threads ths (well_typed_references m) ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Read ad m[ad]]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros * ? Htype ? ? ? tid1 tid2 ? ? ? ?.
  destruct (Htype tid1).
  assert (tid < length ths) by eauto using length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  do 3 simpl_array;
  eauto using step_read_preserves_nuacc, step_read_inherits_acc.
Qed.

Local Lemma step_write_sms_preservation : forall m ths t tid ad v,
  forall_threads ths well_typed_thread ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Write ad v]--> t ->
  safe_memory_sharing m[ad <- v] ths[tid <- t].
Proof.
  intros * ? ? ? tid1 tid2 ad' ? ? ?.
  assert (tid < length ths) by eauto using length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  do 3 simpl_array;
  assert (~ UnsafeAccess m ths[tid1] ad');
  assert (~ UnsafeAccess m ths[tid2] ad');
  eauto 8 using mem_set_acc, mem_set_uacc, step_write_sms_helper,
    step_write_preserves_nuacc, step_write_inherits_acc.
Qed.

Local Corollary mstep_sms_preservation : forall m m' t eff ths tid,
  forall_memory m value ->
  forall_threads ths (valid_accesses m) ->
  forall_threads ths well_typed_thread ->
  forall_threads ths (well_typed_references m) ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[eff]==> m' / t ->
  safe_memory_sharing m' ths[tid <- t].
Proof.
  intros. inversion_mstep;
  eauto using step_none_sms_preservation,
    step_alloc_sms_preservation,
    step_read_sms_preservation,
    step_write_sms_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* sms preservation                                                          *)
(* ------------------------------------------------------------------------- *)

Theorem safe_memory_sharing_preservation : forall m m' ths ths' tid eff,
  forall_memory m value ->
  forall_threads ths (valid_accesses m) ->
  forall_threads ths well_typed_thread ->
  forall_threads ths (well_typed_references m) ->
  forall_threads ths SafeSpawns ->
  forall_threads ths (SafeBlocks m) ->
  safe_memory_sharing m ths ->
  tid < length ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  safe_memory_sharing m' ths'.
Proof.
  intros * ? ? ? ? ? Hsb. intros.
  inversion_cstep; eauto using mstep_sms_preservation.
  assert (NoMut block) by eauto using nomut_thread.
  intros tid1 tid2 ad Hneq Hacc1 Hacc2.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia.
  - destruct (lt_eq_lt_dec tid1 (length ths)) as [[Hlen1 | ?] | ?]; subst.
    + rewrite <- (set_preserves_length _ tid1 t') in Hlen1. do 4 simpl_array.
      assert (access m' ths[tid1] ad) by eauto using step_spawn_inherits_acc.
      destruct (lt_eq_lt_dec tid2 (length ths)) as [[Hlen2 | ?] | Hlen2]; subst.
      * rewrite <- (set_preserves_length _ tid1 t') in Hlen2. do 2 simpl_array.
        eauto using step_spawn_preserves_nuacc.
      * rewrite <- (set_preserves_length _ tid1 t') in Hacc2. simpl_array.
        specialize (Hsb tid1).
        eauto using step_spawn_preserves_nuacc, step_spawn_contains_block.
      * rewrite <- (set_preserves_length _ tid1 t') in Hlen2. simpl_array.
        inversion_access.
    + do 6 simpl_array. inversion_step.
    + do 8 simpl_array. inversion_step.
Abort.

