From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.
From Elo Require Import References.
From Elo Require Import SafeAccess.
From Elo Require Import Soundness.
From Elo Require Import Compat.
From Elo Require Import AccessProp.
From Elo Require Import Safe.

Local Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access m ths[tid1] ad ->
  access m ths[tid2] ad ->
  SafeAccess m ths[tid1] ad.

(* ------------------------------------------------------------------------- *)
(* safe-memory-sharing preservation                                          *)
(* ------------------------------------------------------------------------- *)

Local Lemma length_tid : forall m m' t' ths tid eff,
  m / ths[tid] ==[eff]==> m' / t' ->
  tid < length ths.
Proof.
  intros * Hmstep.
  decompose sum (lt_eq_lt_dec tid (length ths)); subst; trivial;
  rewrite (get_default TM_Unit) in Hmstep; try lia;
  inversion_mstep; inversion_step.
Qed.

Local Lemma mstep_none_sms_preservation : forall m m' ths t' tid,
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  forall_threads ths (well_typed_references m) ->
  well_typed_memory m ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[EF_None]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * Htype ? ? Hsms Hmstep tid1 tid2 ad Hneq ? ?.
  destruct (Htype tid1).
  specialize (Hsms _ _ ad Hneq) as ?.
  specialize (Hsms _ _ ad (not_eq_sym Hneq)) as ?.
  assert (tid < length ths) by eauto using length_tid.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  try lia; do 3 simpl_array;
  eauto using mstep_none_inherits_access.
  assert (access m' ths[tid1] ad) by eauto using mstep_none_inherits_access.
  eauto using mstep_none_preserves_sacc.
Qed.

Local Lemma mstep_read_sms_preservation : forall m m' ths t' tid ad v,
  forall_memory m value ->
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  forall_threads ths (well_typed_references m) ->
  well_typed_memory m ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[EF_Read ad v]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * ? Htype ? ? Hsms Hmstep tid1 tid2 ad Hneq ? ?.
  destruct (Htype tid1).
  specialize (Hsms _ _ ad Hneq) as ?.
  specialize (Hsms _ _ ad (not_eq_sym Hneq)) as ?.
  assert (tid < length ths) by eauto using length_tid.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  try lia; do 3 simpl_array;
  eauto using mstep_read_inherits_access.
  assert (access m' ths[tid1] ad) by eauto using mstep_read_inherits_access.
  eauto using mstep_read_preserves_sacc.
Qed.

Local Lemma mstep_alloc_sms_preservation : forall m m' ths t' tid ad v,
  well_typed_memory m ->
  forall_threads ths (valid_accesses m) ->
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[EF_Alloc ad v]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * ? ? Htype Hsms Hmstep tid1 tid2 ad Hneq Hacc1 Hacc2.
  specialize (Hsms _ _ ad Hneq) as ?.
  specialize (Hsms _ _ ad (not_eq_sym Hneq)) as ?.
  assert (tid < length ths) by eauto using length_tid.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  do 3 simpl_array;
  destruct (Htype tid1); destruct (Nat.eq_dec ad (length m)); subst;
  try solve
    [ contradict Hacc1; eauto using va_nacc_length, mem_add_nacc_length
    | contradict Hacc2; eauto using va_nacc_length, mem_add_nacc_lt
    ];
  assert (access m ths[tid1] ad);
  assert (access m ths[tid2] ad);
  eauto using va_nacc_length, mem_add_inherits_access, mstep_alloc_inherits_acc;
  eauto using mstep_alloc_preserves_sacc;
  eauto using va_nacc_length, mem_add_preserves_sacc.
Qed.

Local Ltac sms_infer Htype tid1 :=
  match goal with
  | _ : safe_memory_sharing ?m ?ths
  , _ : access ?m[?ad <- ?v] ?t' ?ad'
  , _ : access ?m[?ad <- ?v] ?t2 ?ad'
  , _ : ?t1 --[EF_Write ?ad _]--> ?t'
  |- _ =>
    destruct (Htype tid1) as [T1 Htype1];
    assert (Hnsacc1 : ~ SafeAccess m t1 ad) by eauto using write_then_nsacc;
    assert (Hacc1 : access m t1 ad) by eauto using mstep_write_requires_acc;
    destruct (access_dec m t2 ad) as [? | Hnacc2];
    try solve [exfalso; eauto];
    assert (Hacc1' : access m t1 ad') by eauto using mstep_write_inherits_acc;
    assert (Hacc2' : access m t2 ad') by eauto using mem_set_inherits_acc2;
    do 4 auto_specialize
  end.

Local Lemma mstep_write_sms_preservation : forall m m' ths t' tid ad v,
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[EF_Write ad v]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * Htype Hsms Hmstep tid1 tid2 ad' Hneq Hacc1W Hacc2W.
  specialize (Hsms _ _ ad' Hneq) as Hsms1.
  specialize (Hsms _ _ ad' (not_eq_sym Hneq)) as Hsms2.
  assert (Hlen : tid < length ths) by eauto using length_tid.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  do 3 simpl_array.
  - sms_infer Htype tid1.
Qed.

Local Lemma mstep_sms_preservation : forall m m' ths t' tid eff,
  safe_memory_sharing m ths ->
  m / ths[tid] ==[eff]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * ? ? ? Hmstep. inversion Hmstep; subst;
  eauto using none_disjoint_memory_preservation,
              alloc_disjoint_memory_preservation,
              read_disjoint_memory_preservation,
              write_disjoint_memory_preservation.
Qed.

Theorem safe_memory_sharing_preservation : forall m m' ths ths' tid eff,
  forall_threads SafeSpawns ths ->
  forall_threads (valid_accesses m) ths ->
  safe_memory_sharing m ths ->
  tid < length ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  safe_memory_sharing m' ths'.
Proof.
  intros. inversion_cstep;
  eauto using mstep_disjoint_memory_preservation.
  intros tid1 tid2 ad Hacc Hneq.
  decompose sum (lt_eq_lt_dec (length ths) tid2); subst.
  - rewrite (get_add_gt TM_Unit);
    try solve [rewrite set_preserves_length; trivial].
    intros ?. inversion_access.
  - erewrite <- set_preserves_length.
    rewrite (get_add_eq TM_Unit).
    eauto using safe_for_block. (* safe_then_not_access *)
    admit.
  - rewrite (get_add_lt TM_Unit);
    try solve [rewrite set_preserves_length; trivial].
    decompose sum (lt_eq_lt_dec (length ths) tid1); subst.
    + rewrite (get_add_gt TM_Unit) in Hacc;
      try solve [rewrite set_preserves_length; trivial].
      inversion_access.
    + erewrite <- set_preserves_length in Hacc.
      rewrite (get_add_eq TM_Unit) in Hacc.
      (*
      assert (~ access m' block ad) by 
        eauto using safe_for_block, safe_then_not_access.
      *)
      eauto.
      admit.
    + rewrite (get_add_lt TM_Unit) in Hacc;
      try solve [rewrite set_preserves_length; trivial].
      destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto;
      do 2 rewrite_term_array;
      eauto using step_spawn_inherits_access, step_spawn_preserves_not_access.
Abort.

