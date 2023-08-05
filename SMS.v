From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import ValidAddresses.
From Elo Require Import References.
From Elo Require Import Access.
From Elo Require Import SafeSpawns.

Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access ad m ths[tid2] ->
  ~ unsafe_access ad m ths[tid1].

(* ------------------------------------------------------------------------- *)
(* helpers                                                                   *)
(* ------------------------------------------------------------------------- *)

Local Lemma cstep_length_tid : forall m m' ths ths' tid e,
  m / ths ~~[tid, e]~~> m' / ths' ->
  tid < #ths.
Proof.
  intros. inversion_clear_cstep; trivial.
Qed.

Local Lemma step_write_sms_helper : forall m t ad v ths tid tid' T,
  tid <> tid' ->
  forall_threads ths well_typed_term ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Write ad v T]--> t ->
  ~ access ad m ths[tid'].
Proof.
  assert (forall m t t' ad v T Te,
    empty |-- t is T ->
    t --[EF_Write ad v Te]--> t' ->
    unsafe_access ad m t
  ). {
    intros. generalize dependent T.
    induction_step; intros; inversion_type; eauto using unsafe_access.
    inversion_type. eauto using unsafe_access.
  }
  (* main proof *)
  intros * Hneq Htype Hsms ? Hacc.
  destruct (Htype tid). specialize (Hsms _ _ _ Hneq Hacc); eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Local Lemma sms_tstep_none_preservation : forall m t ths tid,
  safe_memory_sharing m ths ->
  ths[tid] --[EF_None]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros. intros ? ? ? ? ?.
  assert (tid < #ths) by eauto using step_length_tid.
  destruct (nat_eq_dec tid tid1), (nat_eq_dec tid tid2); subst;
  try lia; simpl_array;
  eauto using acc_tstep_none_inheritance, nuacc_tstep_none_preservation.
Qed.

Lemma vac_then_nuacc : forall m t,
  valid_accesses m t ->
  ~ unsafe_access (#m) m t.
Proof.
  intros * H F. eapply uacc_then_acc in F. eapply H in F; eauto. lia.
Qed.

Local Lemma trying_sms_tstep_alloc_preservation : forall m t v ths tid T,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (valid_accesses m) ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Alloc (#m) v T]--> t ->
  safe_memory_sharing (m +++ (v, T)) ths[tid <- t].
Proof.
  intros * ? ? Hvac Hsms ? tid1 tid2 ? ? ?.
  assert (tid < #ths) by eauto using step_length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  try lia; simpl_array.
  - eapply (nuacc_tstep_alloc_preservation _ ths[tid1]); eauto.
    + eapply Hvac; eauto.
      eapply acc_mem_add_inheritance; eauto.
    + eapply Hsms; eauto.
      eapply acc_mem_add_inheritance; eauto.
  - eapply nuacc_mem_add_preservation.
    + eapply vac_then_nuacc; eauto.
    + intros Huacc. eapply uacc_then_acc in Huacc as ?. contradict Huacc.
      eapply Hsms; eauto.
      eapply acc_tstep_alloc_inheritance; eauto.
      eapply Hvac; eauto.
  - eapply nuacc_mem_add_preservation.
    + eapply vac_then_nuacc; eauto.
    + eapply Hsms; eauto.
      eapply acc_mem_add_inheritance; eauto.
Qed.

Local Lemma sms_tstep_alloc_preservation : forall m t v ths tid T,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (valid_accesses m) ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Alloc (#m) v T]--> t ->
  safe_memory_sharing (m +++ (v, T)) ths[tid <- t].
Proof.
  intros * ? ? Hvac Hsms ? tid1 tid2 ? ? ?.
  specialize Hvac as Hvac'. unfold valid_accesses in Hvac'.
  assert (tid < #ths) by eauto using step_length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  try lia; simpl_array.
  - eapply (nuacc_tstep_alloc_preservation _ ths[tid1]);
    eauto using acc_mem_add_inheritance.
  - eapply nuacc_mem_add_preservation;
    eauto using vac_then_nuacc.
    intros Huacc. eapply uacc_then_acc in Huacc as ?. contradict Huacc.
    eauto using acc_tstep_alloc_inheritance.
  - eauto using nuacc_mem_add_preservation,
      vac_then_nuacc,
      acc_mem_add_inheritance.
Qed.

Local Lemma sms_tstep_read_preservation : forall m t ad ths tid,
  forall_memory m value ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Read ad m[ad].tm]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros * ? Htype ? ? ? tid1 tid2 ? ? ?. destruct (Htype tid1).
  assert (tid < #ths) by eauto using step_length_tid.
  destruct (nat_eq_dec tid tid1), (nat_eq_dec tid tid2); subst;
  try lia; simpl_array;
  eauto using acc_tstep_read_inheritance, nuacc_tstep_read_preservation.
Qed.

Local Lemma sms_tstep_write_preservation : forall m ths t tid ad v T,
  forall_threads ths well_typed_term ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Write ad v T]--> t ->
  safe_memory_sharing m[ad <- (v, T)] ths[tid <- t].
Proof.
  intros * ? Hsms ? tid1 tid2 ad' ? ? Huacc.
  eapply uacc_then_acc in Huacc as Hacc2. contradict Huacc.
  assert (tid < #ths) by eauto using step_length_tid.
  destruct (nat_eq_dec tid tid1), (nat_eq_dec tid tid2); subst;
  try lia; simpl_array.
  - assert (~ access ad m ths[tid2]) by eauto using step_write_sms_helper.
    eapply nuacc_tstep_write_preservation; eauto.
    eapply Hsms; eauto.
    eapply alt_acc_mem_set_inheritance; eauto.
  - assert (~ access ad m ths[tid1]) by eauto using step_write_sms_helper.
    intros F. eapply uacc_mem_set_inheritance in F as F'; eauto. contradict F'.
    eapply Hsms; eauto.
    eapply acc_tstep_write_inheritance; eauto.
  - assert (~ access ad m ths[tid1]) by eauto using step_write_sms_helper.
    assert (~ access ad m ths[tid2]) by eauto using step_write_sms_helper.
    intros F. eapply uacc_mem_set_inheritance in F as F'; eauto. contradict F'.
    eapply Hsms; eauto.
    eapply alt_acc_mem_set_inheritance; eauto.
Qed.

Local Corollary mstep_sms_preservation : forall m m' t e ths tid,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (valid_accesses m) ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[e]==> m' / t ->
  safe_memory_sharing m' ths[tid <- t].
Proof.
  intros. inversion_mstep;
  eauto using sms_tstep_none_preservation,
    sms_tstep_alloc_preservation,
    sms_tstep_read_preservation,
    sms_tstep_write_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* consistency                                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma uacc_then_mut : forall m ad v T,
  value v ->
  unsafe_access ad m v ->
  empty |-- v is <{{ Immut T }}> ->
  False.
Proof.
  intros * Hval Huacc ?. generalize dependent T.
  induction Huacc; intros; inversion Hval; subst; inversion_type; eauto.
Qed.

Local Lemma consistent_memtyp : forall m t ad T,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  m[ad].typ = <{{ &T }}> ->
  access ad m t ->
  unsafe_access ad m t.
Proof.
  intros * ? ? ? Heq Hacc. induction Hacc;
  inversion_ctr; eauto using unsafe_access;
  exfalso; eauto using uacc_then_mut.
  rewrite Heq in *. discriminate.
Qed.

Lemma memtyp_uacc : forall m t ad,
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  unsafe_access ad m t ->
  exists T, m[ad].typ = <{{ &T }}>.
Proof.
  intros * ? ? Huacc. induction Huacc; inversion_ctr; eauto.
Qed.

Lemma consistent_uacc : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  consistently_typed_references m t' ->
  unsafe_access ad m t ->
  access ad m t' ->
  unsafe_access ad m t'.
Proof.
  intros.
  assert (exists T, m[ad].typ = <{{ &T }}>) as [? ?] by eauto using memtyp_uacc.
  eauto using consistent_memtyp.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem safe_memory_sharing_preservation : forall m m' ths ths' tid e,
  forall_memory m value ->
  forall_threads ths well_typed_term ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths (consistently_typed_references m) ->
  forall_threads ths SafeSpawns ->
  (* --- *)
  safe_memory_sharing m ths ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  safe_memory_sharing m' ths'.
Proof.
  intros * ? ? [? ?] [? ?]. intros.
  assert (tid < #ths) by eauto using cstep_length_tid.
  assert (forall_threads ths (valid_accesses m))
    by eauto using forall_threads_vad_then_vac.
  inversion_clear_cstep; eauto using mstep_sms_preservation.
  assert (NoMut block) by eauto using nomut_block.
  intros tid1 tid2. intros.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  decompose sum (lt_eq_lt_dec tid1 (#ths)); subst; simpl_array;
  eauto using acc_tstep_spawn_inheritance, nuacc_tstep_spawn_preservation;
  eauto using nomut_then_nuacc;
  eauto using nuacc_unit;
  decompose sum (lt_eq_lt_dec tid2 (#ths)); subst; simpl_array;
  eauto using acc_tstep_spawn_inheritance, nuacc_tstep_spawn_preservation;
  unfold thread_default in *; try inv_acc; intros ?;
  eauto using consistent_uacc,
    ctr_spawn_block_preservation,
    ctr_tstep_spawn_preservation,
    nomut_then_nuacc.
Qed.

