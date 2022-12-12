From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Contains.
From Elo Require Import ValidAddresses.
From Elo Require Import Access.
From Elo Require Import References.
From Elo Require Import UnsafeAccess.
From Elo Require Import SafeSpawns.

Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access m ths[tid2] ad ->
  ~ UnsafeAccess m ths[tid1] ad.

(* ------------------------------------------------------------------------- *)
(* helpers                                                                   *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_length_tid : forall t ths tid eff,
  ths[tid] --[eff]--> t ->
  tid < #ths.
Proof.
  intros * Hstep.
  decompose sum (lt_eq_lt_dec tid (#ths)); subst; trivial;
  simpl_array; try lia; inversion_step.
Qed.

Local Lemma cstep_length_tid : forall m m' ths ths' tid eff,
  m / ths ~~[tid, eff]~~> m' / ths' ->
  tid < #ths.
Proof.
  intros. inversion_clear_cstep; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* mstep preservation                                                        *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_write_sms_helper : forall m t ad v ths tid tid' V,
  tid <> tid' ->
  forall_threads ths well_typed ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Write ad v V]--> t ->
  ~ access m ths[tid'] ad.
Proof.
  intros * Hneq Htype Hsms ? F.
  destruct (Htype tid). specialize (Hsms _ _ _ Hneq F).
  eauto using step_write_requires_uacc.
Qed.

Local Lemma step_none_sms_preservation : forall m t ths tid,
  safe_memory_sharing m ths ->
  ths[tid] --[EF_None]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros * ? ? tid1 tid2 ? ? ?.
  assert (tid < #ths) by eauto using step_length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  simpl_array;
  eauto using step_none_nuacc_preservation, step_none_inherits_access.
Qed.

Local Lemma step_alloc_sms_preservation : forall m t v ths tid V,
  forall_threads ths (valid_accesses m) ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Alloc (#m) v V]--> t ->
  safe_memory_sharing (m +++ (v, V)) ths[tid <- t].
Proof.
  intros * Hva ? ? tid1 tid2 ad Hneq Hacc1 Huacc.
  eapply uacc_then_acc in Huacc as Hacc2. contradict Huacc.
  assert (tid < #ths) by eauto using step_length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  simpl_array;
  assert (ad <> #m)
    by eauto 6 using mem_add_acc, mem_add_uacc, uacc_then_acc,
      vac_length, vac_nacc_length, Nat.lt_neq;
  eauto 6 using step_alloc_inherits_acc, step_alloc_nuacc_preservation,
    mem_add_acc, vac_nacc_length;
  intros Huacc; eapply mem_add_uacc in Huacc; eauto using vac_nacc_length;
  specialize Huacc as Huacc'; contradict Huacc';
  eauto using step_alloc_inherits_acc, mem_add_acc,
    uacc_then_acc, vac_nacc_length.
Qed.

Local Lemma step_read_sms_preservation : forall m t ad ths tid,
  forall_memory m value ->
  forall_threads ths well_typed ->
  forall_threads ths (well_typed_references m) ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Read ad m[ad].tm]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros * ? Htype ? ? ? tid1 tid2 ? ? ?.
  destruct (Htype tid1).
  assert (tid < #ths) by eauto using step_length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  simpl_array; eauto using step_read_nuacc_preservation, step_read_inherits_acc.
Qed.

Local Lemma step_write_sms_preservation : forall m ths t tid ad v V,
  forall_threads ths well_typed ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Write ad v V]--> t ->
  safe_memory_sharing m[ad <- (v, V)] ths[tid <- t].
Proof.
  intros * ? ? ? tid1 tid2 ad' ? ? Huacc.
  eapply uacc_then_acc in Huacc as Hacc2. contradict Huacc.
  assert (tid < #ths) by eauto using step_length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  simpl_array;
  assert (~ UnsafeAccess m ths[tid1] ad');
  assert (~ UnsafeAccess m ths[tid2] ad');
  eauto 8 using mem_set_acc, mem_set_uacc, step_write_sms_helper,
    step_write_nuacc_preservation, step_write_inherits_acc.
Qed.

Local Corollary mstep_sms_preservation : forall m m' t eff ths tid,
  forall_memory m value ->
  forall_threads ths (valid_accesses m) ->
  forall_threads ths well_typed ->
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
(* consistency                                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma uacc_then_mut : forall m ad v T,
  value v ->
  UnsafeAccess m v ad ->
  empty |-- v is <{{ Immut T }}> ->
  False.
Proof.
  intros * Hval Huacc ?. generalize dependent T.
  induction Huacc; intros; inversion Hval; subst; inversion_type; eauto.
Qed.

Local Lemma consistent_memtyp : forall m t ad T,
  forall_memory m value ->
  forall_memory m (well_typed_references m) ->
  well_typed_references m t ->
  m[ad].typ = <{{ &T }}> ->
  access m t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * ? ? ? Heq Hacc. induction Hacc;
  inversion_wtr; eauto using UnsafeAccess;
  exfalso; eauto using uacc_then_mut.
  rewrite Heq in *. discriminate.
Qed.

Local Lemma wtr_uacc_memtyp : forall m t ad,
  forall_memory m (well_typed_references m) ->
  well_typed_references m t ->
  UnsafeAccess m t ad ->
  exists T, m[ad].typ = <{{ &T }}>.
Proof.
  intros * ? ? Huacc. induction Huacc; inversion_wtr; eauto.
Qed.

Lemma consistent_uacc : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (well_typed_references m) ->
  well_typed_references m t ->
  well_typed_references m t' ->
  UnsafeAccess m t ad ->
  access m t' ad ->
  UnsafeAccess m t' ad.
Proof.
  intros.
  assert (exists T, m[ad].typ = <{{ &T }}>) as [? ?]
    by eauto using wtr_uacc_memtyp.
  eauto using consistent_memtyp.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem safe_memory_sharing_preservation : forall m m' ths ths' tid eff,
  forall_memory m value ->
  forall_threads ths well_typed ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths (well_typed_references m) ->
  forall_threads ths SafeSpawns ->
  (* --- *)
  safe_memory_sharing m ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
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
  eauto using step_spawn_inherits_acc, step_spawn_nuacc_preservation;
  eauto using nomut_then_nuacc;
  eauto using nuacc_unit;
  decompose sum (lt_eq_lt_dec tid2 (#ths)); subst; simpl_array;
  eauto using step_spawn_inherits_acc, step_spawn_nuacc_preservation;
  unfold thread_default in *; try inversion_acc; intros ?;
  eauto using consistent_uacc,
    step_spawn_wtr_block, step_spawn_wtr_preservation,
    nomut_then_nuacc.
Qed.

From Elo Require Import Soundness.

Theorem safe_memory_sharing_multistep_preservation :
  forall m m' ths ths' tc,
    forall_memory m value ->
    forall_program m ths well_typed ->
    forall_program m ths (valid_addresses m) ->
    forall_program m ths (well_typed_references m) ->
    forall_program m ths SafeSpawns ->
    (* --- *)
    safe_memory_sharing m ths ->
    m / ths ~~[tc]~~>* m' / ths' ->
    safe_memory_sharing m' ths'.
Proof.
  intros * ? ? ? ? ? ? Hmultistep. induction Hmultistep; trivial.
  do 6 auto_specialize.
  eapply (safe_memory_sharing_preservation m' m'' ths' ths''); eauto.
  - admit.
  - eapply well_typed_multistep_preservation; eauto.
  - eapply valid_addresses_multistep_preservation; eauto.
  - eapply well_typed_multistep_preservation; eauto.
  - eapply safe_spawns_multistep_preservation; eauto.
Admitted.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma todo : forall m t ad ad' v Tr,
  valid_accesses m t ->
  ~ access m t ad ->
  access m[ad' <- (v, Tr)] t ad ->
  access m t ad'.
Proof.
  intros * ? Hnacc Hacc. eapply nacc_iff in Hnacc.
  induction Hnacc; try inversion_vac; inversion_acc; try lia;
  try solve [
    try
      (  destruct (acc_dec m t ad')
      || destruct (acc_dec m t1 ad')
      || destruct (acc_dec m t2 ad')
      );
    eauto using access; exfalso;
    eapply (mem_set_nacc1 _ _ ad ad' (v, Tr)); eauto using vac_nacc_length
  ];
  try solve [
    destruct (acc_dec m t1 ad'); eauto using access;
    destruct (acc_dec m t2 ad'); eauto using access;
    exfalso;
    eapply (mem_set_nacc1 _ _ ad ad' (v, Tr)); eauto using vac_nacc_length
  ].
  destruct (Nat.eq_dec ad ad'); subst; eauto using access. simpl_array.
  rename ad'0 into AD.
  eapply acc_mem; eauto.
  destruct (acc_dec m m[ad].tm ad'); trivial. exfalso.
  eapply (mem_set_nacc1 _ _ AD ad' (v, Tr)); eauto using vac_nacc_length.
Qed.

Local Lemma cstep_nacc_preservation : forall m m' ths ths' tid tid' ad eff,
  ad <> #m ->
  tid < #ths ->
  forall_threads ths well_typed ->
  forall_threads ths (valid_accesses m) ->
  safe_memory_sharing m ths ->
  ~ access m ths[tid] ad ->
  m / ths ~~[tid', eff]~~> m' / ths' ->
  ~ access m' ths'[tid] ad.
Proof.
  intros * ? ? Htype ? Hsms. intros. rename ad into ad'.
  destruct (Htype tid'). inversion_clear_cstep;
  destruct (Nat.eq_dec tid tid'); subst; simpl_array;
  eauto using mstep_nacc_preservation, step_spawn_nacc_preservation.
  inversion_mstep; eauto using vac_nacc_length, mem_add_nacc.
  assert (UnsafeAccess m ths[tid'] ad) by eauto using step_write_requires_uacc.
  intros F.
  eapply todo in F; eauto.
  eapply (Hsms tid' tid); eauto.
Qed.

Theorem cstep_nacc_multistep_preservation : forall m m' ths ths' tid ad tc,
  ad <> #m ->
  tid < #ths ->
  forall_threads ths well_typed ->
  forall_threads ths (valid_accesses m) ->
  safe_memory_sharing m ths ->
  ~ access m ths[tid] ad ->
  m / ths ~~[tc]~~>* m' / ths' ->
  ~ access m' ths'[tid] ad.
Proof.
  intros * ? ? Htype ? Hsms. intros.
  induction H3; trivial.
  do 6 auto_specialize.
  eapply (cstep_nacc_preservation m' _ ths'); eauto.
Admitted.

