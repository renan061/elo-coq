From Elo Require Import Util.
From Elo Require Import Core.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

From Elo Require Import PropertiesVAD.
From Elo Require Import PropertiesCTR.
From Elo Require Import PropertiesACC.
From Elo Require Import PropertiesUACC.
From Elo Require Import PropertiesSS.

(* ------------------------------------------------------------------------- *)
(* misc. properties                                                          *)
(* ------------------------------------------------------------------------- *)

(* If there is access: *)
(* The access is unsafe if and only if the memtyp is mutable. *)
Lemma uacc_iff_memtyp_mut : forall m t ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  access ad m t ->
  (* --- *)
  unsafe_access ad m t <-> (exists T, m[ad].typ = <{{&T}}>).
Proof.
  intros * ? ? ? Hacc. split.
  - intros Huacc. clear Hacc. induction Huacc; inv_ctr; eauto.
  - intros [T Heq].
    induction Hacc; inv_ctr; eauto using unsafe_access.
    + exfalso. eauto using nuacc_from_immutable_type.
    + rewrite Heq in *. discriminate.
Qed.

(* If one access is unsafe, then all accesses are unsafe. *)
Corollary uacc_from_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  consistently_typed_references m t' ->
  (* --- *)
  access ad m t ->
  unsafe_access ad m t' ->
  unsafe_access ad m t.
Proof.
  intros.
  eapply uacc_iff_memtyp_mut; eauto.
  eapply uacc_iff_memtyp_mut; eauto using uacc_then_acc.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

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
    induction_tstep; intros; inv_type; eauto using unsafe_access.
    inv_type. eauto using unsafe_access.
  }
  (* main proof *)
  intros * Hneq Htype Hsms ? Hacc.
  destruct (Htype tid). specialize (Hsms _ _ _ Hneq Hacc); eauto.
Qed.

(* tstep ------------------------------------------------------------------- *)

(*
  Three cases:
  - needs nuacc-tstep-preservation;
  - needs acc-tstep-inheritance;
  - just safe-memory-sharing.
*)

Local Ltac destruct_sms ths tid tid1 tid2 :=
  assert (Hlt : tid < #ths) by eauto using step_length_tid;
  destruct (nat_eq_dec tid tid1), (nat_eq_dec tid tid2); subst;
  try contradiction.

Lemma sms_tstep_none_preservation : forall m t ths tid,
  safe_memory_sharing m ths ->
  ths[tid] --[EF_None]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros ** tid1 tid2 **. destruct_sms ths tid tid1 tid2; simpl_array;
  eauto using acc_tstep_none_inheritance, nuacc_tstep_none_preservation.
Qed.

Lemma sms_tstep_alloc_preservation : forall m t v ths tid T,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Alloc (#m) v T]--> t ->
  safe_memory_sharing (m +++ (v, T)) ths[tid <- t].
Proof.
  intros ** tid1 tid2 ** Huacc.
  assert (Hvac : forall_threads ths (valid_accesses m))
    by (intros ?; eauto using vad_then_vac).
  assert (forall tid, ~ unsafe_access (#m) m ths[tid])
    by eauto using nuacc_vad_length.
  autounfold with vac in Hvac.
  eapply uacc_then_acc in Huacc as ?. contradict Huacc.
  destruct_sms ths tid tid1 tid2; simpl_array;
  eauto 6 using nuacc_tstep_alloc_preservation,
                acc_tstep_alloc_inheritance,
                nuacc_mem_add_preservation,
                acc_mem_add_inheritance.
Qed.

Lemma sms_tstep_read_preservation : forall m t ad ths tid,
  forall_memory m value ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Read ad m[ad].tm]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros * ? Hwtt ** tid1 tid2 **. destruct (Hwtt tid1).
  destruct_sms ths tid tid1 tid2; simpl_array;
  eauto using acc_tstep_read_inheritance, nuacc_tstep_read_preservation.
Qed.

Lemma sms_tstep_write_preservation : forall m ths t tid ad v T,
  forall_threads ths well_typed_term ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Write ad v T]--> t ->
  safe_memory_sharing m[ad <- (v, T)] ths[tid <- t].
Proof.
  intros ** tid1 tid2 ** Huacc.
  eapply uacc_then_acc in Huacc as ?. contradict Huacc.
  destruct_sms ths tid tid1 tid2; simpl_array;
  try assert (~ access ad m ths[tid1]) by eauto using step_write_sms_helper;
  try assert (~ access ad m ths[tid2]) by eauto using step_write_sms_helper;
  eauto 7 using uacc_then_acc,
    nuacc_tstep_write_preservation,
    acc_tstep_write_inheritance,
    alt_nuacc_mem_set_preservation,
    alt_acc_mem_set_inheritance.
Qed.

Lemma sms_tstep_spawn_preservation : forall m ths t block tid,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  forall_memory m (consistently_typed_references m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (consistently_typed_references m) ->
  forall_threads ths safe_spawns ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Spawn block]--> t ->
  safe_memory_sharing m (ths[tid <- t] +++ block).
Proof.
  intros ** tid1 tid2 **.
  assert (~ unsafe_access ad m block) by eauto using nuacc_spawn_block.
  assert (consistently_typed_references m block) by eauto using ctr_spawn_block.
  destruct_sms ths tid tid1 tid2;
  decompose sum (lt_eq_lt_dec tid1 (#ths)); subst; simpl_array;
  decompose sum (lt_eq_lt_dec tid2 (#ths)); subst; simpl_array;
  try solve [inv_step | inv_acc | intros ?; inv_uacc];
  eauto using uacc_from_association,
    nuacc_tstep_spawn_preservation,
    acc_tstep_spawn_inheritance.
Qed.

Corollary sms_mstep_preservation : forall m m' t e ths tid,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  (* --- *)
  safe_memory_sharing m ths ->
  m / ths[tid] ==[e]==> m' / t ->
  safe_memory_sharing m' ths[tid <- t].
Proof.
  intros. inv_mstep;
  eauto using sms_tstep_none_preservation,
              sms_tstep_alloc_preservation,
              sms_tstep_read_preservation,
              sms_tstep_write_preservation.
Qed.

(* safe-memory-sharing preservation ---------------------------------------- *)

Theorem safe_memory_sharing_preservation : forall m m' ths ths' tid e,
  forall_memory m value ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  forall_program m ths safe_spawns ->
  (* --- *)
  safe_memory_sharing m ths ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  safe_memory_sharing m' ths'.
Proof.
  intros * ? [? ?] [_ ?] [? ?] [_ ?] **.
  invc_cstep; eauto using sms_tstep_spawn_preservation, sms_mstep_preservation.
Qed.

