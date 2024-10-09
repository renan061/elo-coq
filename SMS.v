From Elo Require Import Core.

From Elo Require Import Access.

(* ------------------------------------------------------------------------- *)
(* safe-memory-sharing                                                       *)
(* ------------------------------------------------------------------------- *)

Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  write_access ad m ths[tid1] ->
  ~ write_access ad m ths[tid2].

(* ------------------------------------------------------------------------- *)

Local Lemma tstep_length_tid : forall ths tid e t,
  ths[tid] --[e]--> t ->
  tid < #ths.
Proof.
  intros.
  decompose sum (lt_eq_lt_dec tid (#ths)); subst; sigma; eauto; invc_tstep.
Qed.

Local Ltac destruct_sms ths tid tid1 tid2 :=
  assert (Hlt : tid < #ths) by eauto using tstep_length_tid;
  destruct (nat_eq_dec tid tid1), (nat_eq_dec tid tid2); subst;
  try contradiction.

Lemma wacc_inheritance_subst : forall m x Tx t tx ad,
  write_access ad m <{[x := tx] t}> ->
  write_access ad m <{call <{fn x Tx t}> tx}>.
Proof.
  intros. induction t; eauto; simpl in *;
  try (destruct str_eq_dec; subst; eauto using write_access);
  invc_wacc; auto_specialize; repeat invc_wacc; eauto using write_access.
Qed.

Lemma wacc_inheritance_none : forall m t1 t2 ad,
  write_access ad m t2 ->
  t1 --[e_none]--> t2 ->
  write_access ad m t1.
Proof.
  intros. ind_tstep; try inv_wacc;
  eauto using wacc_inheritance_subst, write_access.
Qed.

Lemma nwacc_preservation_none : forall m t1 t2 ad,
  ~ write_access ad m t1 ->
  t1 --[e_none]--> t2 ->
  ~ write_access ad m t2.
Proof.
  intros ** Hwacc.
  ind_tstep. inv_nuacc; try inv_uacc; eauto.
  inv_nuacc. contradict Huacc. eauto using (may_subst (unsafe_access ad)).
Qed.

Local Lemma sms_tstep_none_preservation : forall m t ths tid,
  safe_memory_sharing m ths ->
  ths[tid] --[e_none]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros ** tid1 tid2 **. destruct_sms ths tid tid1 tid2; sigma.
  - eauto using wacc_inheritance_none.
  - eauto using nwacc_preservation_none.
  - admit.
Qed.
