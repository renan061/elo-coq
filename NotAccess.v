From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import ValidAddresses.
From Elo Require Import AccessCore.

Inductive not_access (ad : addr) (m : mem) : tm -> Prop :=
  | nacc_unit :
    not_access ad m <{unit}>

  | nacc_num : forall n,
    not_access ad m <{N n}>

  | nacc_ad : forall T ad',
    ad <> ad' ->
    ~ access ad m (m[ad'].tm) ->
    not_access ad m <{&ad' :: T}>

  | nacc_new : forall T t,
    ~ access ad m t ->
    not_access ad m <{new T t}>

  | nacc_load : forall t,
    ~ access ad m t ->
    not_access ad m <{*t}>

  | nacc_asg : forall t1 t2,
    ~ access ad m t1 ->
    ~ access ad m t2 ->
    not_access ad m <{t1 = t2}>

  | nacc_var : forall x,
    not_access ad m <{var x}>

  | nacc_fun : forall x Tx t,
    ~ access ad m t ->
    not_access ad m <{fn x Tx t}>

  | nacc_call : forall t1 t2,
    ~ access ad m t1 ->
    ~ access ad m t2 ->
    not_access ad m <{call t1 t2}>

  | nacc_seq : forall t1 t2,
    ~ access ad m t1 ->
    ~ access ad m t2 ->
    not_access ad m <{t1; t2}>

  | nacc_spawn : forall t,
    not_access ad m <{spawn t}>
  .

Theorem nacc_iff : forall m t ad,
  ~ access ad m t <-> not_access ad m t.
Proof.
  intros. split; intros Hnacc; destruct t;
  try (eapply nacc_ad
    || eapply nacc_asg
    || eapply nacc_call
    || eapply nacc_seq);
  eauto using access, not_access;
  intros ?; subst; try (inv_acc; inv_clear Hnacc); eauto using access.
  match goal with
  | Hnacc : ~ access ?ad' _ <{& ?ad :: _}> |- _ =>
    destruct (nat_eq_dec ad ad'); subst
  end;
  eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Ltac inv_nacc Hnacc :=
  eapply nacc_iff in Hnacc; inversion Hnacc; subst; eauto using access.

(* ------------------------------------------------------------------------- *)
(* length                                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma nacc_vad_length : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ access (#m) m t.
Proof.
  intros * ? Hvad Hacc. remember (#m) as ad.
  induction Hacc; inversion_vad; eauto. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Local Lemma nacc_subst_preservation : forall m t tx ad x,
  ~ access ad m t ->
  ~ access ad m tx ->
  ~ access ad m ([x := tx] t).
Proof.
  intros * Hnacc ?. induction t; simpl;
  try solve [inv_nacc Hnacc; eapply nacc_iff; eauto using not_access];
  destruct string_eq_dec; trivial.
  inv_nacc Hnacc. eapply nacc_iff. eauto using not_access.
Qed.

Local Lemma nacc_mem_add_preservation : forall m t ad vT,
  ~ access (#m) m t ->
  ~ access ad m t ->
  ~ access ad (m +++ vT) t.
Proof.
  intros * Hnacc1 Hnacc2 Hacc. induction Hacc; inv_nacc Hnacc2.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array;
  inv_nacc Hnacc1. eapply IHHacc; eapply nacc_iff; eauto using not_access.
Qed.

Local Lemma nacc_mem_set_preservation : forall m t ad ad' v T,
  ~ access ad m v ->
  ~ access ad m t ->
  ~ access ad m[ad' <- (v, T)] t.
Proof.
  assert (forall m ad ad' v,
    access ad m[ad' <- v] m[ad' <- v][ad'].tm -> ad' < length m). {
      intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
      rewrite (get_set_invalid memory_default) in H; trivial. inversion H.
  }
  (* main proof *)
  intros * ? ? Hacc. induction Hacc; eauto using access.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  destruct (nat_eq_dec ad' ad''); subst;
  try (assert (ad'' < #m) by eauto);
  simpl_array; eauto using access.
Qed.

(* alternative for mem_set ------------------------------------------------- *)

Local Lemma alt_mem_set_preservation : forall m t ad ad' vT,
  ~ access ad' m t ->
  ~ access ad m t ->
  ~ access ad m[ad' <- vT] t.
Proof.
  intros * Hnacc' Hnacc Hacc.
  induction Hacc; inv_nacc Hnacc'; inv_nacc Hnacc.
  simpl_array. eauto.
Qed.

(* tstep ------------------------------------------------------------------- *)

Local Lemma nacc_tstep_none_preservation : forall m t t' ad,
  ~ access ad m t ->
  t --[EF_None]--> t' ->
  ~ access ad m t'.
Proof.
  intros * Hnacc. intros. induction_step; inv_nacc Hnacc;
  try solve [eapply nacc_iff; eauto using not_access].
  match goal with H : ~ access _ _ <{ fn _ _ _ }> |- _ => inv_nacc H end.
  eauto using nacc_subst_preservation.
Qed.

Local Lemma nacc_tstep_alloc_preservation : forall m t t' ad v T,
  ad < #m ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ access ad m t ->
  t --[EF_Alloc (#m) v T]--> t' ->
  ~ access ad (m +++ (v, T)) t'.
Proof.
  intros * ? ? ? Hnacc ?.
  induction_step; inversion_vad; inv_nacc Hnacc; eapply nacc_iff;
  eauto using not_access, nacc_mem_add_preservation, nacc_vad_length.
  eapply nacc_ad. eauto using not_eq_sym, Nat.lt_neq.
  simpl_array. eauto using nacc_mem_add_preservation, nacc_vad_length.
Qed.

Local Lemma nacc_tstep_read_preservation : forall m t t' ad ad',
  ~ access ad m t ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  ~ access ad m t'.
Proof.
  intros * Hnacc ?. induction_step; inv_nacc Hnacc;
  try solve [eapply nacc_iff; eauto using not_access].
  match goal with H : ~ access _ _ _ |- _ => inv_nacc H end.
Qed.

Local Lemma nacc_tstep_write_preservation : forall m t t' ad ad' v T,
  ~ access ad m t ->
  t --[EF_Write ad' v T]--> t' ->
  ~ access ad m[ad' <- (v, T)] t'.
Proof.
  assert (forall m t t' ad ad' v T,
    ~ access ad m t ->
    t --[EF_Write ad' v T]--> t' ->
    ~ access ad m v)
    by (intros; induction_step; eauto using access).
  (* main proof *)
  intros * Hnacc ?. induction_step; inv_nacc Hnacc;
  eapply nacc_iff; eauto using not_access, nacc_mem_set_preservation.
Qed.

Local Lemma nacc_tstep_spawn_preservation : forall m t t' block ad,
  ~ access ad m t ->
  t --[EF_Spawn block]--> t' ->
  ~ access ad m t'.
Proof.
  intros * Hnacc ?. induction_step; inv_nacc Hnacc;
  eapply nacc_iff; eauto using not_access.
Qed.

Local Corollary nacc_mstep_preservation : forall m m' t t' e ad,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  ad < #m ->
  ~ access ad m t ->
  m / t ==[e]==> m' / t' ->
  ~ access ad m' t'.
Proof.
  intros. inversion_mstep;
  eauto using nacc_tstep_none_preservation,
    nacc_tstep_alloc_preservation,
    nacc_tstep_read_preservation,
    nacc_tstep_write_preservation.
Qed.

(* cstep ------------------------------------------------------------------- *)

Local Lemma nacc_thread_default_preservation : forall m ad,
  ~ access ad m thread_default.
Proof.
  intros. eapply nacc_iff. eauto using not_access.
Qed.

Local Lemma nacc_spawn_block_preservation : forall m t t' block ad,
  ~ access ad m t ->
  t --[EF_Spawn block]--> t' ->
  access ad m block ->
  exists T, m[ad].typ = <{{ i&T }}>.
Proof.
  (* need SafeSpawns to prove this. *)
Abort.

Local Lemma nacc_untouched_threads_preservation :
  forall m m' ths tid tid' t' e ad,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    tid <> tid' ->
    ~ access ad m ths[tid'] ->
    m / ths[tid] ==[e]==> m' / t' ->
    ~ access ad m' ths[tid'].
Proof.
  (* nees SMS to prove this. *)
Abort.

