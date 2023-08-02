From Coq Require Import Arith.Arith.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import ValidAddresses.
From Elo Require Import Access.
From Elo Require Import NotAccess.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Local Lemma nacc_subst_preservation : forall m t tx ad x,
  ~ access m t ad ->
  ~ access m tx ad ->
  ~ access m ([x := tx] t) ad.
Proof.
  intros * Hnacc ?. generalize dependent tx.
  induction t; intros; trivial; simpl;
  try solve [eapply nacc_iff; inv_nacc Hnacc; eauto using not_access];
  destruct string_eq_dec; trivial.
  inv_nacc Hnacc. eapply nacc_iff. eauto using not_access.
Qed.

Local Lemma nacc_mem_add_preservation : forall m t ad vT,
  ~ access m t (#m) ->
  ~ access m t ad ->
  ~ access (m +++ vT) t ad.
Proof.
  intros * Hnacc1 Hnacc2 F. induction F; inv_nacc Hnacc2.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; inv_nacc Hnacc1.
  eapply IHF; trivial. eapply nacc_iff. eauto using not_access.
Qed.

Local Lemma nacc_mem_set_preservation : forall m t ad ad' v T,
  ~ access m v ad ->
  ~ access m t ad ->
  ~ access m[ad' <- (v, T)] t ad.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m)
    by (intros; split; destruct n; eauto).
  assert (forall m ad ad' v,
    access m[ad' <- v] m[ad' <- v][ad'].tm ad -> ad' < length m). {
      intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
      rewrite (get_set_invalid memory_default) in H; trivial. inversion H.
  }
  (* main proof *)
  intros * ? ? Hacc. remember (m[ad' <- (v, T)]) as m'.
  induction Hacc; inv_clear Heqm'; eauto using access.
  match goal with
  | _ : ~ access _ <{ & ?ad :: _ }> _ |- _ => 
    decompose sum (nat_eq_dec ad' ad); subst; try (assert (ad < #m) by eauto)
  end;
  simpl_array; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma nacc_tstep_none_preservation : forall m t t' ad,
  ~ access m t ad ->
  t --[EF_None]--> t' ->
  ~ access m t' ad.
Proof.
  intros * Hnacc. intros. induction_step; inv_nacc Hnacc;
  try solve [eapply nacc_iff; eauto using not_access].
  match goal with H : ~ access _ <{ fn _ _ _ }> _ |- _ => inv_nacc H end.
  eauto using nacc_subst_preservation.
Qed.

Local Lemma nacc_tstep_alloc_preservation : forall m t t' ad v T,
  ad < #m ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ access m t ad ->
  t --[EF_Alloc (#m) v T]--> t' ->
  ~ access (m +++ (v, T)) t' ad.
Proof.
  intros * ? ? ? Hnacc ?.
  induction_step; inversion_vad; inv_nacc Hnacc; eapply nacc_iff;
  eauto using not_access, nacc_mem_add_preservation, vad_nacc_length.
  eapply nacc_ad. eauto using not_eq_sym, Nat.lt_neq.
  simpl_array. eauto using nacc_mem_add_preservation, vad_nacc_length.
Qed.

Local Lemma nacc_tstep_read_preservation : forall m t t' ad ad',
  ~ access m t ad ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  ~ access m t' ad.
Proof.
  intros * Hnacc ?. induction_step; inv_nacc Hnacc;
  try solve [eapply nacc_iff; eauto using not_access].
  match goal with H : ~ access _ _ _ |- _ => inv_nacc H end.
Qed.

Local Lemma nacc_tstep_write_preservation : forall m t t' ad ad' v T,
  ~ access m t ad ->
  t --[EF_Write ad' v T]--> t' ->
  ~ access m[ad' <- (v, T)] t' ad.
Proof.
  assert (forall m t t' ad ad' v T,
    ~ access m t ad ->
    t --[EF_Write ad' v T]--> t' ->
    ~ access m v ad)
    by (intros; induction_step; eauto using access).
  (* main proof *)
  intros * Hnacc ?. induction_step; inv_nacc Hnacc;
  eapply nacc_iff; eauto using not_access, nacc_mem_set_preservation.
Qed.

Local Lemma nacc_tstep_spawn_preservation : forall m t t' block ad,
  ~ access m t ad ->
  t --[EF_Spawn block]--> t' ->
  ~ access m t' ad.
Proof.
  intros * Hnacc ?. induction_step; inv_nacc Hnacc;
  eapply nacc_iff; eauto using not_access.
Qed.

Local Corollary nacc_mstep_preservation : forall m m' t t' e ad,
  ad < #m ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ access m t ad ->
  m / t ==[e]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros. inversion_mstep;
  eauto using nacc_tstep_none_preservation,
    nacc_tstep_alloc_preservation,
    nacc_tstep_read_preservation,
    nacc_tstep_write_preservation.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma nacc_thread_default_preservation : forall m ad,
  ~ access m thread_default ad.
Proof.
  intros. eapply nacc_iff. eauto using not_access.
Qed.

Local Lemma nacc_spawn_block_preservation : forall m t t' block ad,
  ~ access m t ad ->
  t --[EF_Spawn block]--> t' ->
  ~ access m block ad.
Proof.
Abort.

Local Lemma nacc_untouched_threads_preservation :
  forall m m' ths tid tid' t' e ad,
    forall_threads ths (fun t => ~ access m t ad) ->
    tid <> tid' ->
    tid' < #ths ->
    m / ths[tid] ==[e]==> m' / t' ->
    ~ access m' ths[tid'] ad.
Proof.
Abort.

Corollary nacc_cstep_preservation : forall m m' ths ths' tid e,
  forall_memory m (~ access m) ->
  forall_threads ths (~ access m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_threads ths' (~ access m').
Proof.
Abort.

(* ------------------------------------------------------------------------- *)

Local Lemma nacc_tstep_alloc_mem_preservation : forall m t t' v T,
  ~ access m t ->
  forall_memory m (~ access m) ->
  t --[EF_Alloc (#m) v T]--> t' ->
  forall_memory  (m +++ (v, T)) (~ access (m +++ (v, T))).
Proof.
Qed.

Local Lemma nacc_tstep_write_mem_preservation : forall m t t' ad v T,
  ~ access m t ->
  forall_memory m (~ access m) ->
  t --[EF_Write ad v T]--> t' ->
  forall_memory m[ad <- (v, T)] (~ access m[ad <- (v, T)]).
Proof.
Qed.

Local Corollary nacc_mstep_mem_preservation : forall m m' t t' e,
  ~ access m t ->
  forall_memory m (~ access m) ->
  m / t ==[e]==> m' / t' ->
  forall_memory m' (~ access m').
Proof.
Qed.

Local Corollary nacc_cstep_mem_preservation : forall m m' ths ths' tid e,
  forall_threads ths (~ access m) ->
  forall_memory m (~ access m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_memory m' (~ access m').
Proof.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem not_access_preservation : forall m m' ths ths' tid e,
  forall_program m ths (~ access m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_program m' ths' (~ access m').
Proof.
Qed.

