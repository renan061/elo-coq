From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* misc. properties                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma nacc_vad_length : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ access (#m) m t.
Proof.
  intros * ? Hvad Hacc. remember (#m) as ad.
  induction Hacc; inv_vad; eauto. rewrite Heqad in *. eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Module Preservation.

  Lemma nacc_subst_preservation : forall m t tx ad x,
    ~ access ad m t ->
    ~ access ad m tx ->
    ~ access ad m ([x := tx] t).
  Proof.
    intros. induction t; simpl; eauto using access;
    try inv_nacc; eauto with acc;
    destruct string_eq_dec; subst; eauto with acc.
  Qed.

  Lemma nacc_mem_add_preservation : forall m t ad vT,
    ~ access (#m) m t ->
    (* --- *)
    ~ access ad m t ->
    ~ access ad (m +++ vT) t.
  Proof.
    intros ** Hacc. induction Hacc; inv_nacc; inv_nacc; eauto.
    decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; eauto.
  Qed.

  Lemma nacc_mem_set_preservation : forall m t ad ad' v T,
    ~ access ad m v ->
    ~ access ad m t ->
    ~ access ad m[ad' <- (v, T)] t.
  Proof.
    assert (forall m ad ad' v,
      access ad m[ad' <- v] m[ad' <- v][ad'].tm -> ad' < #m). {
        intros * H. decompose sum (lt_eq_lt_dec ad' (#m)); subst; trivial;
        simpl_array; simpl in *; inv_acc.
    }
    (* main proof *)
    intros ** Hacc. induction Hacc; eauto using access.
    match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
    destruct (nat_eq_dec ad' ad''); subst;
    try (assert (ad'' < #m) by eauto);
    simpl_array; eauto using access.
  Qed.

  Lemma alt_nacc_mem_set_preservation : forall m t ad ad' vT,
    ~ access ad' m t ->
    (* --- *)
    ~ access ad m t ->
    ~ access ad m[ad' <- vT] t.
  Proof.
    intros ** Hacc.
    induction Hacc; inv_nacc; inv_nacc; eauto using access.
    simpl_array. eauto.
  Qed.

  (* tstep ----------------------------------------------------------------- *)

  Lemma nacc_tstep_none_preservation : forall m t t' ad,
    ~ access ad m t ->
    t --[EF_None]--> t' ->
    ~ access ad m t'.
  Proof.
    intros. induction_tstep; inv_nacc; eauto with acc.
    inv_nacc. eauto using nacc_subst_preservation.
  Qed.

  Lemma nacc_tstep_alloc_preservation : forall m t t' ad v T,
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

  Lemma nacc_tstep_read_preservation : forall m t t' ad ad',
    ~ access ad m t ->
    t --[EF_Read ad' m[ad'].tm]--> t' ->
    ~ access ad m t'.
  Proof.
    intros * Hnacc ?. induction_step; inv_nacc Hnacc;
    try solve [eapply nacc_iff; eauto using not_access].
    match goal with H : ~ access _ _ _ |- _ => inv_nacc H end.
  Qed.

  Lemma nacc_tstep_write_preservation : forall m t t' ad ad' v T,
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

  Lemma nacc_tstep_spawn_preservation : forall m t t' block ad,
    ~ access ad m t ->
    t --[EF_Spawn block]--> t' ->
    ~ access ad m t'.
  Proof.
    intros * Hnacc ?. induction_step; inv_nacc Hnacc;
    eapply nacc_iff; eauto using not_access.
  Qed.

  Corollary nacc_mstep_preservation : forall m m' t t' ad e,
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

  Lemma nacc_thread_default : forall m ad,
    ~ access ad m thread_default.
  Proof.
    intros. eapply nacc_iff. eauto using not_access.
  Qed.

  Lemma nacc_spawn_block : forall m t t' block ad,
    ~ access ad m t ->
    t --[EF_Spawn block]--> t' ->
    access ad m block ->
    exists T, m[ad].typ = <{{ i&T }}>.
  Proof.
    (* need SafeSpawns to prove this. *)
  Abort.

  Lemma nacc_untouched_threads_preservation :
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

End Module.
