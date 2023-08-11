From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

From Elo Require Import PropertiesVAD.

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
(* access inheritance                                                        *)
(* ------------------------------------------------------------------------- *)

Module Inheritance.
  Lemma alt_acc_mem_set_inheritance : forall m t ad ad' vT,
    ~ access ad' m t ->
    (* --- *)
    access ad m[ad' <- vT] t ->
    access ad m t.
  Proof.
    intros * ? Hacc. induction Hacc; inv_nacc; eauto using access.
    simpl_array. eauto using access.
  Qed.
End Inheritance.

(* ------------------------------------------------------------------------- *)
(* not-access preservation                                                   *)
(* ------------------------------------------------------------------------- *)

Module PreservationNACC.
  (* subst & mem ----------------------------------------------------------- *)

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
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    (* --- *)
    ad < #m ->
    ~ access ad m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    ~ access ad (m +++ (v, T)) t'.
  Proof.
    intros. induction_tstep; inv_vad; inv_nacc;
    eauto using nacc_mem_add_preservation, nacc_vad_length with acc.
    eapply nacc_ad.
    - intros ?. subst. eauto.
    - simpl_array. eauto using nacc_mem_add_preservation, nacc_vad_length.
  Qed.

  Lemma nacc_tstep_read_preservation : forall m t t' ad ad',
    ~ access ad m t ->
    t --[EF_Read ad' m[ad'].tm]--> t' ->
    ~ access ad m t'.
  Proof.
    intros. induction_tstep; inv_nacc; eauto with acc.
    inv_nacc. assumption.
  Qed.

  Lemma nacc_tstep_write_preservation : forall m t t' ad ad' v T,
    ~ access ad m t ->
    t --[EF_Write ad' v T]--> t' ->
    ~ access ad m[ad' <- (v, T)] t'.
  Proof.
    intros.
    assert (~ access ad m v) by eauto using nacc_tstep_write_value.
    induction_tstep; inv_nacc; eauto using nacc_mem_set_preservation with acc.
  Qed.

  Lemma nacc_tstep_spawn_preservation : forall m t t' block ad,
    ~ access ad m t ->
    t --[EF_Spawn block]--> t' ->
    ~ access ad m t'.
  Proof.
    intros. induction_tstep; eauto with acc; inv_nacc; eauto with acc.
  Qed.

  (* mstep ----------------------------------------------------------------- *)

  Corollary nacc_mstep_preservation : forall m m' t t' ad e,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    (* --- *)
    ad < #m ->
    ~ access ad m t ->
    m / t ==[e]==> m' / t' ->
    ~ access ad m' t'.
  Proof.
    intros. inv_mstep;
    eauto using nacc_tstep_none_preservation,
                nacc_tstep_alloc_preservation,
                nacc_tstep_read_preservation,
                nacc_tstep_write_preservation.
  Qed.

  (* cstep ----------------------------------------------------------------- *)

  Local Lemma uacc_tstep_write_requirement : forall m t t' ad v T,
    well_typed_term t ->
    t --[EF_Write ad v T]--> t' ->
    unsafe_access ad m t.
  Proof.
    intros * [T' ?] **. generalize dependent T'.
    induction_tstep; intros; inv_type; eauto using unsafe_access.
    inv_type. eauto using unsafe_access.
  Qed.

  Lemma nacc_untouched_threads_preservation : forall m m' ths tid tid' t' ad e,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    forall_threads ths well_typed_term ->
    safe_memory_sharing m ths ->
    (* --- *)
    tid <> tid' ->
    tid' < #ths ->
    ~ access ad m ths[tid'] ->
    m / ths[tid] ==[e]==> m' / t' ->
    ~ access ad m' ths[tid'].
  Proof.
    intros * ? ? ? Hsms **. rename ad into ad'. invc_mstep;
    eauto using nacc_mem_add_preservation, nacc_vad_length.
    eapply alt_nacc_mem_set_preservation; eauto.
    assert (unsafe_access ad m ths[tid])
      by eauto using uacc_tstep_write_requirement.
    intros ?. eapply (Hsms tid tid'); eauto.
  Qed.

  Corollary nacc_cstep_preservation : forall m m' ths ths' tid tid' ad e,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    forall_threads ths well_typed_term ->
    safe_memory_sharing m ths ->
    (* --- *)
    ad < #m ->
    tid < #ths ->
    ~ access ad m ths[tid] ->
    m / ths ~~[tid', e]~~> m' / ths' ->
    ~ access ad m' ths'[tid].
  Proof.
    intros. invc_cstep; destruct (nat_eq_dec tid tid'); subst; simpl_array;
    eauto using nacc_tstep_spawn_preservation,
                nacc_mstep_preservation,
                nacc_untouched_threads_preservation.
  Qed.
End PreservationNACC.

(* ------------------------------------------------------------------------- *)
(* misc. properties                                                          *)
(* ------------------------------------------------------------------------- *)

(* TODO: rename and ask Roberto about that test scrambling thing. *)
Theorem acc_from_mem_set : forall m t ad ad' vT,
  ~ access ad m t ->
  access ad m[ad' <- vT] t ->
  access ad' m t.
Proof.
  intros. induction t; inv_acc; inv_nacc; eauto using access.
  match goal with |- access _ _ <{&?ad :: _}> => rename ad into ad'' end.
  destruct (nat_eq_dec ad' ad''); subst; eauto using access.
  simpl_array. eapply acc_mem; trivial.
  destruct (acc_dec ad' m m[ad''].tm); trivial. exfalso.
  eapply (PreservationNACC.alt_nacc_mem_set_preservation _ _ ad ad'); eauto.
Qed.

