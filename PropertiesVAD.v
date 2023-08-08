From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import AnyTerm.
From Elo Require Import Meta.

From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* valid-addresses implies valid-accesses                                    *)
(* ------------------------------------------------------------------------- *)

Local Lemma acc_then_hasad : forall m t ad,
  access ad m t ->
  t has_address ad \/ (exists ad', m[ad'].tm has_address ad).
Proof.
  intros * Hacc. induction Hacc; try decompose [or and] IHHacc;
  eauto using anyt, is_address.
Qed.

Lemma vad_then_vac : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  valid_accesses m t.
Proof.
  intros * Hmvad ? ? Hacc. autounfold with vad in Hmvad.
  eapply acc_then_hasad in Hacc as [? | [? ?]]; eauto.
Qed.

Lemma mvad_then_mvac : forall m,
  forall_memory m (valid_addresses m) ->
  forall_memory m (valid_accesses m).
Proof.
  intros * Hmvad ? ? Hacc. autounfold with vad in Hmvad.
  eapply acc_then_hasad in Hacc as [? | [? ?]]; eauto.
Qed.

Corollary forall_program_vad_then_vac : forall m ths,
  forall_program m ths (valid_addresses m) ->
  forall_program m ths (valid_accesses m).
Proof.
  intros * [? ?]; split; eauto using mvad_then_mvac.
  intros ?. eauto using vad_then_vac.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Module Preservation.

  (* subst & mem ----------------------------------------------------------- *)

  Lemma vad_subst_preservation : forall m t tx x,
    valid_addresses m t ->
    valid_addresses m tx ->
    valid_addresses m ([x := tx] t).
  Proof.
    intros.
    induction t; trivial; simpl; try solve [inv_vad; eauto with vad];
    destruct string_eq_dec; subst; trivial. inv_vad. eauto with vad.
  Qed.

  Lemma vad_mem_add_preservation : forall m t vT,
    valid_addresses m t ->
    valid_addresses (m +++ vT) t.
  Proof.
    intros. induction t; eauto with vad; inv_vad; eauto with vad.
    intros ? ?. inv_hasad. rewrite add_increments_length. eauto.
  Qed.

  Lemma vad_mem_set_preservation : forall m t ad vT,
    valid_addresses m t ->
    valid_addresses m[ad <- vT] t.
  Proof.
    intros. induction t; eauto with vad; inv_vad; eauto with vad.
    intros ? ?. inv_hasad. rewrite set_preserves_length. assumption.
  Qed.

  (* tstep ----------------------------------------------------------------- *)

  Lemma vad_tstep_none_preservation : forall m t t',
    valid_addresses m t ->
    t --[EF_None]--> t' ->
    valid_addresses m t'.
  Proof.
    intros. induction_tstep; inv_vad; eauto with vad. 
    inv_vad. eauto using vad_subst_preservation.
  Qed.

  Lemma vad_tstep_alloc_preservation : forall m t t' v T,
    valid_addresses m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    valid_addresses (m +++ (v, T)) t'.
  Proof.
    intros. induction_tstep; inv_vad;
    eauto using vad_mem_add_preservation with vad.
    intros ? ?. inv_hasad. rewrite add_increments_length. eauto.
  Qed.

  Lemma vad_tstep_read_preservation : forall m t t' ad v,
    valid_addresses m v ->
    valid_addresses m t ->
    t --[EF_Read ad v]--> t' ->
    valid_addresses m t'.
  Proof.
    intros. induction_tstep; inv_vad; eauto with vad.
  Qed.

  Lemma vad_tstep_write_preservation : forall m t t' ad v T,
    valid_addresses m t ->
    t --[EF_Write ad v T]--> t' ->
    valid_addresses m[ad <- (v, T)] t'.
  Proof.
    intros. induction_tstep; inv_vad;
    eauto using vad_mem_set_preservation with vad.
  Qed.

  Lemma vad_tstep_spawn_preservation : forall m t t' block,
    valid_addresses m t ->
    t --[EF_Spawn block]--> t' ->
    valid_addresses m t'.
  Proof.
    intros. induction_tstep; inv_vad; eauto with vad.
  Qed.

  (* mstep ----------------------------------------------------------------- *)

  Corollary vad_mstep_preservation : forall m m' t t' e,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    m / t ==[e]==> m' / t' ->
    valid_addresses m' t'.
  Proof.
    intros. inv_mstep;
    eauto using vad_tstep_none_preservation,
                vad_tstep_alloc_preservation,
                vad_tstep_read_preservation,
                vad_tstep_write_preservation.
  Qed.

  (* cstep ----------------------------------------------------------------- *)

  Lemma vad_thread_default : forall m,
    valid_addresses m thread_default.
  Proof.
    intros. eauto with vad.
  Qed.

  Lemma vad_spawn_block : forall m t t' block,
    valid_addresses m t ->
    t --[EF_Spawn block]--> t' ->
    valid_addresses m block.
  Proof.
    intros. induction_tstep; inv_vad; eauto.
  Qed.

  Lemma vad_untouched_threads_preservation : forall m m' ths tid tid' t' e,
    forall_threads ths (valid_addresses m) ->
    tid <> tid' ->
    tid' < #ths ->
    m / ths[tid] ==[e]==> m' / t' ->
    valid_addresses m' ths[tid'].
  Proof.
    intros. inv_mstep; 
    eauto using vad_mem_add_preservation, vad_mem_set_preservation.
  Qed.

  Corollary vad_cstep_preservation : forall m m' ths ths' tid e,
    forall_program m ths (valid_addresses m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' (valid_addresses m').
  Proof.
    intros. eauto 6 using cstep_preservation,
      vad_tstep_spawn_preservation,
      vad_mstep_preservation,
      vad_thread_default,
      vad_spawn_block,
      vad_untouched_threads_preservation.
  Qed.

  (* tstep mem ------------------------------------------------------------- *)

  Lemma vad_tstep_alloc_mem_preservation : forall m t t' v T,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    forall_memory  (m +++ (v, T)) (valid_addresses (m +++ (v, T))).
  Proof.
    assert (forall m t t' ad v T,
      valid_addresses m t ->
      t --[EF_Alloc ad v T]--> t' ->
      valid_addresses m v)
        by (intros; induction_tstep; inv_vad; eauto).
    (* main proof *)
    intros ** ad.
    decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
    eauto using vad_mem_add_preservation with vad.
  Qed.

  Lemma vad_tstep_write_mem_preservation : forall m t t' ad v T,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    t --[EF_Write ad v T]--> t' ->
    forall_memory m[ad <- (v, T)] (valid_addresses m[ad <- (v, T)]).
  Proof.
    assert (forall m t t' ad v T,
      valid_addresses m t ->
      t --[EF_Write ad v T]--> t' ->
      valid_addresses m v)
        by (intros; induction_tstep; inv_vad; eauto).
    (* main proof *)
    intros ** ad'.
    assert (ad < #m)
      by (intros; induction_tstep; inv_vad; eauto; inv_vad; assumption).
    destruct (nat_eq_dec ad ad'); subst; simpl_array;
    eauto using vad_mem_set_preservation.
  Qed.

  (* mstep mem ------------------------------------------------------------- *)

  Corollary vad_mstep_mem_preservation : forall m m' t t' e,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    m / t ==[e]==> m' / t' ->
    forall_memory m' (valid_addresses m').
  Proof.
    intros. inv_mstep;
    eauto using vad_tstep_alloc_mem_preservation,
                vad_tstep_write_mem_preservation.
  Qed.

  (* cstep mem ------------------------------------------------------------- *)

  Corollary vad_cstep_mem_preservation : forall m m' ths ths' tid e,
    forall_program m ths (valid_addresses m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_memory m' (valid_addresses m').
  Proof.
    intros * [? ?] ?. inv_cstep; eauto using vad_mstep_mem_preservation.
  Qed.

  (* valid-addresses preservation ------------------------------------------ *)

  Theorem valid_addresses_preservation : forall m m' ths ths' tid e,
    forall_program m ths (valid_addresses m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_program m' ths' (valid_addresses m').
  Proof.
    eauto using vad_cstep_preservation, vad_cstep_mem_preservation.
  Qed.

End Preservation.

