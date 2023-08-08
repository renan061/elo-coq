
(* ------------------------------------------------------------------------- *)
(* important properties                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma acc_dec : forall m t ad,
  Decidable.decidable (access ad m t).
Proof. eauto using classic_decidable. Qed.

Theorem strong_acc_mem : forall m t ad ad',
  access ad' m t ->
  access ad  m (m[ad'].tm) ->
  access ad  m t.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access;
  match goal with
  |- access ?ad _ <{& ?ad' :: _}> => destruct (nat_eq_dec ad ad'); subst
  end;
  eauto using access.
Qed.

(* valid-addresses implies valid-accesses ---------------------------------- *)

Local Lemma acc_then_hasad : forall m t ad,
  access ad m t ->
  t has_address ad \/ (exists ad', m[ad'].tm has_address ad).
Proof.
  intros * Hacc. induction Hacc; try destruct IHHacc as [? | [? ?]];
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

Lemma vad_then_mvac : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  forall_memory m (valid_accesses m).
Proof.
  intros * Hmvad ? ? ? Hacc. autounfold with vad in Hmvad.
  eapply acc_then_hasad in Hacc as [? | [? ?]]; eauto.
Qed.

Corollary forall_threads_vad_then_vac : forall m ths,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (valid_accesses m).
Proof.
  intros ** ?. eauto using vad_then_vac.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Local Lemma vad_subst_preservation : forall m t tx x,
  valid_addresses m t ->
  valid_addresses m tx ->
  valid_addresses m ([x := tx] t).
Proof.
  intros. induction t; try inversion_vad; simpl; eauto with vad_constructors;
  destruct string_eq_dec; subst; trivial;
  autounfold with vad in *; eauto with has_address_inversion.
Qed.

Local Lemma vad_mem_add_preservation : forall m t vT,
  valid_addresses m t ->
  valid_addresses (m +++ vT) t.
Proof.
  intros. intros ? Hha. rewrite add_increments_length.
  induction Hha; try inversion_vad; eauto with has_address_inversion.
Qed.

Local Lemma vad_mem_set_preservation : forall m t ad vT,
  valid_addresses m t ->
  valid_addresses m[ad <- vT] t.
Proof.
  intros. intros ? Hha. rewrite set_preserves_length.
  induction Hha; try inversion_vad; eauto with has_address_inversion.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma vad_tstep_none_preservation : forall m t t',
  valid_addresses m t ->
  t --[EF_None]--> t' ->
  valid_addresses m t'.
Proof.
  intros. induction_step; inversion_vad; eauto with vad_constructors. 
  inversion_vad. eauto using vad_subst_preservation.
Qed.

Local Lemma vad_tstep_alloc_preservation : forall m t t' v T,
  valid_addresses m t ->
  t --[EF_Alloc (#m) v T]--> t' ->
  valid_addresses (m +++ (v, T)) t'.
Proof.
  intros. induction_step; inversion_vad;
  eauto using vad_mem_add_preservation with vad_constructors.
  intros ? ?. inversion_has_address. rewrite add_increments_length. eauto.
Qed.

Local Lemma vad_tstep_read_preservation : forall m t t' ad v,
  valid_addresses m v ->
  valid_addresses m t ->
  t --[EF_Read ad v]--> t' ->
  valid_addresses m t'.
Proof.
  intros. induction_step; inversion_vad; eauto with vad_constructors.
Qed.

Local Lemma vad_tstep_write_preservation : forall m t t' ad v T,
  valid_addresses m t ->
  t --[EF_Write ad v T]--> t' ->
  valid_addresses m[ad <- (v, T)] t'.
Proof.
  intros. assert (valid_addresses m v); induction_step; inversion_vad;
  eauto using vad_mem_set_preservation with vad_constructors.
Qed.

Local Lemma vad_tstep_spawn_preservation : forall m t t' block,
  valid_addresses m t ->
  t --[EF_Spawn block]--> t' ->
  valid_addresses m t'.
Proof.
  intros. induction_step; inversion_vad; eauto with vad_constructors.
Qed.

Local Corollary vad_mstep_preservation : forall m m' t t' e,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  m / t ==[e]==> m' / t' ->
  valid_addresses m' t'.
Proof.
  solve_mstep_preservation_using
    vad_tstep_none_preservation
    vad_tstep_alloc_preservation
    vad_tstep_read_preservation
    vad_tstep_write_preservation.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma vad_thread_default_preservation : forall m,
  valid_addresses m thread_default.
Proof.
  intros. eauto with vad_constructors.
Qed.

Local Lemma vad_spawn_block_preservation : forall m t t' block,
  valid_addresses m t ->
  t --[EF_Spawn block]--> t' ->
  valid_addresses m block.
Proof.
  intros. induction_step; inversion_vad; eauto.
Qed.

Local Lemma vad_untouched_threads_preservation : forall m m' ths tid tid' e t',
  forall_threads ths (valid_addresses m) ->
  tid <> tid' ->
  tid' < #ths ->
  m / ths[tid] ==[e]==> m' / t' ->
  valid_addresses m' ths[tid'].
Proof.
  intros. intros ? ?. autounfold with vad in *. inversion_mstep; eauto;
  (rewrite add_increments_length || rewrite set_preserves_length);
  eauto using Nat.lt_lt_succ_r.
Qed.

Corollary vad_cstep_preservation : forall m m' ths ths' tid e,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_threads ths' (valid_addresses m').
Proof.
  eauto 6 using cstep_preservation,
    vad_tstep_spawn_preservation,
    vad_mstep_preservation,
    vad_thread_default_preservation,
    vad_spawn_block_preservation,
    vad_untouched_threads_preservation.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma vad_tstep_alloc_mem_preservation : forall m t t' v T,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  t --[EF_Alloc (#m) v T]--> t' ->
  forall_memory  (m +++ (v, T)) (valid_addresses (m +++ (v, T))).
Proof.
  intros. intros ad.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
  intros ? ?; rewrite add_increments_length; autounfold with vad in *;
  eauto using anyt_alloc_generalization, Nat.lt_lt_succ_r
        with has_address_inversion.
Qed.

Local Lemma vad_tstep_write_mem_preservation : forall m t t' ad v T,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  t --[EF_Write ad v T]--> t' ->
  forall_memory m[ad <- (v, T)] (valid_addresses m[ad <- (v, T)]).
Proof.
  intros. intros ad'. 
  assert (ad < #m) by eauto using valid_address_write.
  destruct (eq_nat_dec ad ad'); subst; simpl_array;
  intros ? ?; rewrite set_preserves_length; autounfold with vad in *;
  eauto using anyt_write_generalization, Nat.lt_lt_succ_r.
Qed.

Local Corollary vad_mstep_mem_preservation : forall m m' t t' e,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  m / t ==[e]==> m' / t' ->
  forall_memory m' (valid_addresses m').
Proof.
  solve_mstep_mem_preservation_using 
    vad_tstep_alloc_mem_preservation 
    vad_tstep_write_mem_preservation.
Qed.

Local Corollary vad_cstep_mem_preservation : forall m m' ths ths' tid e,
  forall_threads ths (valid_addresses m) ->
  forall_memory m (valid_addresses m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_memory m' (valid_addresses m').
Proof.
  solve_cstep_mem_preservation_using vad_mstep_mem_preservation.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem valid_addresses_preservation : forall m m' ths ths' tid e,
  forall_program m ths (valid_addresses m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_program m' ths' (valid_addresses m').
Proof.
  intros * [? ?]. intros.
  eauto using vad_cstep_preservation, vad_cstep_mem_preservation.
Qed.

