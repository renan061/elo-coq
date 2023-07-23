From Coq Require Import Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import ValidAddresses.
From Elo Require Import Access.
From Elo Require Import References.
From Elo Require Import Soundness.
From Elo Require Import UnsafeAccess.
From Elo Require Import SafeSpawns.
From Elo Require Import SMS.

Theorem memory_value_multistep_preservation : forall m m' ths ths' tc,
  forall_memory m value ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_memory m' value.
Proof.
  assert (forall t t' ad v Tr, t --[EF_Alloc ad v Tr]--> t' -> value v)
    by (intros; induction_step; eauto).
  assert (forall t t' ad v Tr, t --[EF_Write ad v Tr]--> t' -> value v)
    by (intros; induction_step; eauto).
  intros. induction_multistep; trivial. auto_specialize.
  inversion_cstep; trivial. inversion_mstep; trivial;
  (eapply forall_array_add || eapply forall_array_set); eauto using value.
Qed.

Theorem valid_addresses_multistep_preservation : forall m m' ths ths' tc,
  forall_program m ths (valid_addresses m) ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_program m' ths' (valid_addresses m').
Proof.
  intros * [? ?] Hmultistep. induction Hmultistep; eauto.
  destruct IHHmultistep; eauto using valid_addresses_preservation.
Qed.

Theorem well_typed_multistep_preservation : forall m m' ths ths' tc,
  forall_program m ths (valid_addresses m) ->
  (* --- *)
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_program m' ths' well_typed_term /\
    forall_program m' ths' (consistently_typed_references m') /\
    m' extends m.
Proof.
  (* TODO *)
Admitted.

Theorem safe_spawns_multistep_preservation : forall m m' ths ths' tc,
  forall_program m ths well_typed_term ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths (consistently_typed_references m) ->
  (* --- *)
  forall_program m ths SafeSpawns ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_program m' ths' SafeSpawns.
Proof.
  intros * ? ? ? ? Hmultistep. induction Hmultistep; eauto.
  destruct IHHmultistep; eauto.
  eapply (safe_spawns_preservation m' m'' ths' ths''); eauto.
  eapply well_typed_multistep_preservation; eauto.
Qed.

Theorem safe_memory_sharing_multistep_preservation :
  forall m m' ths ths' tc,
    forall_memory m value ->
    forall_program m ths well_typed_term ->
    forall_program m ths (valid_addresses m) ->
    forall_program m ths (consistently_typed_references m) ->
    forall_program m ths SafeSpawns ->
    (* --- *)
    safe_memory_sharing m ths ->
    m / ths ~~[tc]~~>* m' / ths' ->
    safe_memory_sharing m' ths'.
Proof.
  intros * ? ? ? ? ? ? Hmultistep. induction Hmultistep; trivial.
  do 6 auto_specialize.
  eapply (safe_memory_sharing_preservation m' m'' ths' ths''); eauto.
  - eapply memory_value_multistep_preservation; eauto.
  - eapply well_typed_multistep_preservation; eauto.
  - eapply valid_addresses_multistep_preservation; eauto.
  - eapply well_typed_multistep_preservation; eauto.
  - eapply safe_spawns_multistep_preservation; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Local Lemma acc_from_mem : forall m t ad ad' v Tr,
  valid_accesses m t ->
  ~ access m t ad ->
  access m[ad' <- (v, Tr)] t ad ->
  access m t ad'.
Proof.
  intros * ? Hnacc Hacc. eapply nacc_iff in Hnacc.
  induction Hnacc; try inversion_vac; inversion_acc; try lia;
  try (destruct (acc_dec m t ad'); eauto using access);
  try (destruct (acc_dec m t1 ad'));
  try solve [
    exfalso; eapply (mem_set_nacc1 _ _ ad ad'); eauto using vac_nacc_length
  ];
  try (destruct (acc_dec m t2 ad'); eauto using access);
  try solve [
    exfalso; eapply (mem_set_nacc1 _ _ ad ad'); eauto using vac_nacc_length
  ].
  destruct (Nat.eq_dec ad ad'); subst; eauto using access. simpl_array.
  match goal with _ : ~ access _ _ ?ad |- _ => rename ad into ad'' end.
  eapply acc_mem; eauto. destruct (acc_dec m m[ad].tm ad'); trivial. exfalso.
  eapply (mem_set_nacc1 _ _ ad'' ad'); eauto using vac_nacc_length.
Qed.

Local Lemma cstep_nacc_preservation : forall m m' ths ths' tid tid' ad eff,
  ad < #m ->
  tid < #ths ->
  forall_threads ths well_typed_term ->
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
  inversion_mstep; eauto using vac_nacc_length, mem_add_nacc. intros ?.
  eapply (Hsms tid' tid); eauto using step_write_requires_uacc, acc_from_mem.
Qed.

Lemma monotonic_nondecreasing_memory_length: forall m m' ths ths' tc,
  m / ths ~~[tc]~~>* m' / ths' ->
  #m <= #m'.
Proof.
  assert (forall m m' eff t t',
    m / t ==[eff]==> m' / t' ->
    #m <= #m'). {
    intros. inversion_mstep; try lia.
    - rewrite add_increments_length. lia.
    - eauto using Nat.eq_le_incl, set_preserves_length.
  }
  intros. induction_multistep; trivial. inversion_cstep; eauto.
  eauto using Nat.le_trans.
Qed.

Lemma monotonic_nondecreasing_threads_length: forall m m' ths ths' tc,
  m / ths ~~[tc]~~>* m' / ths' ->
  #ths <= #ths'.
Proof.
  intros. induction_multistep; trivial. inversion_cstep;
  try rewrite add_increments_length; rewrite set_preserves_length;
  eauto using Nat.le_trans.
Qed.

Theorem not_access_multistep_preservation : forall m m' ths ths' tid ad tc,
  ad < #m ->
  tid < #ths ->
  forall_memory m value ->
  forall_program m ths well_typed_term ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths (consistently_typed_references m) ->
  forall_program m ths SafeSpawns ->
  safe_memory_sharing m ths ->
  (* --- *)
  ~ access m ths[tid] ad ->
  m / ths ~~[tc]~~>* m' / ths' ->
  ~ access m' ths'[tid] ad.
Proof.
  intros. induction H8; trivial. do 9 auto_specialize.
  eapply (cstep_nacc_preservation m' _ ths'); eauto.
  - eauto using monotonic_nondecreasing_memory_length, Nat.le_trans.
  - eauto using monotonic_nondecreasing_threads_length, Nat.le_trans.
  - eapply well_typed_multistep_preservation; eauto.
  - eapply forall_threads_vad_then_vac;
    eapply valid_addresses_multistep_preservation; eauto.
  - eapply safe_memory_sharing_multistep_preservation; eauto.
Qed.

