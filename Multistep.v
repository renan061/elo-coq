From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import ValidAddresses.
From Elo Require Import References.
From Elo Require Import Soundness.
From Elo Require Import Access.
From Elo Require Import SafeSpawns.
From Elo Require Import SMS.

Theorem memory_value_multistep_preservation : forall m m' ths ths' tc,
  forall_memory m value ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_memory m' value.
Proof.
  assert (forall t t' ad v T, t --[EF_Alloc ad v T]--> t' -> value v);
  assert (forall t t' ad v T, t --[EF_Write ad v T]--> t' -> value v);
  try solve [intros; induction_step; eauto].
  intros. induction_multistep; trivial.
  inversion_cstep; eauto. inversion_mstep; eauto;
  (eapply forall_array_add || eapply forall_array_set);
  eauto using value; autounfold with fall in *; eauto.
Qed.

Local Ltac destruct_multistep_IH :=
  match goal with
  | IH : context C [_ -> forall_program _ _ _] |- _ =>
    destruct IH
  end.

Corollary valid_addresses_multistep_preservation : forall m m' ths ths' tc,
  forall_program m ths (valid_addresses m) ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_program m' ths' (valid_addresses m').
Proof.
  intros. induction_multistep; trivial.
  destruct_multistep_IH; eauto using valid_addresses_preservation.
Qed.

Theorem typing_multistep_preservation : forall m m' ths ths' tc,
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

Corollary safe_spawns_multistep_preservation : forall m m' ths ths' tc,
  forall_program m ths (valid_addresses m) ->
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  (* --- *)
  forall_program m ths SafeSpawns ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_program m' ths' SafeSpawns.
Proof.
  intros. induction_multistep; trivial.
  assert (forall_program m' ths' well_typed_term)
    by (eapply typing_multistep_preservation; eauto).
  destruct_multistep_IH; eauto using safe_spawns_preservation.
Qed.

Theorem safe_memory_sharing_multistep_preservation : forall m m' ths ths' tc,
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
  intros. induction_multistep; trivial.
  (* TODO *)
  eapply (safe_memory_sharing_preservation m' m'' ths' ths''); eauto;
  eauto using memory_value_multistep_preservation,
              valid_addresses_multistep_preservation,
              safe_spawns_multistep_preservation;
  eapply typing_multistep_preservation; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)


Lemma monotonic_nondecreasing_memory_length: forall m m' ths ths' tc,
  m / ths ~~[tc]~~>* m' / ths' ->
  #m <= #m'.
Proof.
  assert (forall m m' e t t',
    m / t ==[e]==> m' / t' ->
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
  forall_memory m value ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  forall_program m ths SafeSpawns ->
  safe_memory_sharing m ths ->
  (* --- *)
  ad < #m ->
  tid < #ths ->
  ~ access ad m ths[tid] ->
  m / ths ~~[tc]~~>* m' / ths' ->
  ~ access ad m' ths'[tid].
Proof.
  intros. induction_multistep; trivial.
  eapply (nacc_cstep_preservation m' _ ths');
  eauto using valid_addresses_multistep_preservation,
              safe_memory_sharing_multistep_preservation,
              monotonic_nondecreasing_memory_length,
              monotonic_nondecreasing_threads_length,
              Nat.le_trans.
  eapply typing_multistep_preservation; eauto.
Qed.

