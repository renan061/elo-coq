From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

From Elo Require Import PropertiesVAD.
From Elo Require Import PropertiesACC.
From Elo Require Import PropertiesSS.
From Elo Require Import PropertiesSMS.

From Elo Require Import Soundness.

(* ------------------------------------------------------------------------- *)
(* multistep monotonic-nondecreasing                                         *)
(* ------------------------------------------------------------------------- *)

Lemma monotonic_nondecreasing_memory_length: forall m m' ths ths' tc,
  m / ths ~~[tc]~~>* m' / ths' ->
  #m <= #m'.
Proof.
  assert (forall m m' e t t',
    m / t ==[e]==> m' / t' ->
    #m <= #m'). {
    intros. inv_mstep; eauto.
    - rewrite add_increments_length. eauto.
    - rewrite set_preserves_length. eauto.
  }
  intros. induction_multistep; trivial. inv_cstep; eauto.
  eauto using Nat.le_trans.
Qed.

Lemma monotonic_nondecreasing_threads_length: forall m m' ths ths' tc,
  m / ths ~~[tc]~~>* m' / ths' ->
  #ths <= #ths'.
Proof.
  intros. induction_multistep; trivial. inv_cstep;
  try rewrite add_increments_length; rewrite set_preserves_length;
  eauto using Nat.le_trans.
Qed.

(* ------------------------------------------------------------------------- *)
(* multistep preservation                                                    *)
(* ------------------------------------------------------------------------- *)

Theorem memory_value_multistep_preservation : forall m m' ths ths' tc,
  forall_memory m value ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_memory m' value.
Proof.
  assert (forall t t' ad v T, t --[EF_Alloc ad v T]--> t' -> value v);
  assert (forall t t' ad v T, t --[EF_Write ad v T]--> t' -> value v);
  try solve [intros; induction_tstep; eauto].
  intros. induction_multistep; trivial.
  inv_cstep; eauto. inv_mstep; eauto;
  (eapply forall_array_add || eapply forall_array_set);
  eauto using value; autounfold with fall in *; eauto.
Qed.

Local Ltac destruct_for_multistep :=
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
  destruct_for_multistep; eauto using valid_addresses_preservation.
Qed.

Theorem typing_multistep_preservation : forall m m' ths ths' tc,
  forall_program m ths (valid_addresses m) ->
  (* --- *)
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_program m' ths' well_typed_term /\
    forall_program m' ths' (consistently_typed_references m')
    (* /\ m' extends m *).
Proof.
  (* TODO *)
Admitted.

Corollary memory_type_multistep_preservation : forall m m' ths ths' ad tc,
  forall_program m ths (valid_addresses m) ->
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  (* --- *)
  m / ths ~~[tc]~~>* m' / ths' ->
  ad < #m ->
  m'[ad].typ = m[ad].typ.
Proof.
  intros. induction_multistep; trivial.
  assert (forall_threads ths' (consistently_typed_references m'))
    by (eapply typing_multistep_preservation; eauto).
  rewrite <- IHmultistep; eauto.
  eapply memtyp_preservation; eauto.
  assert (#m <= #m') by eauto using monotonic_nondecreasing_memory_length. lia.
Qed.

Corollary safe_spawns_multistep_preservation : forall m m' ths ths' tc,
  forall_program m ths (valid_addresses m) ->
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  (* --- *)
  forall_program m ths safe_spawns ->
  m / ths ~~[tc]~~>* m' / ths' ->
  forall_program m' ths' safe_spawns.
Proof.
  intros. induction_multistep; trivial.
  assert (forall_program m' ths' well_typed_term)
    by (eapply typing_multistep_preservation; eauto).
  destruct_for_multistep; eauto using safe_spawns_preservation.
Qed.

Corollary safe_memory_sharing_multistep_preservation : forall m m' ths ths' tc,
  forall_memory m value ->
  forall_program m ths well_typed_term ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths (consistently_typed_references m) ->
  forall_program m ths safe_spawns ->
  (* --- *)
  safe_memory_sharing m ths ->
  m / ths ~~[tc]~~>* m' / ths' ->
  safe_memory_sharing m' ths'.
Proof.
  intros. induction_multistep; trivial.
  eapply (safe_memory_sharing_preservation m' m'' ths' ths'');
  eauto using memory_value_multistep_preservation,
              valid_addresses_multistep_preservation,
              safe_spawns_multistep_preservation;
  eapply typing_multistep_preservation; eauto.
Qed.

Theorem not_access_multistep_preservation : forall m m' ths ths' tid ad tc,
  forall_memory m value ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  forall_program m ths safe_spawns ->
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
  (* TODO *)
  - eapply valid_addresses_multistep_preservation; eauto.
  - eapply valid_addresses_multistep_preservation; eauto.
  - eapply typing_multistep_preservation; eauto.
Qed.

Definition valid_program m ths :=
  (  forall_memory  m value
  /\ forall_program m ths well_typed_term
  /\ forall_program m ths (valid_addresses m)
  /\ forall_program m ths (consistently_typed_references m)
  /\ forall_program m ths safe_spawns
  /\ safe_memory_sharing m ths).

Corollary properties_preservation : forall m m' ths ths' tc,
  valid_program m ths ->
  m / ths ~~[tc]~~>* m' / ths' ->
  valid_program m' ths'.
Proof.
  unfold valid_program.
  intros * Hvp **. decompose record Hvp. split.
  eapply memory_value_multistep_preservation; eauto. split.
  eapply typing_multistep_preservation; eauto. split.
  eapply valid_addresses_multistep_preservation; eauto. split.
  eapply typing_multistep_preservation; eauto. split.
  eapply safe_spawns_multistep_preservation; eauto.
  eapply safe_memory_sharing_multistep_preservation; eauto.
Qed.

