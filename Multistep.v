From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Core.
From Elo Require Import Properties.
From Elo Require Import PtrTyp.
From Elo Require Import Preservation.
From Elo Require Import Soundness.

(* ------------------------------------------------------------------------- *)
(* monotonic-nondecreasing memory                                            *)
(* ------------------------------------------------------------------------- *)

Lemma cstep_nondecreasing_memory_length : forall m m' ths ths' tid e,
  m / ths ~~[tid, e]~~> m' / ths' ->
  #m <= #m'.
Proof.
  intros. inv_cstep; trivial. inv_mstep; trivial.
  - rewrite add_increments_length. lia. 
  - rewrite set_preserves_length. lia. 
Qed.

Lemma multistep_nondecreasing_memory_length: forall m m' ths ths' tc,
  m / ths ~~[tc]~~>* m' / ths' ->
  #m <= #m'.
Proof.
  intros. induction_mulst; trivial.
  assert (#m' <= #m'')
    by eauto using cstep_nondecreasing_memory_length.
  lia.
Qed.

Lemma monotonic_nondecreasing_threads_length: forall m m' ths ths' tc,
  m / ths ~~[tc]~~>* m' / ths' ->
  #ths <= #ths'.
Proof.
  intros. induction_mulst; trivial. inv_cstep;
  try rewrite add_increments_length; rewrite set_preserves_length;
  eauto using Nat.le_trans.
Qed.

(* ------------------------------------------------------------------------- *)
(* valid-program                                                             *)
(* ------------------------------------------------------------------------- *)

Definition valid_program m ths :=
  (  forall_memory  m value
  /\ forall_program m ths well_typed_term
  /\ forall_program m ths (valid_addresses m)
  /\ forall_program m ths (consistently_typed_references m)
  /\ forall_program m ths safe_spawns
  /\ safe_memory_sharing m ths).

Local Corollary vp_cstep_preservation : forall m m' ths ths' tid e,
  valid_program m ths ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  valid_program m' ths'.
Proof.
  intros * Hvp **. unfold valid_program in Hvp.
  decompose record Hvp. splits 6;
  eauto using value_preservation ,
              wtt_preservation,
              vad_preservation,
              ctr_preservation,
              ss_preservation,
              sms_preservation.
Qed.

Local Corollary vp_multistep_preservation : forall m m' ths ths' tc,
  valid_program m ths ->
  m / ths ~~[tc]~~>* m' / ths' ->
  valid_program m' ths'.
Proof.
  intros. induction_mulst; eauto using vp_cstep_preservation .
Qed.

Corollary vp_preservation : forall m m' ths ths',
  valid_program m ths ->
  (
    (exists tid e, m / ths ~~[tid, e]~~> m' / ths') \/ 
    (exists tc, m / ths ~~[tc]~~>* m' / ths')
  ) ->
  valid_program m' ths'.
Proof.
  intros * ? [[? [? ?]] | [? ?]];
  eauto using vp_multistep_preservation.
  eapply vp_cstep_preservation; eauto. 
Qed.

(* ------------------------------------------------------------------------- *)
(* valid-program destruction                                                 *)
(* ------------------------------------------------------------------------- *)

Ltac solve_vp_destruction :=
  unfold valid_program; unfold forall_program;
  intros * Hvp **; decompose [and or] Hvp; trivial.

Corollary des_vp_mval : forall m ths,
  valid_program m ths -> forall_memory m value.
Proof. solve_vp_destruction. Qed.

Corollary des_vp_mwtt : forall m ths,
  valid_program m ths -> forall_memory m well_typed_term.
Proof. solve_vp_destruction. Qed.

Corollary des_vp_wtt : forall m ths,
  valid_program m ths -> forall_threads ths well_typed_term.
Proof. solve_vp_destruction. Qed.

Corollary des_vp_mvad : forall m ths,
  valid_program m ths -> forall_memory m (valid_addresses m).
Proof. solve_vp_destruction. Qed.

Corollary des_vp_vad : forall m ths,
  valid_program m ths -> forall_threads ths (valid_addresses m).
Proof. solve_vp_destruction. Qed.

Corollary des_vp_mctr : forall m ths,
  valid_program m ths -> forall_memory m (consistently_typed_references m).
Proof. solve_vp_destruction. Qed.

Corollary des_vp_ctr1 : forall m ths,
  valid_program m ths -> forall_threads ths (consistently_typed_references m).
Proof. solve_vp_destruction. Qed.

Corollary des_vp_ctr2 : forall m ths,
  valid_program m ths -> forall tid, consistently_typed_references m ths[tid].
Proof. solve_vp_destruction. Qed.

Corollary des_vp_mss : forall m ths,
  valid_program m ths -> forall_memory m safe_spawns.
Proof. solve_vp_destruction. Qed.

Corollary des_vp_ss : forall m ths,
  valid_program m ths -> forall_threads ths safe_spawns.
Proof. solve_vp_destruction. Qed.

Corollary des_vp_sms : forall m ths,
  valid_program m ths -> safe_memory_sharing m ths.
Proof. solve_vp_destruction. Qed.

#[export] Hint Resolve
  des_vp_mval
  des_vp_mwtt des_vp_wtt
  des_vp_mvad des_vp_vad
  des_vp_mctr des_vp_ctr1 des_vp_ctr2
  des_vp_mss  des_vp_ss 
  des_vp_sms
  : vp.

Corollary memtyp_multistep_preservation : forall m m' ths ths' ad tc,
  valid_program m ths ->
  (* --- *)
  ad < #m ->
  m / ths ~~[tc]~~>* m' / ths' ->
  m[ad].typ = m'[ad].typ.
Proof.
  intros. induction_mulst; trivial.
  rewrite IHmultistep; eauto.
  eapply ptyp_cstep_preservation; eauto using vp_multistep_preservation with vp.
  assert (#m <= #m') by eauto using multistep_nondecreasing_memory_length.
  lia.
Qed.

Corollary memtyp_preservation : forall m m' ths ths' ad,
  valid_program m ths ->
  (* --- *)
  ad < #m ->
  (
    (exists tid e, m / ths ~~[tid, e]~~> m' / ths') \/ 
    (exists tc, m / ths ~~[tc]~~>* m' / ths')
  ) ->
  m[ad].typ = m'[ad].typ.
Proof.
  intros * ? ? [[? [? ?]] | [? ?]];
  eauto using memtyp_multistep_preservation.
  eapply ptyp_cstep_preservation; eauto with vp. 
Qed.

