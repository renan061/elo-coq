From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import ConsistentRegions.

(* ------------------------------------------------------------------------- *)
(* has-invariants                                                            *)
(* ------------------------------------------------------------------------- *)

Definition invariants m ths :=
  forall_memory  m      value              /\
  forall_program m ths (valid_term m)      /\
  no_uninitialized_references m ths        /\
  unique_initializers         m ths        /\
  unique_critical_regions     m ths        /\
  forall_program m ths well_typed_term     /\
  forall_program m ths (consistent_term m) /\
  memory_pointer_types m                   /\
  forall_program m ths safe_term           /\
  init_cr_exclusivity  ths                 /\
  forall_memory_consistent_regions  m      /\
  forall_threads_consistent_regions m ths   .

Theorem invariants_preservation_base : forall t,
  no_refs         t ->
  no_inits        t ->
  no_crs          t ->
  well_typed_term t ->
  invariants base_m (base_t t).
Proof.
  intros.
  split; eauto using forallmemory_base.
  split; eauto using vtm_preservation_base.
  split; eauto using nur_preservation_base.
  split; eauto using ui_preservation_base.
  split; eauto using ucr_preservation_base.
  split; eauto using wtt_preservation_base.
  split; eauto using ctm_preservation_base.
  split; eauto using mpt_preservation_base.
  split; eauto using stm_preservation_base.
  split; eauto using ice_preservation_base.
  split; eauto using mcreg_preservation_base.
         eauto using creg_preservation_base.
Qed.

Theorem invariants_preservation_ustep : forall m1 m2 ths1 ths2 tc,
  invariants m1 ths1 ->
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  invariants m2 ths2.
Proof.
  intros * H ?. ind_ustep; trivial.
  spec. unfold invariants in *. decompose record IHmultistep. clear IHmultistep.
  assert (forall_memory m3 value)
    by eauto using value_preservation_rstep.
  assert (forall_program m3 ths3 (valid_term m3))
    by eauto using vtm_preservation_rstep.
  assert (no_uninitialized_references m3 ths3)
    by eauto using nur_preservation_rstep.
  assert (unique_initializers m3 ths3)
    by eauto using ui_preservation_rstep.
  assert (unique_critical_regions m3 ths3)
    by eauto using ucr_preservation_rstep.
  assert (forall_program m3 ths3 well_typed_term)
    by eauto using wtt_preservation_rstep.
  assert (forall_program m3 ths3 (consistent_term m3))
    by eauto using ctm_preservation_rstep.
  assert (memory_pointer_types m3)
    by eauto using mpt_preservation_rstep.
  assert (forall_program m3 ths3 safe_term)
    by eauto using stm_preservation_rstep.
  assert (init_cr_exclusivity ths3)
    by eauto using ice_preservation_rstep.
  assert (forall_memory_consistent_regions m3)
    by eauto using mcreg_preservation_rstep.
  assert (forall_threads_consistent_regions m3 ths3)
    by eauto using creg_preservation_rstep.
  repeat (split; trivial).
Qed.






(*
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
*)
