From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

(* ------------------------------------------------------------------------- *)
(* invariants                                                                *)
(* ------------------------------------------------------------------------- *)

Definition invariants m ths :=
  forall_memory  m      value                     /\
  forall_program m ths  keywords                  /\
  forall_program m ths (valid_term m)             /\
  forall_program m ths (consistent_waits WR_none) /\
  no_uninitialized_references m ths               /\
  unique_initializers         m ths               /\
  unique_holding              m ths               /\
  forall_program m ths well_typed_term            /\
  forall_program m ths (consistent_term m)        /\
  memory_pointer_types m                          /\
  forall_program m ths safe_term                  /\
  init_cr_exclusivity  ths                        /\
  forall_memory_consistent_regions  m             /\
  forall_threads_consistent_regions m ths          .

Theorem invariants_preservation_base : forall t,
  no_refs t                  ->
  no_inits t                 ->
  no_crs t                   ->
  no_reacqs t                ->
  keywords t                 ->
  consistent_waits WR_none t ->
  well_typed_term t          ->
  invariants nil (base t).
Proof.
  intros.
  split; eauto using forallmemory_base.
  split; eauto using kw_preservation_base.
  split; eauto using vtm_preservation_base.
  split; eauto using cw_preservation_base.
  split; eauto using nur_preservation_base.
  split; eauto using ui_preservation_base.
  split; eauto using uhg_preservation_base.
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
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  invariants m2 ths2.
Proof.
  intros * H ?. ind_ustep; trivial.
  spec. unfold invariants in *. decompose record IHmultistep. clear IHmultistep.
  assert (forall_memory m3 value)
    by eauto using value_preservation_cstep.
  assert (forall_program m3 ths3 keywords)
    by eauto using kw_preservation_cstep.
  assert (forall_program m3 ths3 (valid_term m3))
    by eauto using vtm_preservation_cstep.
  assert (forall_program m3 ths3 (consistent_waits WR_none))
    by eauto using cw_preservation_cstep .
  assert (no_uninitialized_references m3 ths3)
    by eauto using nur_preservation_cstep.
  assert (unique_initializers m3 ths3)
    by eauto using ui_preservation_cstep.
  assert (unique_holding m3 ths3)
    by eauto using uhg_preservation_cstep.
  assert (forall_program m3 ths3 well_typed_term)
    by eauto using wtt_preservation_cstep.
  assert (forall_program m3 ths3 (consistent_term m3))
    by eauto using ctm_preservation_cstep.
  assert (memory_pointer_types m3)
    by eauto using mpt_preservation_cstep.
  assert (forall_program m3 ths3 safe_term)
    by eauto using stm_preservation_cstep.
  assert (init_cr_exclusivity ths3)
    by eauto using ice_preservation_cstep.
  assert (forall_memory_consistent_regions m3)
    by eauto using mcreg_preservation_cstep.
  assert (forall_threads_consistent_regions m3 ths3)
    by eauto using creg_preservation_cstep.
  repeat (split; trivial).
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Corollary des_forallprogram_memory : forall m ths P,
  forall_program m ths P -> forall_memory m P.
Proof. intros * [? ?]. assumption. Qed.

Corollary des_forallprogram_threads : forall m ths P,
  forall_program m ths P -> forall_threads ths P.
Proof. intros * [? ?]. assumption. Qed.

#[export] Hint Resolve
  des_forallprogram_memory
  des_forallprogram_threads
  : inva.

Ltac solve_inva_des :=
  unfold invariants; intros * H; decompose record H; trivial.

Corollary des_inva_value : forall m ths,
  invariants m ths -> forall_memory m value.
Proof. solve_inva_des. Qed.

Corollary des_inva_kw : forall m ths,
  invariants m ths -> forall_program m ths keywords.
Proof. solve_inva_des. Qed.

Corollary des_inva_vtm : forall m ths,
  invariants m ths -> forall_program m ths (valid_term m).
Proof. solve_inva_des. Qed.

Corollary des_inva_cw : forall m ths,
  invariants m ths -> forall_program m ths (consistent_waits WR_none).
Proof. solve_inva_des. Qed.

Corollary des_inva_nur : forall m ths,
  invariants m ths -> no_uninitialized_references m ths.
Proof. solve_inva_des. Qed.

Corollary des_inva_ui : forall m ths,
  invariants m ths -> unique_initializers m ths.
Proof. solve_inva_des. Qed.

Corollary des_inva_mu : forall m ths,
  invariants m ths -> unique_holding m ths.
Proof. solve_inva_des. Qed.

Corollary des_inva_wtt : forall m ths,
  invariants m ths -> forall_program m ths well_typed_term.
Proof. solve_inva_des. Qed.

Corollary des_inva_ctm : forall m ths,
  invariants m ths -> forall_program m ths (consistent_term m).
Proof. solve_inva_des. Qed.

Corollary des_inva_mpt : forall m ths,
  invariants m ths -> memory_pointer_types m.
Proof. solve_inva_des. Qed.

Corollary des_inva_stm : forall m ths,
  invariants m ths -> forall_program m ths safe_term.
Proof. solve_inva_des. Qed.

Corollary des_inva_ice : forall m ths,
  invariants m ths -> init_cr_exclusivity ths.
Proof. solve_inva_des. Qed.

Corollary des_inva_tice : forall m ths,
  invariants m ths -> forall_threads ths term_init_cr_exc.
Proof. solve_inva_des. eauto using tice_from_ice with inva. Qed.

Corollary des_inva_mcreg : forall m ths,
  invariants m ths -> forall_memory_consistent_regions m.
Proof. solve_inva_des. Qed.

Corollary des_inva_creg : forall m ths,
  invariants m ths -> forall_threads_consistent_regions m ths.
Proof. solve_inva_des. Qed.

#[export] Hint Resolve
  des_forallprogram_memory
  des_forallprogram_threads
  des_inva_value
  des_inva_kw
  des_inva_vtm
  des_inva_cw
  des_inva_nur
  des_inva_ui
  des_inva_mu
  des_inva_wtt
  des_inva_ctm
  des_inva_mpt
  des_inva_stm
  des_inva_ice
  des_inva_tice
  des_inva_mcreg
  des_inva_creg
  : inva.

