From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentTerm.

Theorem rstep_nondecreasing_memory_size : forall m1 m2 ths1 ths2 tid e ad,
  ad < #m1 ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  ad < #m2.
Proof.
  intros. invc_ostep; invc_cstep; try invc_mstep; trivial; sigma; lia.
Qed.

Theorem ustep_nondecreasing_memory_size : forall m1 m2 ths1 ths2 tc ad,
  ad < #m1 ->
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  ad < #m2.
Proof.
  intros. ind_ustep; eauto using rstep_nondecreasing_memory_size.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ptyp_for_insert : forall m t1 t2 ad t T,
  consistent_term m t1 ->
  (* --- *)
  t1 --[e_insert ad t T]--> t2 ->
  m[ad].T = T.
Proof.
  intros. ind_tstep; invc_ctm; auto.
Qed.

Lemma ptyp_for_write : forall m t1 t2 ad t,
  well_typed_term t1 ->
  consistent_term m t1 ->
  (* --- *)
  t1 --[e_write ad t]--> t2 ->
  exists T, m[ad].T = `w&T`.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_ctm; eauto.
Qed.

Lemma ptyp_for_acq : forall m t1 t2 ad t,
  well_typed_term t1 ->
  consistent_term m t1 ->
  (* --- *)
  t1 --[e_acq ad t]--> t2 ->
  exists T, m[ad].T = `x&T`.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_ctm; eauto.
Qed.

Theorem ptyp_preservation_cstep : forall m1 m2 ths1 ths2 tid e ad,
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  ad < #m1 ->
  m1[ad].T = m2[ad].T.
Proof.
  intros. invc_cstep; trivial. invc_mstep; sigma; trivial; omicron; trivial.
Qed.

Theorem ptyp_preservation_rstep : forall m1 m2 ths1 ths2 tid e ad,
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  ad < #m1 ->
  m1[ad].T = m2[ad].T.
Proof.
  intros. invc_ostep; eauto using ptyp_preservation_cstep.
  repeat omicron; upsilon; eauto using ptyp_preservation_cstep.
  invc_cstep. invc_mstep. sigma. reflexivity.
Qed.

Theorem ptyp_preservation_ustep : forall m1 m2 ths1 ths2 tc ad,
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  ad < #m1 ->
  m1[ad].T = m2[ad].T.
Proof.
  intros. ind_ustep; trivial. rewrite IHmultistep;
  eauto using ustep_nondecreasing_memory_size, ptyp_preservation_rstep.
Qed.

(* ------------------------------------------------------------------------- *)
(* memory-pointer-types                                                      *)
(* ------------------------------------------------------------------------- *)

Definition memory_pointer_types (m : mem) := forall ad,
  ad < #m -> (exists T, m[ad].T = `r&T`) \/
             (exists T, m[ad].T = `x&T`) \/
             (exists T, m[ad].T = `w&T`). 

(* tactics ----------------------------------------------------------------- *)

Ltac destruct_mpt ad :=
  match goal with
  | H   : memory_pointer_types ?m
  , Hlt : ad < # ?m
  |- _ =>
    specialize (H ad Hlt) as [[?T ?HptypR] | [[?T ?HptypX] | [?T ?HptypW]]]
  end.

(* preservation ------------------------------------------------------------ *)

Theorem mpt_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 well_typed_term ->
  (* --- *)
  memory_pointer_types m1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  memory_pointer_types m2.
Proof.
  intros. invc_cstep; try invc_mstep; trivial;
  intros ? ?; omicron; eauto using wtt_alloc_type. lia.
Qed.

Theorem mpt_preservation_rstep : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  (* --- *)
  memory_pointer_types m1 ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  memory_pointer_types m2.
Proof.
  intros * [_ ?] **. invc_ostep; eauto using mpt_preservation_cstep.
  match goal with _ : _ / _ ~~[_, _]~~> ?m / ?ths |- _ =>
    assert (memory_pointer_types m) by eauto using mpt_preservation_cstep
  end.
  repeat intro. omicron; upsilon; auto.
Qed.

Theorem mpt_preservation_base :
  memory_pointer_types base_m.
Proof.
  unfold base_m. intros ? H. destruct ad; invc H.
Qed.

