From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentTerm.

Theorem cstep_nondecreasing_memory_size : forall m1 m2 ths1 ths2 tid e ad,
  ad < #m1 ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  ad < #m2.
Proof.
  intros. invc_cstep; try invc_mstep; trivial; sigma; lia.
Qed.

Theorem ustep_nondecreasing_memory_size : forall m1 m2 ths1 ths2 tc ad,
  ad < #m1 ->
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  ad < #m2.
Proof.
  intros. ind_ustep; eauto using cstep_nondecreasing_memory_size.
Qed.

(* ------------------------------------------------------------------------- *)

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
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  ad < #m1 ->
  m1[ad].T = m2[ad].T.
Proof.
  intros. invc_cstep; try invc_mstep; sigma; trivial; omicron; trivial.
Qed.

Theorem ptyp_preservation_ustep : forall m1 m2 ths1 ths2 tc ad,
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  ad < #m1 ->
  m1[ad].T = m2[ad].T.
Proof.
  intros. ind_ustep; trivial. rewrite IHmultistep;
  eauto using ustep_nondecreasing_memory_size, ptyp_preservation_cstep.
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
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  memory_pointer_types m2.
Proof.
  intros. invc_cstep; try invc_mstep; trivial;
  intros ? ?; omicron; eauto using wtt_alloc_type. lia.
Qed.

Theorem mpt_preservation_base :
  memory_pointer_types nil.
Proof.
  intros ? H. destruct ad; invc H.
Qed.

