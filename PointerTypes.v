From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentInits.
From Elo Require Import ConsistentRefs.

Lemma ptyp_for_insert : forall m t1 t2 ad t T,
  consistent_inits m t1 ->
  (* --- *)
  t1 --[e_insert ad t T]--> t2 ->
  m[ad].T = T.
Proof.
  intros. ind_tstep; invc_ci; auto.
Qed.

Lemma ptyp_for_write : forall m t1 t2 ad t,
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  t1 --[e_write ad t]--> t2 ->
  exists T, m[ad].T = `w&T`.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_cr; eauto.
Qed.

Lemma ptyp_for_acq : forall m t1 t2 ad t,
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  t1 --[e_acq ad t]--> t2 ->
  exists T, m[ad].T = `x&T`.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_cr; eauto.
Qed.

Theorem ptyp_preservation : forall m1 m2 ths1 ths2 tid e ad,
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  ad < #m1 ->
  m1[ad].T = m2[ad].T.
Proof.
  intros. invc_cstep; trivial. invc_mstep; sigma; trivial; omicron; trivial.
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

(* preservation------------------------------------------------------------- *)

Theorem mpt_base :
  memory_pointer_types nil.
Proof.
  intros ** ? Hlt. inv Hlt.
Qed.

Theorem mpt_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 well_typed_term ->
  (* --- *)
  memory_pointer_types m1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  memory_pointer_types m2.
Proof.
  intros. invc_cstep; try invc_mstep; trivial;
  intros ? ?; omicron; eauto using wtt_alloc_type. lia.
Qed.

