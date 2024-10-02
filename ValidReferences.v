From Elo Require Import Core.

From Elo Require Import Preservation_.
From Elo Require Import WellTypedTerm.
From Elo Require Import ValidPointerTypes.
From Elo Require Import ValidAddresses.

(* ------------------------------------------------------------------------- *)
(* valid_references                                                          *)
(* ------------------------------------------------------------------------- *)

Inductive valid_references (m : mem) : tm -> Prop :=
  | vr_unit :
    valid_references m <{unit}> 

  | vr_nat : forall n,
    valid_references m <{nat n}>

  | vr_var : forall x,
    valid_references m <{var x}>

  | vr_fun : forall x Tx t,
    valid_references m t ->
    valid_references m <{fn x Tx t}>

  | vr_call : forall t1 t2,
    valid_references m t1 ->
    valid_references m t2 ->
    valid_references m <{call t1 t2}> 

  | vr_refR : forall T ad,
    m[ad].T = `r&T` ->
    valid_references m <{&ad : r&T}>

  | vr_refX : forall T ad,
    m[ad].T = `x&T` ->
    valid_references m <{&ad : x&T}>

  | vr_refW : forall T ad,
    m[ad].T = `w&T` ->
    valid_references m <{&ad : w&T}>

  | vr_new : forall T t,
    valid_references m t ->
    valid_references m <{new t : T}> 

  | vr_load : forall t,
    valid_references m t ->
    valid_references m <{*t}> 

  | vr_asg : forall t1 t2,
    valid_references m t1 ->
    valid_references m t2 ->
    valid_references m <{t1 := t2}> 

  | vr_acq : forall t1 t2,
    valid_references m t1 ->
    valid_references m t2 ->
    valid_references m <{acq t1 t2}>

  | vr_cr : forall ad t,
    valid_references m t ->
    valid_references m <{cr ad t}>

  | vr_spawn : forall t,
    valid_references m t ->
    valid_references m <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* tactics                                                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac _vr tt :=
  match goal with
  (* irrelevant for unit, nat, and var *)
  | H : valid_references _ <{fn _ _ _ }> |- _ => tt H
  | H : valid_references _ <{call _ _ }> |- _ => tt H
  | H : valid_references _ <{& _ : _  }> |- _ => tt H
  | H : valid_references _ <{new _ : _}> |- _ => tt H
  | H : valid_references _ <{* _      }> |- _ => tt H
  | H : valid_references _ <{_ := _   }> |- _ => tt H
  | H : valid_references _ <{acq _ _  }> |- _ => tt H
  | H : valid_references _ <{cr _ _   }> |- _ => tt H
  | H : valid_references _ <{spawn _  }> |- _ => tt H
  end.

Ltac inv_vr  := _vr inv.
Ltac invc_vr := _vr invc.

(* ------------------------------------------------------------------------- *)
(* auxiliary lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

Local Lemma vr_tstep_alloc_term : forall m t1 t2 ad t T,
  valid_references m t1 ->
  t1 --[e_alloc ad t T ]--> t2 ->
  valid_references m t.
Proof.
  intros. ind_tstep; inv_vr; eauto using valid_references.
Qed.

Local Lemma vr_tstep_write_term : forall m t1 t2 ad t T,
  valid_references m t1 ->
  t1 --[e_write ad t T ]--> t2 ->
  valid_references m t.
Proof.
  intros. ind_tstep; inv_vr; eauto.
Qed.

Local Lemma vr_write_effect : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  t1 --[e_write ad t T]--> t2 ->
  T = m[ad].T.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  ind_tstep; intros; invc_typeof; invc_vr; eauto.
  invc_typeof. invc_vr. eauto.
Qed.

(*
Local Lemma vr_rel_effect : forall m t1 t2 otid ad,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  t1 --[e_rel otid ad]--> t2 ->
  exists T, empty |-- m[ad].tm is `x&T`
         /\ m[ad].ty = `x&T`.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  ind_tstep; intros; invc_typeof; invc_vr; eauto.
  repeat clean. eexists.
Abort.
*)

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma vr_subst : forall m t tx x,
  valid_references m tx ->
  valid_references m t ->
  valid_references m <{[x := tx] t}>.
Proof.
  intros.
  induction t; try inv_vr; eauto using valid_references;
  simpl; destruct str_eq_dec; eauto using valid_references.
Qed.

Lemma vr_mem_add : forall m t tT,
  valid_addresses m t ->
  (* --- *)
  valid_references m t ->
  valid_references (m +++ tT) t.
Proof.
  intros.
  induction t; eauto using valid_references;
  inv_vad; inv_vr; eauto using valid_references;
  (eapply vr_refR || eapply vr_refX || eapply vr_refW);
  sigma; assumption.
Qed.

Lemma vr_mem_setW : forall m t ad te Te,
  ad < #m ->
  Te = m[ad].T ->
  (* --- *)
  valid_references m t ->
  valid_references m[ad.tT <- te Te] t.
Proof.
  intros.
  induction t; try invc_vr; eauto using valid_references;
  (eapply vr_refR || eapply vr_refX || eapply vr_refW);
  omicron; eauto.
Qed.

Lemma vr_mem_setX : forall m t ad X,
  ad < #m ->
  (* --- *)
  valid_references m t ->
  valid_references m[ad.X <- X] t.
Proof.
  intros.
  induction t; try invc_vr; eauto using valid_references;
  (eapply vr_refR || eapply vr_refX || eapply vr_refW);
  omicron; eauto.
Qed.

(* none -------------------------------------------------------------------- *)

Lemma vr_preservation_none : forall m t1 t2,
  valid_references m t1 ->
  t1 --[e_none]--> t2 ->
  valid_references m t2.
Proof.
  intros.
  ind_tstep; inv_vr; eauto using valid_references.
  inv_vr. eauto using vr_subst.
Qed.

(* alloc ------------------------------------------------------------------- *)

Lemma vr_preservation_mem_alloc : forall m t1 t2 t T X,
  well_typed_term t1 ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t1 ->
  valid_references m t1 ->
  (* --- *)
  forall_memory m (valid_references m) ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  forall_memory (m +++ (t, T, X)) (valid_references (m +++ (t, T, X))).
Proof.
  intros ** ad. omicron;
  eauto using vr_mem_add, valid_references; (* optimization *)
  eauto using vr_mem_add, vr_tstep_alloc_term.
Qed.

Lemma vr_preservation_alloc : forall m t1 t2 t T X,
  well_typed_term t1 ->
  valid_addresses m t1 ->
  (* --- *)
  valid_references m t1 ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  valid_references (m +++ (t, T, X)) t2.
Proof.
  intros * [T ?] **. generalize dependent T.
  ind_tstep; intros; inv_vr; inv_typeof; inv_vad;
  eauto using vr_mem_add, valid_references;
  (eapply vr_refR || eapply vr_refX || eapply vr_refW);
  sigma; eauto using type_of, empty_eq_safe_empty.
Qed.

Lemma vr_preservation_unt_alloc : forall m t1 t2 tu ad t T X,
  valid_addresses m tu ->
  (* --- *)
  valid_references m tu ->
  t1 --[e_alloc ad t T]--> t2 ->
  valid_references (m +++ (t, T, X)) tu.
Proof.
  intros.
  ind_tstep; eauto using vr_mem_add, valid_references.
Qed.

(* read -------------------------------------------------------------------- *)

Lemma vr_preservation_read : forall m t1 t2 ad,
  valid_references m m[ad].t ->
  (* --- *)
  valid_references m t1 ->
  t1 --[e_read ad m[ad].t]--> t2 ->
  valid_references m t2.
Proof.
  intros.
  ind_tstep; inv_vr; eauto using valid_references.
Qed.

(* write ------------------------------------------------------------------- *)

Lemma vr_preservation_mem_write : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (valid_references m) ->
  t1 --[e_write ad t T]--> t2 ->
  forall_memory m[ad.tT <- t T] (valid_references m[ad.tT <- t T]).
Proof.
  intros ** ?.
  omicron; eauto using vr_mem_setW, vr_tstep_write_term, vr_write_effect.
Qed.

Lemma vr_preservation_write : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  (* --- *)
  ad < #m ->
  valid_references m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  valid_references (m[ad.tT <- t T]) t2.
Proof.
  intros.
  ind_tstep; invc_wtt; invc_vr;
  eauto using vr_mem_setW, vr_write_effect, valid_references.
Qed.

Lemma vr_preservation_unt_write : forall m t1 t2 tu ad t T,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  valid_references m tu ->
  t1 --[e_write ad t T]--> t2 ->
  valid_references m[ad.tT <- t T] tu.
Proof.
  intros.
  eauto using vr_mem_setW, vr_write_effect.
Qed.

(* acq --------------------------------------------------------------------- *)

Lemma vr_preservation_mem_acq : forall m t1 t2 tid ad t X,
  forall_memory m well_typed_term ->
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (valid_references m) ->
  t1 --[e_acq tid ad t]--> t2 ->
  forall_memory m[ad.X <- X] (valid_references m[ad.X <- X]).
Proof.
  intros ** ?. omicron; eauto using vr_mem_setX.
Qed.

Lemma vr_preservation_acq : forall m t1 t2 tid ad X,
  forall_memory m (valid_references m) ->
  (* --- *)
  ad < #m ->
  valid_references m t1 ->
  t1 --[e_acq tid ad m[ad].t]--> t2 ->
  valid_references m[ad.X <- X] t2.
Proof.
  intros.
  ind_tstep; invc_vr; eauto using vr_mem_setX, valid_references.
  repeat invc_vr; eauto using vr_subst, vr_mem_setX, valid_references.
Qed.

Lemma vr_preservation_unt_acq : forall m t1 t2 tu tid ad t X,
  ad < #m ->
  valid_references m tu ->
  t1 --[e_acq tid ad t]--> t2 ->
  valid_references m[ad.X <- X] tu.
Proof.
  eauto using vr_mem_setX.
Qed.

(* rel --------------------------------------------------------------------- *)

Lemma vr_preservation_mem_rel : forall m t1 t2 tid ad X,
  forall_memory m well_typed_term ->
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (valid_references m) ->
  t1 --[e_rel tid ad]--> t2 ->
  forall_memory m[ad.X <- X] (valid_references m[ad.X <- X]).
Proof.
  intros ** ?. omicron; eauto using vr_mem_setX.
Qed.

Lemma vr_preservation_rel : forall m t1 t2 tid ad X,
  ad < #m ->
  valid_references m t1 ->
  t1 --[e_rel tid ad]--> t2 ->
  valid_references m[ad.X <- X] t2.
Proof.
  intros.
  ind_tstep; invc_vr; eauto using vr_mem_setX, valid_references.
Qed.

Lemma vr_preservation_unt_rel : forall m t1 t2 tu tid ad X,
  ad < #m ->
  valid_references m tu ->
  t1 --[e_rel tid ad]--> t2 ->
  valid_references m[ad.X <- X] tu.
Proof.
  eauto using vr_mem_setX.
Qed.

(* spawn ------------------------------------------------------------------- *)

Lemma vr_preservation_spawn : forall m t1 t2 tid t,
  valid_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_references m t2.
Proof.
  intros. ind_tstep; inv_vr; eauto using valid_references.
Qed.

Lemma vr_preservation_spawned : forall m t1 t2 tid t,
  valid_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_references m t.
Proof.
  intros. ind_tstep; inv_vr; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem vr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  forall_program m1 ths1 (valid_addresses m1) ->
  (* --- *)
  forall_program m1 ths1 (valid_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (valid_references m2).
Proof.
  split_preservation.
  - eauto using vr_preservation_none.
  - eauto using vr_preservation_mem_alloc.
  - eauto using vr_preservation_alloc.
  - eauto using vr_preservation_unt_alloc.
  - eauto using vr_preservation_read.
  - eauto using vr_preservation_mem_write.
  - eauto using vr_preservation_write.
  - eauto using vr_preservation_unt_write.
  - eauto using vr_preservation_mem_acq.
  - eauto using vr_preservation_acq.
  - eauto using vr_preservation_unt_acq.
  - eauto using vr_preservation_mem_rel.
  - eauto using vr_preservation_rel.
  - eauto using vr_preservation_unt_rel.
  - eauto using vr_preservation_spawn.
  - eauto using vr_preservation_spawned.
  - eauto using valid_references.
Qed.

(* ------------------------------------------------------------------------- *)

Corollary vr_cstep_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   well_typed_term ->
  forall_threads ths1 well_typed_term ->
  forall_memory  m1   (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  (* --- *)
  forall_memory m1 (valid_references m1) ->
  forall_threads ths1 (valid_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (valid_references m2).
Proof.
  intros.
  assert (forall_program m2 ths2 (valid_references m2))
    by (eapply vr_preservation; eauto).
  destruct_forall_program. assumption.
Qed.

