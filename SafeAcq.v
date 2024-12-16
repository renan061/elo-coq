From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentRefs.

(* ------------------------------------------------------------------------- *)
(* safe-acq                                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive safe_acq : tm -> Prop :=
  | sacq_unit  :                 safe_acq <{unit         }>
  | sacq_nat   : forall n,       safe_acq <{nat n        }>
  | sacq_var   : forall x,       safe_acq <{var x        }>
  | sacq_fun   : forall x Tx t,  safe_acq t  ->
                                 safe_acq <{fn x Tx t    }>
  | sacq_call  : forall t1 t2,   safe_acq t1 ->
                                 safe_acq t2 ->
                                 safe_acq <{call t1 t2   }>
  | sacq_ref   : forall ad T,    safe_acq <{&ad : T      }>
  | sacq_new   : forall t T,     safe_acq t  ->
                                 safe_acq <{new t : T    }>
  | sacq_init  : forall ad t T,  safe_acq t  ->
                                 safe_acq <{init ad t : T}>
  | sacq_load  : forall t,       safe_acq t  ->
                                 safe_acq <{*t           }>
  | sacq_asg   : forall t1 t2,   safe_acq t1 ->
                                 safe_acq t2 ->
                                 safe_acq <{t1 := t2     }>
  | sacq_acq   : forall t1 x t2, safe_acq t1 ->
                                 no_wrefs t2 ->
                                 safe_acq <{acq t1 x t2  }>
  | sacq_cr    : forall ad t,    safe_acq t  ->
                                 safe_acq <{cr ad t      }>
  | sacq_spawn : forall t,       safe_acq t  ->
                                 safe_acq <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _sacq tt :=
  match goal with
  | H : safe_acq <{unit        }>   |- _ => clear H
  | H : safe_acq <{nat _       }>   |- _ => clear H
  | H : safe_acq <{var _       }>   |- _ => clear H
  | H : safe_acq <{fn _ _ _    }>   |- _ => tt H
  | H : safe_acq <{call _ _    }>   |- _ => tt H
  | H : safe_acq <{& _ : _     }>   |- _ => clear H
  | H : safe_acq <{new _ : _   }>   |- _ => tt H
  | H : safe_acq <{init _ _ : _}>   |- _ => tt H
  | H : safe_acq <{* _         }>   |- _ => tt H
  | H : safe_acq <{_ := _      }>   |- _ => tt H
  | H : safe_acq <{acq _ _ _   }>   |- _ => tt H
  | H : safe_acq <{cr _ _      }>   |- _ => tt H
  | H : safe_acq <{spawn _     }>   |- _ => tt H
  end.

Ltac inv_sacq  := _sacq inv.
Ltac invc_sacq := _sacq invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma sacq_from_nowrefs : forall t,
  no_wrefs t ->
  safe_acq t.
Proof.
  intros. induction t; invc_nowrefs; auto using safe_acq.
Qed.

Lemma sacq_insert_term : forall t1 t2 ad t T,
  safe_acq t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  safe_acq t.
Proof.
  intros. ind_tstep; invc_sacq; auto using safe_acq.
Qed.

Lemma sacq_write_term : forall t1 t2 ad t,
  safe_acq t1 ->
  t1 --[e_write ad t]--> t2 ->
  safe_acq t.
Proof.
  intros. ind_tstep; invc_sacq; auto using safe_acq.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma sacq_subst : forall Gamma x tx t Tx T,
  value tx ->
  empty |-- tx is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  (* --- *)
  safe_acq t ->
  safe_acq tx ->
  safe_acq <{[x := tx] t}>.
Proof.
  intros. gendep Gamma. gendep T.
  induction t; intros; simpl; try destruct _str_eq_dec;
  invc_typeof; inv_sacq;
  eauto using safe_acq,
    MapEqv.update_permutation, ctx_eqv_typeof,
    update_safe_includes_safe_update,
    context_weakening, context_weakening_empty,
    nowrefs_subst2.
  Unshelve.
  eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma sacq_preservation_none : forall t1 t2,
  well_typed_term t1 ->
  (* --- *)
  safe_acq t1 ->
  t1 --[e_none]--> t2 ->
  safe_acq t2.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_sacq;
  eauto using sacq_subst, safe_acq.
Qed.

Local Lemma sacq_preservation_alloc : forall t1 t2 ad T,
  safe_acq t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  safe_acq t2.
Proof.
  intros. ind_tstep; intros; invc_sacq; eauto using safe_acq.
Qed.

Local Lemma sacq_preservation_insert : forall t1 t2 ad t T,
  safe_acq t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  safe_acq t2.
Proof.
  intros. ind_tstep; intros; invc_sacq; eauto using safe_acq.
Qed.

Local Lemma sacq_preservation_read : forall m t1 t2 ad t,
  forall_memory m safe_acq ->
  (* --- *)
  m[ad].t = Some t ->
  safe_acq t1 ->
  t1 --[e_read ad t]--> t2 ->
  safe_acq t2.
Proof.
  intros. ind_tstep; intros; invc_sacq; eauto using safe_acq.
Qed.

Local Lemma sacq_preservation_write : forall t1 t2 ad t,
  safe_acq t1 ->
  t1 --[e_write ad t]--> t2 ->
  safe_acq t2.
Proof.
  intros. ind_tstep; intros; invc_sacq; eauto using safe_acq.
Qed.

Local Lemma sacq_preservation_acq : forall m t1 t2 ad t,
  forall_memory m value ->
  forall_memory m safe_acq ->
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  m[ad].t = Some t ->
  safe_acq t1 ->
  t1 --[e_acq ad t]--> t2 ->
  safe_acq t2.
Proof.
  intros * ? ? [T ?] **. gendep T.
  ind_tstep; intros;
  repeat invc_typeof; repeat invc_cr; repeat invc_sacq;
  try invc_eq; eauto 6 using sacq_from_nowrefs, sacq_subst, safe_acq.
Qed.

Local Lemma sacq_preservation_rel : forall t1 t2 ad,
  safe_acq t1 ->
  t1 --[e_rel ad]--> t2 ->
  safe_acq t2.
Proof.
  intros. ind_tstep; intros; invc_sacq; eauto using safe_acq.
Qed.

Local Lemma sacq_preservation_spawn : forall t1 t2 tid t,
  safe_acq t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  safe_acq t2.
Proof.
  intros. ind_tstep; intros; invc_sacq; eauto using safe_acq.
Qed.

Local Lemma sacq_preservation_spawned : forall t1 t2 tid t,
  safe_acq t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  safe_acq t.
Proof.
  intros. ind_tstep; intros; invc_sacq; eauto using safe_acq.
Qed.

Theorem sacq_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   value ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistent_references m1) ->
  (* --- *)
  forall_program m1 ths1 safe_acq ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 safe_acq.
Proof.
  intros until 3. intros [? ?] ?. split.
  - invc_cstep; try invc_mstep; trivial; intros ? ? ?; upsilon;
    eauto using sacq_insert_term, sacq_write_term.
  - invc_cstep; try invc_mstep; upsilon.
    + eauto using sacq_preservation_none.
    + eauto using sacq_preservation_alloc.
    + eauto using sacq_preservation_insert.
    + eauto using sacq_preservation_read.
    + eauto using sacq_preservation_write.
    + eauto using sacq_preservation_acq.
    + eauto using sacq_preservation_rel.
    + eauto using sacq_preservation_spawn.
    + eauto using sacq_preservation_spawned.
Qed.

