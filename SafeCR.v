From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentTerm.
From Elo Require Import Soundness.

(* ------------------------------------------------------------------------- *)
(* safe-cr                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive safe_cr : tm -> Prop :=
  | scr_unit  :                 safe_cr <{unit         }>
  | scr_nat   : forall n,       safe_cr <{nat n        }>
  | scr_var   : forall x,       safe_cr <{var x        }>
  | scr_fun   : forall x Tx t,  safe_cr t  ->
                                safe_cr <{fn x Tx t    }>
  | scr_call  : forall t1 t2,   safe_cr t1 ->
                                safe_cr t2 ->
                                safe_cr <{call t1 t2   }>
  | scr_ref   : forall ad T,    safe_cr <{&ad : T      }>
  | scr_new   : forall t T,     safe_cr t  ->
                                safe_cr <{new t : T    }>
  | scr_init  : forall ad t T,  safe_cr t  ->
                                safe_cr <{init ad t : T}>
  | scr_load  : forall t,       safe_cr t  ->
                                safe_cr <{*t           }>
  | scr_asg   : forall t1 t2,   safe_cr t1 ->
                                safe_cr t2 ->
                                safe_cr <{t1 := t2     }>
  | scr_acq   : forall t1 x t2, safe_cr t1 ->
                                safe_cr <{acq t1 x t2  }>
  | scr_cr    : forall ad t,    (exists T, empty |-- t is `Safe T`) ->
                                safe_cr t  ->
                                safe_cr <{cr ad t      }>
  | scr_spawn : forall t,       safe_cr t  ->
                                safe_cr <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _scr tt :=
  match goal with
  | H : safe_cr <{unit        }>   |- _ => clear H
  | H : safe_cr <{nat _       }>   |- _ => clear H
  | H : safe_cr <{var _       }>   |- _ => clear H
  | H : safe_cr <{fn _ _ _    }>   |- _ => tt H
  | H : safe_cr <{call _ _    }>   |- _ => tt H
  | H : safe_cr <{& _ : _     }>   |- _ => clear H
  | H : safe_cr <{new _ : _   }>   |- _ => tt H
  | H : safe_cr <{init _ _ : _}>   |- _ => tt H
  | H : safe_cr <{* _         }>   |- _ => tt H
  | H : safe_cr <{_ := _      }>   |- _ => tt H
  | H : safe_cr <{acq _ _ _   }>   |- _ => tt H
  | H : safe_cr <{cr _ _      }>   |- _ => tt H
  | H : safe_cr <{spawn _     }>   |- _ => tt H
  end.

Ltac inv_scr  := _scr inv.
Ltac invc_scr := _scr invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma scr_from_nocrs : forall t,
  no_crs  t ->
  safe_cr t.
Proof.
  intros. induction t; invc_nocrs; eauto using safe_cr.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma scr_subst : forall Gamma x tx t Tx T,
  value tx ->
  empty |-- tx is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  (* --- *)
  safe_cr t ->
  safe_cr tx ->
  safe_cr <{[x := tx] t}>.
Proof.
  intros. gendep Gamma. gendep T.
  induction t; intros; simpl; try destruct _str_eq_dec;
  invc_typeof; invc_scr;
  eauto using safe_cr,
    MapEqv.update_permutation, ctx_eqv_typeof,
    update_safe_includes_safe_update, context_weakening.
  match goal with H : exists _, _ |- _ => destruct H end.
  erewrite <- hasvar_subst; eauto using hasvar_type_contradiction, safe_cr.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma scr_preservation_none : forall t1 t2,
  well_typed_term t1 ->
  (* --- *)
  safe_cr t1 ->
  t1 --[e_none]--> t2 ->
  safe_cr t2.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_scr;
  eauto using scr_subst, safe_cr.
  match goal with H : exists _, _ |- _ => destruct H end.
  apply_deterministic_typing. 
  eauto using typeof_preservation_none, safe_cr.
Qed.

Local Lemma scr_preservation_alloc : forall t1 t2 ad T,
  safe_cr t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  safe_cr t2.
Proof.
  intros. ind_tstep; intros; invc_scr; eauto using safe_cr.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_alloc, safe_cr.
Qed.

Local Lemma scr_preservation_insert : forall t1 t2 ad t T,
  safe_cr t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  safe_cr t2.
Proof.
  intros. ind_tstep; intros; invc_scr; eauto using safe_cr.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_insert, safe_cr.
Qed.

Local Lemma scr_preservation_read : forall m t1 t2 ad t,
  forall_memory m safe_cr ->
  consistent_term m t1 ->
  (* --- *)
  m[ad].t = Some t ->
  safe_cr t1 ->
  t1 --[e_read ad t]--> t2 ->
  safe_cr t2.
Proof.
  intros. ind_tstep; intros; invc_ctm; invc_scr; eauto using safe_cr.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_read, safe_cr.
Qed.

Local Lemma scr_preservation_write : forall t1 t2 ad t,
  safe_cr t1 ->
  t1 --[e_write ad t]--> t2 ->
  safe_cr t2.
Proof.
  intros. ind_tstep; intros; invc_scr; eauto using safe_cr.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_write, safe_cr.
Qed.

Local Lemma scr_preservation_acq : forall m t1 t2 ad t,
  forall_memory m value ->
  forall_memory m safe_cr ->
  valid_term m t1 ->
  well_typed_term t1 ->
  consistent_term m t1 ->
  (* --- *)
  m[ad].t = Some t ->
  safe_cr t1 ->
  t1 --[e_acq ad t]--> t2 ->
  safe_cr t2.
Proof.
  intros * ? ? ? [T ?] **. gendep T. ind_tstep; intros;
  repeat invc_vtm; repeat invc_typeof; repeat invc_ctm; repeat invc_scr;
  try invc_eq; eauto using safe_cr.
  - constructor.
    + rewrite <- empty_eq_safe_empty in *. eauto using typeof_subst.
    + eauto using scr_from_nocrs, scr_subst.
  - match goal with H : exists _, _ |- _ => destruct H end.
    eauto using typeof_preservation_acq, safe_cr.
Qed.

Local Lemma scr_preservation_rel : forall t1 t2 ad,
  safe_cr t1 ->
  t1 --[e_rel ad]--> t2 ->
  safe_cr t2.
Proof.
  intros. ind_tstep; intros; invc_scr; eauto using safe_cr.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_rel, safe_cr.
Qed.

Local Lemma scr_preservation_spawn : forall t1 t2 tid t,
  safe_cr t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  safe_cr t2.
Proof.
  intros. ind_tstep; intros; invc_scr; eauto using safe_cr.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_spawn, safe_cr.
Qed.

Local Lemma scr_preservation_spawned : forall t1 t2 tid t,
  safe_cr t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  safe_cr t.
Proof.
  intros. ind_tstep; intros; invc_scr; eauto using safe_cr.
Qed.

Theorem scr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   value ->
  forall_threads ths1 (valid_term m1) ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistent_term m1) ->
  (* --- *)
  forall_program m1 ths1 safe_cr ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 safe_cr.
Proof.
  intros until 4. intros [? ?] ?. split.
  - invc_cstep; try invc_mstep; trivial; intros ? ? ?; upsilon;
    eauto using value_insert_term, vtm_insert_term,
                value_write_term,  vtm_write_term,
                nocrs_from_value, scr_from_nocrs.
  - invc_cstep; try invc_mstep; upsilon.
    + eauto using scr_preservation_none.
    + eauto using scr_preservation_alloc.
    + eauto using scr_preservation_insert.
    + eauto using scr_preservation_read.
    + eauto using scr_preservation_write.
    + eauto using scr_preservation_acq.
    + eauto using scr_preservation_rel.
    + eauto using scr_preservation_spawn.
    + eauto using scr_preservation_spawned.
Qed.

