From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentTerm.

(* ------------------------------------------------------------------------- *)
(* safe-newx                                                                 *)
(* ------------------------------------------------------------------------- *)

Inductive safe_newx : tm -> Prop :=
  | snx_unit  :                 safe_newx <{unit         }>
  | snx_nat   : forall n,       safe_newx <{nat n        }>
  | snx_var   : forall x,       safe_newx <{var x        }>
  | snx_fun   : forall x Tx t,  safe_newx t  ->
                                safe_newx <{fn x Tx t    }>
  | snx_call  : forall t1 t2,   safe_newx t1 ->
                                safe_newx t2 ->
                                safe_newx <{call t1 t2   }>
  | snx_ref   : forall ad T,    safe_newx <{&ad : T      }>
  | snx_newR  : forall t T,     safe_newx t  ->
                                safe_newx <{new t : r&T  }>
  | snx_newX  : forall t T,     no_wrefs  t  ->
                                safe_newx t  ->
                                safe_newx <{new t : x&T  }>
  | snx_newW  : forall t T,     safe_newx t  ->
                                safe_newx <{new t : w&T  }>
  | snx_init  : forall ad t T,  safe_newx t  ->
                                safe_newx <{init ad t : T}>
  | snx_load  : forall t,       safe_newx t  ->
                                safe_newx <{*t           }>
  | snx_asg   : forall t1 t2,   safe_newx t1 ->
                                safe_newx t2 ->
                                safe_newx <{t1 := t2     }>
  | snx_acq   : forall t1 x t2, safe_newx t1 ->
                                safe_newx t2 ->
                                safe_newx <{acq t1 x t2  }>
  | snx_cr    : forall ad t,    safe_newx t  ->
                                safe_newx <{cr ad t      }>
  | snx_spawn : forall t,       safe_newx t  ->
                                safe_newx <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _snx tt :=
  match goal with
  | H : safe_newx <{unit        }>   |- _ => clear H
  | H : safe_newx <{nat _       }>   |- _ => clear H
  | H : safe_newx <{var _       }>   |- _ => clear H
  | H : safe_newx <{fn _ _ _    }>   |- _ => tt H
  | H : safe_newx <{call _ _    }>   |- _ => tt H
  | H : safe_newx <{& _ : _     }>   |- _ => clear H
  | H : safe_newx <{new _ : _   }>   |- _ => tt H
  | H : safe_newx <{init _ _ : _}>   |- _ => tt H
  | H : safe_newx <{* _         }>   |- _ => tt H
  | H : safe_newx <{_ := _      }>   |- _ => tt H
  | H : safe_newx <{acq _ _ _   }>   |- _ => tt H
  | H : safe_newx <{cr _ _      }>   |- _ => tt H
  | H : safe_newx <{spawn _     }>   |- _ => tt H
  end.

Ltac inv_snx  := _snx inv.
Ltac invc_snx := _snx invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma snx_insert_term : forall t1 t2 ad t T,
  safe_newx t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  safe_newx t.
Proof.
  intros. ind_tstep; invc_snx; auto using safe_newx.
Qed.

Lemma snx_write_term : forall t1 t2 ad t,
  safe_newx t1 ->
  t1 --[e_write ad t]--> t2 ->
  safe_newx t.
Proof.
  intros. ind_tstep; invc_snx; auto using safe_newx.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma snx_subst : forall Gamma x tx t Tx T,
  value tx ->
  empty |-- tx is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  (* --- *)
  safe_newx t ->
  safe_newx tx ->
  safe_newx <{[x := tx] t}>.
Proof.
  intros. gendep Gamma. gendep T.
  induction t; intros; simpl; try destruct _str_eq_dec;
  invc_typeof; invc_snx; try spec;
  eauto 8 using safe_newx,
    MapEqv.update_permutation, ctx_eqv_typeof,
    MapInc.update_inclusion, update_safe_includes_safe_update,
    context_weakening, context_weakening_empty,
    nowrefs_subst1.
  Unshelve.
  eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma snx_preservation_none : forall t1 t2,
  well_typed_term t1 ->
  (* --- *)
  safe_newx t1 ->
  t1 --[e_none]--> t2 ->
  safe_newx t2.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_snx;
  eauto using snx_subst, safe_newx.
Qed.

Local Lemma snx_preservation_alloc : forall t1 t2 ad T,
  safe_newx t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  safe_newx t2.
Proof.
  intros. ind_tstep; intros; invc_snx; auto using safe_newx.
Qed.

Local Lemma snx_preservation_insert : forall t1 t2 ad t T,
  safe_newx t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  safe_newx t2.
Proof.
  intros. ind_tstep; intros; invc_snx; auto using safe_newx.
Qed.

Local Lemma snx_preservation_read : forall m t1 t2 ad t,
  forall_memory m safe_newx ->
  (* --- *)
  m[ad].t = Some t ->
  safe_newx t1 ->
  t1 --[e_read ad t]--> t2 ->
  safe_newx t2.
Proof.
  intros. ind_tstep; intros; invc_snx; eauto using safe_newx.
Qed.

Local Lemma snx_preservation_write : forall t1 t2 ad t,
  safe_newx t1 ->
  t1 --[e_write ad t]--> t2 ->
  safe_newx t2.
Proof.
  intros. ind_tstep; intros; invc_snx; auto using safe_newx.
Qed.

Local Lemma snx_preservation_acq : forall m t1 t2 ad t,
  forall_memory m value ->
  forall_memory m safe_newx ->
  well_typed_term t1 ->
  consistent_term m t1 ->
  (* --- *)
  m[ad].t = Some t ->
  safe_newx t1 ->
  t1 --[e_acq ad t]--> t2 ->
  safe_newx t2.
Proof.
  intros * ? ? [T ?] **. gendep T.
  ind_tstep; intros;
  repeat invc_typeof; repeat invc_ctm; repeat invc_snx;
  try invc_eq; eauto using snx_subst, safe_newx.
Qed.

Local Lemma snx_preservation_rel : forall t1 t2 ad,
  safe_newx t1 ->
  t1 --[e_rel ad]--> t2 ->
  safe_newx t2.
Proof.
  intros. ind_tstep; intros; invc_snx; auto using safe_newx.
Qed.

Local Lemma snx_preservation_spawn : forall t1 t2 tid t,
  safe_newx t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  safe_newx t2.
Proof.
  intros. ind_tstep; intros; invc_snx; auto using safe_newx.
Qed.

Local Lemma snx_preservation_spawned : forall t1 t2 tid t,
  safe_newx t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  safe_newx t.
Proof.
  intros. ind_tstep; intros; invc_snx; auto using safe_newx.
Qed.

Theorem snx_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   value ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistent_term m1) ->
  (* --- *)
  forall_program m1 ths1 safe_newx ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 safe_newx.
Proof.
  intros until 3. intros [? ?] ?. split.
  - invc_cstep; try invc_mstep; trivial; intros ? ? ?; upsilon;
    eauto using snx_insert_term, snx_write_term.
  - invc_cstep; try invc_mstep; upsilon.
    + eauto using snx_preservation_none.
    + eauto using snx_preservation_alloc.
    + eauto using snx_preservation_insert.
    + eauto using snx_preservation_read.
    + eauto using snx_preservation_write.
    + eauto using snx_preservation_acq.
    + eauto using snx_preservation_rel.
    + eauto using snx_preservation_spawn.
    + eauto using snx_preservation_spawned.
Qed.

