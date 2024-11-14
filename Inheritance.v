From Elo Require Import Core.

From Elo Require Import Properties.

From Elo Require Import AccessCore.
From Elo Require Import NotAccess.

(* ------------------------------------------------------------------------- *)
(* inheritance                                                               *)
(* ------------------------------------------------------------------------- *)

(* subst ------------------------------------------------------------------- *)

Local Lemma acc_inheritance_subst : forall m x Tx t tx ad,
  access ad m <{[x := tx] t}> ->
  access ad m <{call <{fn x Tx t}> tx}>.
Proof.
  intros. induction t; simpl in *;
  try destruct str_eq_dec; try invc_acc; eauto using access;
  aspecialize; repeat invc_acc; eauto using access.
Qed.

Local Lemma xacc_inheritance_subst : forall m x Tx t tx ad adx,
  no_inits t ->
  no_crs   t ->
  (* --- *)
  xaccess adx ad m <{[x := tx] t}> ->
  xaccess adx ad m <{call <{fn x Tx t}> tx}>.
Proof.
  intros. induction t; simpl in *; try destruct str_eq_dec;
  invc_noinits; invc_nocrs; try invc_xacc;
  repeat aspecialize; repeat invc_xacc; eauto using xaccess.
Qed.

(* mem-add ----------------------------------------------------------------- *)

Lemma acc_inheritance_mem_add : forall m t ad T,
  access ad (m +++ (None, T, false)) t ->
  access ad m t.
Proof.
  intros * Hacc.
  induction Hacc; eauto using access;
  omicron; upsilon; eauto using access.
Qed.

Lemma xacc_inheritance_mem_add : forall m t adx ad T,
  xaccess adx ad (m +++ (None, T, false)) t ->
  xaccess adx ad m t.
Proof.
  intros * Hxacc. induction Hxacc; eauto using acc_inheritance_mem_add, xaccess.
Qed.

(* none -------------------------------------------------------------------- *)

Lemma acc_inheritance_none : forall ad m t1 t2,
  access ad m t2 ->
  t1 --[e_none]--> t2 ->
  access ad m t1.
Proof.
  intros. ind_tstep; try invc_acc; eauto using acc_inheritance_subst, access.
Qed.

Lemma xacc_inheritance_none : forall adx ad m t1 t2,
  valid_blocks t1 ->
  (* --- *)
  xaccess adx ad m t2 ->
  t1 --[e_none]--> t2 ->
  xaccess adx ad m t1.
Proof.
  intros. ind_tstep; repeat invc_vb; try invc_xacc;
  eauto using acc_inheritance_none, xacc_inheritance_subst, xaccess.
Qed.

(* alloc ------------------------------------------------------------------- *)

Lemma acc_inheritance_alloc : forall ad m t1 t2 T,
  access ad (m +++ (None, T, false)) t2 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  access ad m t1.
Proof.
  intros. ind_tstep; invc_acc;
  eauto using acc_inheritance_mem_add, access.
Qed.

Lemma xacc_inheritance_alloc : forall adx ad m t1 t2 T,
  adx <> #m ->
  xaccess adx ad (m +++ (None, T, false)) t2 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  xaccess adx ad m t1.
Proof.
  intros. ind_tstep; invc_xacc;
  eauto using acc_inheritance_alloc, xacc_inheritance_mem_add, xaccess.
Qed.

