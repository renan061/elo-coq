From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Access.
From Elo Require Import XAccess.

Corollary noref_from_insert : forall m ths tid t ad' t' T',
  forall_threads ths (consistent_inits m) ->
  no_uninitialized_references m ths ->
  (* --- *)
  ths[tid] --[e_insert ad' t' T']--> t ->
  forall_program m ths (no_ref ad').
Proof.
  eauto using insert_then_uninitialized.
Qed.

Corollary acc_insert_contradiction : forall m ths tid t ad' t' T',
  forall_threads ths (consistent_inits m) ->
  no_uninitialized_references m ths ->
  (* --- *)
  ths[tid] --[e_insert ad' t' T']--> t ->
  access ad' ths[tid] ->
  False.
Proof.
  intros * ? ? Htstep ?. eapply noref_from_insert in Htstep as [? ?]; eauto.
  eauto using acc_noref_contradiction.
Qed.

(* ------------------------------------------------------------------------- *)
(* access inheritance                                                        *)
(* ------------------------------------------------------------------------- *)

Lemma acc_inheritance_subst : forall x Tx t tx ad,
  access ad <{[x := tx] t}> ->
  access ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. induction t; simpl in *;
  try destruct _str_eq_dec; try invc_acc; auto using access;
  spec; repeat invc_acc; auto using access.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma acc_inheritance_none : forall ad t1 t2,
  access ad t2 ->
  t1 --[e_none]--> t2 ->
  access ad t1.
Proof.
  intros. ind_tstep; try invc_acc; auto using acc_inheritance_subst, access.
Qed.

Lemma acc_inheritance_alloc : forall ad ad' t1 t2 T,
  access ad t2 ->
  t1 --[e_alloc ad' T]--> t2 ->
  access ad t1.
Proof.
  intros. ind_tstep; invc_acc; auto using access.
Qed.

Lemma acc_inheritance_insert : forall ad t1 t2 ad' t' T',
  ad <> ad' ->
  access ad t2 ->
  t1 --[e_insert ad' t' T']--> t2 ->
  access ad t1.
Proof.
  intros. ind_tstep; invc_acc; auto using access.
Qed.

Lemma acc_inheritance_read : forall ad m t1 t2 ad' t',
  well_typed_term t1 ->
  (* --- *)
  m[ad'].t = Some t' ->
  access ad t2 ->
  t1 --[e_read ad' t']--> t2 ->
  access ad t1.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; try invc_acc; auto using access;
  nat_eq_dec ad' ad; eauto using access.
  - admit.
  - admit.
  - admit.
Abort.

Lemma acc_inheritance_write : forall ad ad' t t1 t2,
  access ad t2 ->
  t1 --[e_write ad' t]--> t2 ->
  access ad t1.
Proof.
  intros. ind_tstep; invc_acc; auto using access.
Qed.

Lemma acc_inheritance_acq : forall ad ad' t t1 t2,
  access ad t2 ->
  t1 --[e_acq ad' t]--> t2 ->
  access ad t1.
Proof.
  intros. ind_tstep; invc_acc; auto using access.
Qed.

Lemma acc_inheritance_rel : forall ad ad' t1 t2,
  access ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  access ad t1.
Proof.
  intros. ind_tstep; try invc_acc; auto using access.
  admit.
Abort.

Lemma acc_inheritance_spawn : forall ad tid t t1 t2,
  access ad t2 ->
  t1 --[e_spawn tid t]--> t2 ->
  access ad t1.
Proof.
  intros. ind_tstep; try invc_acc; auto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* xaccess inheritance                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma xacc_inheritance_subst : forall x Tx t tx ad adx,
  no_inits t ->
  no_crs   t ->
  (* --- *)
  xaccess adx ad <{[x := tx] t}> ->
  xaccess adx ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. induction t; simpl in *; try destruct _str_eq_dec;
  invc_noinits; invc_nocrs; try invc_xacc;
  repeat spec; repeat invc_xacc; eauto using xaccess.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma xacc_inheritance_none : forall adx ad t1 t2,
  valid_blocks t1 ->
  (* --- *)
  xaccess adx ad t2 ->
  t1 --[e_none]--> t2 ->
  xaccess adx ad t1.
Proof.
  intros. ind_tstep; repeat invc_vb; try invc_xacc;
  eauto using acc_inheritance_none, xacc_inheritance_subst, xaccess.
Qed.

Lemma xacc_inheritance_alloc : forall adx adx' ad t1 t2 T',
  adx <> adx' ->
  xaccess adx ad t2 ->
  t1 --[e_alloc adx' T']--> t2 ->
  xaccess adx ad t1.
Proof.
  intros. ind_tstep; invc_xacc;
  eauto using acc_inheritance_alloc, xaccess.
Qed.

Lemma xacc_inheritance_insert : forall m adx ad t1 t2 ad' t' T',
  forall_memory m (no_ref ad') ->
  no_ref ad' t1 ->
  (* --- *)
  ad <> ad' ->
  xaccess adx ad t2 ->
  t1 --[e_insert ad' t' T']--> t2 ->
  xaccess adx ad t1.
Proof.
  intros. ind_tstep; invc_noref; inv_xacc; eauto using xaccess;
  eauto using acc_inheritance_insert, xaccess.
Qed.

Lemma xacc_inheritance_read : forall m adx ad ad' t' t1 t2,
  forall_memory m value ->
  forall_memory m valid_blocks ->
  (* --- *)
  m[ad'].t = Some t' ->
  xaccess adx ad t2 ->
  t1 --[e_read ad' t']--> t2 ->
  xaccess adx ad t1.
Proof.
  intros. ind_tstep; intros; try invc_xacc; eauto using xaccess.
  - repeat spec. constructor. admit.
  - exfalso. eauto using xacc_value_contradiction.
  - repeat spec. constructor. admit.
Abort.

Lemma xacc_inheritance_write : forall adx ad ad' t' t1 t2,
  ad <> ad' ->
  xaccess adx ad t2 ->
  t1 --[e_write ad' t']--> t2 ->
  xaccess adx ad t1.
Proof.
  intros. ind_tstep; invc_xacc; eauto using acc_inheritance_write, xaccess.
Qed.
