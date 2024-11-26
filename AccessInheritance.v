From Elo Require Import Core.

From Elo Require Import Properties1.
From Elo Require Import Properties2.

From Elo Require Import AccessCore.

Corollary noref_from_insert : forall m ths tid t ad te,
  forall_threads ths (consistent_inits m) ->
  no_uninitialized_references m ths ->
  (* --- *)
  ths[tid] --[e_insert ad te]--> t ->
  forall_program m ths (no_ref ad).
Proof.
  eauto using insert_then_uninitialized.
Qed.

(* ------------------------------------------------------------------------- *)
(* access inheritance                                                        *)
(* ------------------------------------------------------------------------- *)

Lemma acc_inheritance_subst : forall x Tx t tx ad,
  access ad <{[x := tx] t}> ->
  access ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. induction t; simpl in *;
  try destruct str_eq_dec; try invc_acc; eauto using access;
  aspecialize; repeat invc_acc; eauto using access.
Qed.

Lemma acc_inheritance_mem_add : forall m t ad T,
  access ad (m +++ (None, T, false)) t ->
  access ad m t.
Proof.
  intros * Hacc.
  induction Hacc; eauto using access;
  omicron; upsilon; eauto using access.
Qed.

Lemma acc_inheritance_mem_set1 : forall ad ad' m t t',
  forall_memory m (no_ref ad') ->
  no_ref ad' t ->
  (* --- *)
  access ad m[ad'.t <- t'] t ->
  access ad m t.
Proof.
  intros * ? ? Hacc. induction Hacc; invc_noref; upsilon; eauto using access.
Qed.

Lemma acc_inheritance_mem_set2 : forall ad ad' m t t',
  ~ access ad m t' ->
  (* --- *)
  access ad m[ad'.t <- t'] t ->
  access ad m t.
Proof.
  intros * ? Hacc. induction Hacc; eauto using access;
  repeat omicron; upsilon; eauto using access.
Qed.

Lemma acc_inheritance_mem_set3 : forall ad ad' m t t',
  ~ access ad' m t ->
  (* --- *)
  access ad m[ad'.t <- t'] t ->
  access ad m t.
Proof.
  intros * ? Hacc. induction Hacc; invc_nacc; sigma; eauto using access.
Qed.

Lemma acc_inheritance_mem_acq : forall ad ad' m t,
  access ad m[ad'.X <- true] t ->
  access ad m t.
Proof.
  intros * Hacc. induction Hacc; eauto using access;
  (eapply acc_memR || eapply acc_memW); upsilon; eauto.
Qed.

Lemma acc_inheritance_mem_rel : forall ad ad' m t,
  access ad m[ad'.X <- false] t ->
  access ad m t.
Proof.
  intros * Hacc. induction Hacc; eauto using access;
  (eapply acc_memR || eapply acc_memW); upsilon; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma acc_inheritance_none : forall ad m t1 t2,
  access ad m t2 ->
  t1 --[e_none]--> t2 ->
  access ad m t1.
Proof.
  intros. ind_tstep; try invc_acc; eauto using acc_inheritance_subst, access.
Qed.

Lemma acc_inheritance_alloc : forall ad m t1 t2 T,
  access ad (m +++ (None, T, false)) t2 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  access ad m t1.
Proof.
  intros. ind_tstep; invc_acc; eauto using acc_inheritance_mem_add, access.
Qed.

Lemma acc_inheritance_insert : forall ad ad' m t t1 t2,
  forall_memory m (no_ref ad') ->
  no_ref ad' t1 ->
  (* --- *)
  ad <> ad' ->
  access ad m[ad'.t <- t] t2 ->
  t1 --[e_insert ad' t]--> t2 ->
  access ad m t1.
Proof.
  intros. ind_tstep; invc_noref; invc_acc; eauto using access; upsilon;
  eauto using acc_inheritance_mem_set1, access.
Qed.

Lemma acc_inheritance_read : forall ad ad' m t t1 t2,
  well_typed_term t1 ->
  (* --- *)
  m[ad'].t = Some t ->
  access ad m t2 ->
  t1 --[e_read ad' t]--> t2 ->
  access ad m t1.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; try invc_acc; eauto using access;
  destruct (nat_eq_dec ad' ad); subst; eauto using access.
Qed.

Lemma acc_inheritance_write : forall ad ad' m t t1 t2,
  access ad m[ad'.t <- t] t2 ->
  t1 --[e_write ad' t]--> t2 ->
  access ad m t1.
Proof.
  intros. ind_tstep; invc_acc; eauto using access; upsilon.
  - destruct (acc_dec ad' m t2); eauto using acc_inheritance_mem_set3, access.
    destruct (acc_dec ad m t); eauto using acc_inheritance_mem_set2, access.
    destruct (acc_dec ad m t1), (acc_dec ad m t2); eauto using access.
    assert (~ access ad m <{call t1 t2}>) by eauto using nacc_call.
Abort.

(* ------------------------------------------------------------------------- *)
(* xaccess inheritance                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma xacc_inheritance_subst : forall m x Tx t tx ad adx,
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

Lemma xacc_inheritance_mem_add : forall m t adx ad T,
  xaccess adx ad (m +++ (None, T, false)) t ->
  xaccess adx ad m t.
Proof.
  intros * Hxacc. induction Hxacc; eauto using acc_inheritance_mem_add, xaccess.
Qed.

Lemma xacc_inheritance_mem_set1 : forall adx ad ad' m t t',
  forall_memory m (no_ref ad') ->
  no_ref ad' t ->
  (* --- *)
  xaccess adx ad m[ad'.t <- t'] t ->
  xaccess adx ad m t.
Proof.
  intros * ? ? Hxacc. induction Hxacc; invc_noref; eauto using xaccess;
  eauto using acc_inheritance_mem_set1, xaccess.
Qed.

Lemma xacc_inheritance_mem_set2 : forall adx ad ad' m t t',
  ~ access ad m t' ->
  (* --- *)
  xaccess adx ad m[ad'.t <- t'] t ->
  xaccess adx ad m t.
Proof.
  intros * ? Hxacc. induction Hxacc;
  eauto using acc_inheritance_mem_set2, xaccess.
Qed.

(* ------------------------------------------------------------------------- *)

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

Lemma xacc_inheritance_alloc : forall adx ad m t1 t2 T,
  adx <> #m ->
  xaccess adx ad (m +++ (None, T, false)) t2 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  xaccess adx ad m t1.
Proof.
  intros. ind_tstep; invc_xacc;
  eauto using acc_inheritance_alloc, xacc_inheritance_mem_add, xaccess.
Qed.

Lemma xacc_inheritance_insert : forall adx ad ad' m t t1 t2,
  forall_memory m (no_ref ad') ->
  no_ref ad' t1 ->
  (* --- *)
  ad <> ad' ->
  xaccess adx ad m[ad'.t <- t] t2 ->
  t1 --[e_insert ad' t]--> t2 ->
  xaccess adx ad m t1.
Proof.
  intros. ind_tstep; invc_noref; inv_xacc; eauto using xaccess;
  eauto using acc_inheritance_insert, xacc_inheritance_mem_set1, xaccess.
Qed.

Lemma xacc_inheritance_read : forall adx ad ad' m t t1 t2,
  forall_memory m value ->
  forall_memory m valid_blocks ->
  well_typed_term t1 ->
  (* --- *)
  m[ad'].t = Some t ->
  xaccess adx ad m t2 ->
  t1 --[e_read ad' t]--> t2 ->
  xaccess adx ad m t1.
Proof.
  intros. ind_tstep; intros; invc_wtt; try invc_xacc;
  eauto using acc_inheritance_read, xaccess.
  exfalso. eauto using xacc_value_contradiction.
Qed.

Lemma xacc_inheritance_write : forall adx ad ad' m t t1 t2,
  ad <> ad' ->
  xaccess adx ad m[ad'.t <- t] t2 ->
  t1 --[e_write ad' t]--> t2 ->
  xaccess adx ad m t1.
Proof.
  intros. ind_tstep; invc_xacc; eauto using xaccess; upsilon.
Abort.
