From Elo Require Import Core.

From Elo Require Import NoInit.
From Elo Require Import NoCR.
From Elo Require Import ValidBlocks.

(* ------------------------------------------------------------------------- *)
(* no-init inheritance                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma noinit_inheritance_subst : forall x Tx t tx ad,
  no_init ad tx ->
  no_init ad <{[x := tx] t}> ->
  no_init ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. repeat constructor; trivial.
  induction t; simpl in *;
  try destruct str_eq_dec; try invc_noinit; eauto using no_init.
Qed.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_noinit_inheritance :=
  intros; ind_tstep; repeat invc_vb; try invc_noinit;
  eauto using noinit_from_value, noinit_inheritance_subst, no_init.

Lemma noinit_inheritance_none : forall ad t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_init ad t2 ->
  t1 --[e_none]--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_alloc : forall ad ad' t1 t2 T,
  no_init ad t2 ->
  t1 --[e_alloc ad' T]--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_insert : forall ad ad' t t1 t2,
  valid_blocks t1 ->
  (* --- *)
  ad <> ad' ->
  no_init ad t2 ->
  t1 --[e_insert ad' t]--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_read : forall ad ad' t t1 t2,
  no_init ad t2 ->
  t1 --[e_read ad' t]--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_write : forall ad ad' t t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_init ad t2 ->
  t1 --[e_write ad' t]--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_acq : forall ad ad' t t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_init ad t2 ->
  t1 --[e_acq ad' t]--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_rel : forall ad ad' t1 t2,
  no_init ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_spawn : forall ad tid t t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_init ad t2 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

(* ------------------------------------------------------------------------- *)
(* no-cr inheritance                                                         *)
(* ------------------------------------------------------------------------- *)

Local Lemma nocr_inheritance_subst : forall x Tx t tx ad,
  no_cr ad tx ->
  no_cr ad <{[x := tx] t}> ->
  no_cr ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. repeat constructor; trivial.
  induction t; simpl in *;
  try destruct str_eq_dec; try invc_nocr; eauto using no_cr.
Qed.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_nocr_inheritance :=
  intros; ind_tstep; repeat invc_vb; try invc_nocr;
  eauto using nocr_from_value, nocr_inheritance_subst, no_cr.

Lemma nocr_inheritance_none : forall ad t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_none]--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_alloc : forall ad ad' t1 t2 T,
  no_cr ad t2 ->
  t1 --[e_alloc ad' T]--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_insert : forall ad ad' t t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_insert ad' t]--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_read : forall ad ad' t t1 t2,
  no_cr ad t2 ->
  t1 --[e_read ad' t]--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_write : forall ad ad' t t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_write ad' t]--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_acq : forall ad ad' t t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_acq ad' t]--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_rel : forall ad ad' t1 t2,
  ad <> ad' ->
  no_cr ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_spawn : forall ad tid t t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

