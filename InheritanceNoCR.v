From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import ValidTerm.

Local Lemma nocr_inheritance_subst : forall x Tx t tx ad,
  no_cr ad tx ->
  no_cr ad <{[x := tx] t}> ->
  no_cr ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. repeat constructor; trivial.
  induction t; simpl in *;
  try destruct _str_eq_dec; try invc_nocr; auto using no_cr.
Qed.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_nocr_inheritance :=
  intros; ind_tstep; repeat invc_vtm; try invc_nocr;
  eauto using nocr_from_value, nocr_inheritance_subst, no_cr.

Lemma nocr_inheritance_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_none]--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_alloc : forall ad t1 t2 ad' T',
  no_cr ad t2 ->
  t1 --[e_alloc ad' T']--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_insert : forall ad m t1 t2 ad' t' T',
  valid_term m t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_insert ad' t' T']--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_read : forall ad t1 t2 ad' t',
  no_cr ad t2 ->
  t1 --[e_read ad' t']--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_write ad' t']--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_acq : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_acq ad' t']--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_rel : forall ad t1 t2 ad',
  ad <> ad' ->
  no_cr ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

Lemma nocr_inheritance_spawn : forall ad m t1 t2 tid t,
  valid_term m t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_cr ad t1.
Proof. solve_nocr_inheritance. Qed.

