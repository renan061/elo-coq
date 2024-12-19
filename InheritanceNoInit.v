From Elo Require Import Core.

From Elo Require Import NoInit.
From Elo Require Import ValidTerm.

Local Lemma noinit_inheritance_subst : forall x Tx t tx ad,
  no_init ad tx ->
  no_init ad <{[x := tx] t}> ->
  no_init ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. repeat constructor; trivial.
  induction t; simpl in *; try destruct _str_eq_dec;
  try invc_noinit; auto using no_init.
Qed.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_noinit_inheritance :=
  intros; ind_tstep; repeat invc_vtm; try invc_noinit;
  eauto using noinit_from_value, noinit_inheritance_subst, no_init.

Lemma noinit_inheritance_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  no_init ad t2 ->
  t1 --[e_none]--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_alloc : forall ad t1 t2 ad' T',
  no_init ad t2 ->
  t1 --[e_alloc ad' T']--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_insert : forall ad m t1 t2 ad' t' T',
  valid_term m t1 ->
  (* --- *)
  ad <> ad' ->
  no_init ad t2 ->
  t1 --[e_insert ad' t' T']--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_read : forall ad t1 t2 ad' t',
  no_init ad t2 ->
  t1 --[e_read ad' t']--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  no_init ad t2 ->
  t1 --[e_write ad' t']--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_acq : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  no_init ad t2 ->
  t1 --[e_acq ad' t']--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_rel : forall ad t1 t2 ad',
  no_init ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

Lemma noinit_inheritance_spawn : forall ad m t1 t2 tid t,
  valid_term m t1 ->
  (* --- *)
  no_init ad t2 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_init ad t1.
Proof. solve_noinit_inheritance. Qed.

