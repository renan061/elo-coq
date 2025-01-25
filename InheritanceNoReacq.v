From Elo Require Import Core.

From Elo Require Import NoReacq.
From Elo Require Import ValidTerm.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_noreacq_inheritance :=
  intros; ind_tstep; repeat invc_vtm; repeat invc_noreacq;
  eauto using noreacq_from_value, no_reacq.

Lemma noreacq_inheritance_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  no_reacq ad t2 ->
  t1 --[e_none]--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

Lemma noreacq_inheritance_alloc : forall ad t1 t2 ad' T',
  no_reacq ad t2 ->
  t1 --[e_alloc ad' T']--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

Lemma noreacq_inheritance_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  no_reacq ad t2 ->
  t1 --[e_init ad' t']--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

Lemma noreacq_inheritance_read : forall ad t1 t2 ad' t',
  no_reacq ad t' ->
  (* --- *)
  no_reacq ad t2 ->
  t1 --[e_read ad' t']--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

Lemma noreacq_inheritance_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  no_reacq ad t2 ->
  t1 --[e_write ad' t']--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

Lemma noreacq_inheritance_acq : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  no_reacq ad t2 ->
  t1 --[e_acq ad' t']--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

Lemma noreacq_inheritance_rel : forall ad t1 t2 ad',
  no_reacq ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

Lemma noreacq_inheritance_wacq : forall ad t1 t2 ad',
  ad <> ad' ->
  no_reacq ad t2 ->
  t1 --[e_wacq ad']--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

Lemma noreacq_inheritance_wrel : forall ad t1 t2 ad',
  no_reacq ad t2 ->
  t1 --[e_wrel ad']--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

Lemma noreacq_inheritance_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  no_reacq ad t2 ->
  t1 --[e_spawn t']--> t2 ->
  no_reacq ad t1.
Proof. solve_noreacq_inheritance. Qed.

