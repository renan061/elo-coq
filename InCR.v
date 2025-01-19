From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import NoReacq.
From Elo Require Import ValidTerm.
From Elo Require Import OneCR.
From Elo Require Import IsWaiting.

(* ------------------------------------------------------------------------- *)
(* in-cr & not-in-cr                                                         *)
(* ------------------------------------------------------------------------- *)

Definition in_cr (ad : addr) (t : tm) := one_cr ad t /\ no_reacq ad t.

Definition not_in_cr (ad : addr) (t : tm) := no_cr ad t \/ is_waiting ad t.

(* lemmas ------------------------------------------------------------------ *)

Corollary nincr_unit : forall ad,
  not_in_cr ad <{unit}>.
Proof.
  intros. left. auto using no_cr.
Qed.

Corollary nincr_from_value : forall m ad t,
  valid_term m t ->
  (* --- *)
  value t ->
  not_in_cr ad t.
Proof.
  intros. left. eauto using nocr_from_value.
Qed.

Corollary nincr_incr_contradiction : forall ad t,
  not_in_cr ad t ->
  in_cr     ad t ->
  False.
Proof.
  intros * [? | ?] [? ?];
  eauto using nocr_onecr_contradiction, noreacq_isw_contradiction.
Qed.

(* preservation (incr) ----------------------------------------------------- *)

Local Ltac solve_incr_preservation L1 L2 :=
  intros; match goal with H : in_cr _ _ |- _ => destruct H end; split;
  eauto using nocr_from_value, noreacq_from_value, L1, L2.

Corollary incr_preservation_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  in_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_none
    noreacq_preservation_none.
Qed.

Corollary incr_preservation_alloc : forall ad t1 t2 ad' T',
  in_cr ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_alloc
    noreacq_preservation_alloc.
Qed.

Corollary incr_preservation_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  in_cr ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_init
    noreacq_preservation_init.
Qed.

Corollary incr_preservation_read : forall ad m t1 t2 ad' t',
  valid_term m t' ->
  value t'        ->
  (* --- *)
  in_cr ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_read
    noreacq_preservation_read.
Qed.

Corollary incr_preservation_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  in_cr ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_write
    noreacq_preservation_write.
Qed.

Corollary incr_preservation_acq : forall ad m t1 t2 ad' t',
  valid_term m t' ->
  value t'        ->
  (* --- *)
  ad <> ad' ->
  in_cr ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_acq
    noreacq_preservation_acq.
Qed.

Corollary incr_preservation_rel : forall ad t1 t2 ad',
  ad <> ad' ->
  in_cr ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_rel
    noreacq_preservation_rel.
Qed.

Corollary incr_preservation_wacq : forall ad t1 t2 ad',
  in_cr ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_wacq
    noreacq_preservation_wacq.
Qed.

Corollary incr_preservation_wrel : forall ad t1 t2 ad',
  ad <> ad' ->
  in_cr ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_wrel
    noreacq_preservation_wrel.
Qed.

Corollary incr_preservation_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  in_cr ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  in_cr ad t2.
Proof.
  solve_incr_preservation
    onecr_preservation_spawn
    noreacq_preservation_spawn.
Qed.

(* preservation  (nincr) --------------------------------------------------- *)

Local Ltac solve_nincr_preservation L1 L2 :=
  intros; match goal with H : not_in_cr _ _ |- _ => destruct H end;
  solve [ left; eauto using nocr_from_value, L1
        | right; eauto using noreacq_from_value, L2
        ].

Corollary nincr_preservation_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  not_in_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_none
    isw_preservation_none.
Qed.

Corollary nincr_preservation_alloc : forall ad t1 t2 ad' T',
  not_in_cr ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_alloc
    isw_preservation_alloc.
Qed.

Corollary nincr_preservation_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  not_in_cr ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_init
    isw_preservation_init.
Qed.

Corollary nincr_preservation_read : forall ad m t1 t2 ad' t',
  valid_term m t' ->
  value t'        ->
  (* --- *)
  not_in_cr ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_read
    isw_preservation_read.
Qed.

Corollary nincr_preservation_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  not_in_cr ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_write
    isw_preservation_write.
Qed.

Corollary nincr_preservation_acq : forall ad m t1 t2 ad' t',
  valid_term m t' ->
  value t'        ->
  (* --- *)
  ad <> ad' ->
  not_in_cr ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_acq
    isw_preservation_acq.
Qed.

Corollary nincr_preservation_rel : forall ad t1 t2 ad',
  not_in_cr ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_rel
    isw_preservation_rel.
Qed.

Corollary nincr_preservation_wacq : forall ad t1 t2 ad',
  ad <> ad' ->
  not_in_cr ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_wacq
    isw_preservation_wacq.
Qed.

Corollary nincr_preservation_wrel : forall ad t1 t2 ad',
  ad <> ad' ->
  not_in_cr ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_wrel
    isw_preservation_wrel.
Qed.

Corollary nincr_preservation_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  not_in_cr ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  not_in_cr ad t2.
Proof.
  solve_nincr_preservation
    nocr_preservation_spawn
    isw_preservation_spawn.
Qed.

