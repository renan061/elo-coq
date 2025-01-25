From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import NoReacq.
From Elo Require Import ValidTerm.
From Elo Require Import ConsistentWaits.
From Elo Require Import OneCR.
From Elo Require Import Waiting.

(* ------------------------------------------------------------------------- *)
(* holding & not-holding                                                     *)
(* ------------------------------------------------------------------------- *)

Definition holding (ad : addr) (t : tm) :=
  one_cr ad t /\ no_reacq ad t.

Definition not_holding (ad : addr) (t : tm) :=
  no_cr ad t \/ (one_cr ad t /\ waiting ad t).

(* lemmas ------------------------------------------------------------------ *)

Corollary hg_contradiction : forall ad t,
  not_holding ad t ->
  holding     ad t ->
  False.
Proof.
  intros * [? | [? ?]] [? ?];
  eauto using nocr_onecr_contradiction, noreacq_wg_contradiction.
Qed.

Corollary nhg_unit : forall ad,
  not_holding ad <{unit}>.
Proof.
  intros. left. auto using no_cr.
Qed.

Corollary nhg_from_value : forall m ad t,
  valid_term m t ->
  (* --- *)
  value t ->
  not_holding ad t.
Proof.
  intros. left. eauto using nocr_from_value.
Qed.

(* preservation (holding) -------------------------------------------------- *)

Local Ltac solve_hg_preservation L1 L2 :=
  intros; match goal with H : holding _ _ |- _ => destruct H end; split;
  eauto using nocr_from_value, noreacq_from_value, L1, L2.

Corollary hg_preservation_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  holding ad t1 ->
  t1 --[e_none]--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_none
    noreacq_preservation_none.
Qed.

Corollary hg_preservation_alloc : forall ad t1 t2 ad' T',
  holding ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_alloc
    noreacq_preservation_alloc.
Qed.

Corollary hg_preservation_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  holding ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_init
    noreacq_preservation_init.
Qed.

Corollary hg_preservation_read : forall ad m t1 t2 ad' t',
  valid_term m t' ->
  value t'        ->
  (* --- *)
  holding ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_read
    noreacq_preservation_read.
Qed.

Corollary hg_preservation_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  holding ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_write
    noreacq_preservation_write.
Qed.

Corollary hg_preservation_acq : forall ad m t1 t2 ad' t',
  valid_term m t' ->
  value t'        ->
  (* --- *)
  ad <> ad' ->
  holding ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_acq
    noreacq_preservation_acq.
Qed.

Corollary hg_preservation_rel : forall ad t1 t2 ad',
  ad <> ad' ->
  holding ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_rel
    noreacq_preservation_rel.
Qed.

Corollary hg_preservation_wacq : forall ad t1 t2 ad',
  holding ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_wacq
    noreacq_preservation_wacq.
Qed.

Corollary hg_preservation_wrel : forall ad t1 t2 ad',
  ad <> ad' ->
  holding ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_wrel
    noreacq_preservation_wrel.
Qed.

Corollary hg_preservation_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  holding ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  holding ad t2.
Proof.
  solve_hg_preservation
    onecr_preservation_spawn
    noreacq_preservation_spawn.
Qed.

(* preservation  (nholding) ------------------------------------------------ *)

Local Ltac solve_nhg_preservation L1 L2 L3 :=
  intros;
  match goal with H : not_holding _ _ |- _ => destruct H as [? | [? ?]] end;
  solve [ left; eauto using nocr_from_value, L1
        | right; split; eauto using nocr_from_value, noreacq_from_value, L2, L3
        ].

Corollary nhg_preservation_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  not_holding ad t1 ->
  t1 --[e_none]--> t2 ->
  not_holding ad t2.
Proof.
  solve_nhg_preservation
    nocr_preservation_none
    onecr_preservation_none wg_preservation_none.
Qed.

Corollary nhg_preservation_alloc : forall ad t1 t2 ad' T',
  not_holding ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  not_holding ad t2.
Proof.
  solve_nhg_preservation
    nocr_preservation_alloc
    onecr_preservation_alloc wg_preservation_alloc.
Qed.

Corollary nhg_preservation_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  not_holding ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  not_holding ad t2.
Proof.
  solve_nhg_preservation
    nocr_preservation_init
    onecr_preservation_init wg_preservation_init.
Qed.

Corollary nhg_preservation_read : forall ad m t1 t2 ad' t',
  valid_term m t' ->
  value t'        ->
  (* --- *)
  not_holding ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  not_holding ad t2.
Proof.
  solve_nhg_preservation
    nocr_preservation_read
    onecr_preservation_read wg_preservation_read.
Qed.

Corollary nhg_preservation_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  not_holding ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  not_holding ad t2.
Proof.
  solve_nhg_preservation
    nocr_preservation_write
    onecr_preservation_write wg_preservation_write.
Qed.

Corollary nhg_preservation_acq : forall ad m t1 t2 ad' t',
  valid_term m t' ->
  value t'        ->
  (* --- *)
  ad <> ad' ->
  not_holding ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  not_holding ad t2.
Proof.
  solve_nhg_preservation
    nocr_preservation_acq
    onecr_preservation_acq wg_preservation_acq.
Qed.

Corollary nhg_preservation_rel : forall ad t1 t2 ad',
  ad <> ad' ->
  not_holding ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  not_holding ad t2.
Proof.
  solve_nhg_preservation
    nocr_preservation_rel
    onecr_preservation_rel wg_preservation_rel.
Qed.

Corollary nhg_preservation_wacq : forall ad t1 t2 ad',
  ad <> ad' ->
  not_holding ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  not_holding ad t2.
Proof.
  solve_nhg_preservation
    nocr_preservation_wacq
    onecr_preservation_wacq wg_preservation_wacq.
Qed.

Corollary nhg_preservation_wrel : forall m ad t1 t2 ad',
  valid_term m t1             ->
  consistent_waits WR_none t1 ->
  (* --- *)
  not_holding ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  not_holding ad t2.
Proof.
  intros * ? ? H **.
  assert (ad <> ad'). {
    intro. subst. destruct H as [? | [? ?]];
    eauto using nocr_wrel_contradiction, wg_effect_contradiction.
  }
  solve_nhg_preservation
    nocr_preservation_wrel
    onecr_preservation_wrel wg_preservation_wrel.
Qed.

Corollary nhg_preservation_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  not_holding ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  not_holding ad t2.
Proof.
  solve_nhg_preservation
    nocr_preservation_spawn
    onecr_preservation_spawn wg_preservation_spawn.
Qed.

