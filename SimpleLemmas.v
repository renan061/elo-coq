From Elo Require Import Core.
From Elo Require Import Properties.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma empty_eq_safe_empty :
  empty = safe empty.
Proof.
  eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma ctr_tstep_alloc_term : forall m t1 t2 ad t T,
  consistently_typed_references m t1 ->
  t1 --[e_alloc ad t T ]--> t2 ->
  consistently_typed_references m t.
Proof.
  intros. ind_tstep; inv_ctr; eauto using consistently_typed_references.
Qed.

Lemma ctr_tstep_write_term : forall m t1 t2 ad t T,
  consistently_typed_references m t1 ->
  t1 --[e_write ad t T ]--> t2 ->
  consistently_typed_references m t.
Proof.
  intros. ind_tstep; inv_ctr; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma consistently_typed_write_effect : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  consistently_typed_references m t1 ->
  (* --- *)
  t1 --[e_write ad t T]--> t2 ->
  exists Tm, T = `w&Tm`
          /\ empty |-- t is Tm
          /\ empty |-- m[ad].tm is Tm
          /\ m[ad].ty = `w&Tm`.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  ind_tstep; intros; inv_typeof; inv_ctr; eauto.
  inv_typeof. inv_ctr. eauto.
Qed.

