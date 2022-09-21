From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Strings.String.

From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import WBA.

Lemma context_weakening : forall Gamma Gamma' t T,
  Gamma' |-- t is T ->
  Gamma includes Gamma' ->
  Gamma  |-- t is T.
Proof.
  intros. generalize dependent Gamma.
  induction_type; intros;
  eauto using well_typed_term, update_preserves_inclusion.
Qed.

Lemma context_weakening_empty : forall Gamma t T,
  empty |-- t is T ->
  Gamma |-- t is T.
Proof.
  intros. eapply (context_weakening _ empty); trivial. discriminate.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma deterministic_typing : forall Gamma t T1 T2,
  Gamma |-- t is T1 ->
  Gamma |-- t is T2 ->
  T1 = T2.
Proof.
Admitted.

Ltac apply_deterministic_typing :=
  match goal with
  | H1 : _ |-- ?t is ?T1, H2 : _ |-- ?t is ?T2 |- _ =>
    assert (T1 = T2) by eauto using deterministic_typing; subst
  end.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma preservation_subst : forall t tx T Tx Tx' Gamma x,
  Gamma |-- (TM_Fun x Tx t) is (TY_Fun Tx' T) ->
  empty |-- tx is Tx' ->
  Gamma |-- [x := tx] t is T.
Proof.
  assert (forall t tx T Tx Gamma x,
    Gamma[x <== Tx] |-- t is T ->
    empty |-- tx is Tx ->
    Gamma |-- [x := tx] t is T
  ). {
    unfold subst. intros ?.
    induction t; intros * Htype ?; 
    try (destruct String.string_dec);
    inversion Htype; subst; 
    eauto using well_typed_term, context_weakening, context_weakening_empty,
      update_overwrite, update_permutation.
  }
  intros * ?. inversion_type. intros. eapply H; eauto.
Qed.

Theorem preservation : forall m m' t t' eff T,
  well_typed_references m t ->
  empty |-- t is T ->
  m / t ==[eff]==> m' / t' ->
  empty |-- t' is T.
Proof.
  intros * Hwtr Htype ?. inversion_mstep; generalize dependent t'.
  remember empty as Gamma.
  - clear Hwtr.
    induction Htype; intros; inversion_step;
    eauto using well_typed_term, preservation_subst.
  - clear Hwtr.
    induction Htype; intros; inversion_step;
    eauto using well_typed_term.
  - induction Htype; intros;
    inversion_step; inversion_clear Hwtr; subst;
    eauto using well_typed_term;
    inversion Htype; subst.
    + match goal with
      | Hwtr' : well_typed_references _ _ |- _ =>
        inversion Hwtr'; subst
      end.
      eauto using context_weakening_empty.
    + match goal with
      | Hwtr' : well_typed_references _ _ |- _ =>
        inversion Hwtr'; subst
      end.
      eauto using context_weakening_empty.
  - induction Htype; intros; inversion_step; try (inversion Hwtr; subst);
    eauto using well_typed_term.
Qed.

