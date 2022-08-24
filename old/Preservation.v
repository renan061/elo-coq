From Coq Require Import Lia.

From Elo Require Export Array.
From Elo Require Export Map.
From Elo Require Export Core0.

Ltac splits n :=
  match n with
  | O => fail
  | S O => idtac
  | S ?n' => split; [| splits n']
  end.

(* ------------------------------------------------------------------------- *)
(* Definitions ------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Definition well_typed_memory mt m :=
  length mt = length m /\
  (forall ad, mt / empty |-- (getTM m ad) is (getTY mt ad)).

Definition well_typed_threads mt ths :=
  forall tid, exists T, mt / empty |-- (getTM ths tid) is T.

Definition finished ths :=
  forall tid, value (getTM ths tid).

(* ------------------------------------------------------------------------- *)
(* Extends ----------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Module Extends.
  Inductive extends' {A} : list A -> list A -> Prop :=
    | extends_nil : forall mt,
      extends' mt nil
    | extends_cons : forall x mt mt',
      extends' mt mt' ->
      extends' (x :: mt) (x :: mt').

    Infix "extends" := extends' (at level 50).

    Lemma refl : forall {A} (mt : list A),
      mt extends mt.
    Proof.
      intros. induction mt; eauto using @extends'.
    Qed.

    Lemma add : forall {A} (mt : list A) a,
      (add mt a) extends mt.
    Proof.
      intros. induction mt; eauto using @extends'.
    Qed.

    Lemma get : forall (mt mt' : list typ) i,
      i < length mt' ->
      mt extends mt' ->
      getTY mt' i = getTY mt i.
    Proof.
      intros *. generalize dependent mt. generalize dependent i.
      induction mt'; intros * Hlen Hext; try solve [inversion Hlen].
      inversion Hext; subst. destruct i; trivial.
      unfold getTY, get. simpl in *. eauto using Lt.lt_S_n.
    Qed.

    Lemma length : forall {A} (mt mt' : list A) i,
      i < length mt' ->
      mt extends mt' ->
      i < length mt.
    Proof.
      intros *. generalize dependent mt. generalize dependent i.
      induction mt'; intros * Hlen Hext; try solve [inversion Hlen].
      inversion Hext; subst. destruct i;
      eauto using PeanoNat.Nat.lt_0_succ, Lt.lt_n_S, Lt.lt_S_n.
    Qed.
End Extends.

Infix "extends" := Extends.extends' (at level 50).

(* ------------------------------------------------------------------------- *)
(* Weakening --------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Lemma memory_weakening : forall mt mt' Gamma t T,
  mt extends mt' ->
  mt' / Gamma |-- t is T ->
  mt  / Gamma |-- t is T.
Proof.
  intros * Hext Htype.
  induction Htype; eauto using well_typed_term.
  erewrite Extends.get; eauto using well_typed_term, Extends.length.
Qed.

Lemma threads_memory_weakening : forall mt mt' ths,
  mt' extends mt ->
  well_typed_threads mt ths ->
  well_typed_threads mt' ths.
Proof.
  intros * Hext Hths. intros tid.
  specialize (Hths tid) as [? ?]. eexists.
  eauto using memory_weakening.
Qed.

Lemma context_weakening : forall mt Gamma Gamma' t T,
  Gamma includes Gamma' ->
  mt / Gamma' |-- t is T ->
  mt / Gamma  |-- t is T.
Proof.
  intros * Hinc Htype.
  generalize dependent Gamma.
  induction Htype; intros * Hinc;
  eauto 6 using @well_typed_term, safe_preserves_inclusion,
    update_preserves_inclusion.
Qed.

Lemma context_weakening_empty : forall mt Gamma t T,
  mt / empty |-- t is T ->
  mt / Gamma |-- t is T.
Proof.
  intros * Htype.
  eapply (context_weakening _ _ empty); auto.
  discriminate.
Qed.
