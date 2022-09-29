From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Strings.String.

From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import References.

Local Lemma context_weakening : forall Gamma Gamma' t T,
  Gamma' |-- t is T ->
  Gamma includes Gamma' ->
  Gamma  |-- t is T.
Proof.
  intros. generalize dependent Gamma.
  induction_type; intros;
  eauto using well_typed_term, update_preserves_inclusion.
Qed.

Local Lemma context_weakening_empty : forall Gamma t T,
  empty |-- t is T ->
  Gamma |-- t is T.
Proof.
  intros. eapply (context_weakening _ empty); trivial. discriminate.
Qed.

Local Lemma preservation_subst : forall t tx T Tx Tx' Gamma x,
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
  intros * ?. inversion_type. intros. eauto.
Qed.

Theorem mstep_preservation : forall m m' t t' eff T,
  well_typed_references m t ->
  empty |-- t is T ->
  m / t ==[eff]==> m' / t' ->
  empty |-- t' is T.
Proof.
  intros * Hwtr ? ?. inversion_mstep; generalize dependent t';
  remember empty as Gamma;
  induction_type; intros; inversion_step; inversion_clear Hwtr;
  eauto using well_typed_term, preservation_subst;
  inversion_type;
  match goal with
  | H : well_typed_references _ _ |- _ => inversion_clear H
  end;
  eauto using context_weakening_empty.
Qed.

Ltac solve_with_steps :=
  eexists; eexists; eexists; eauto using step, mstep.

Ltac destruct_IH :=
  match goal with
  | IH : valid_accesses _ _ -> value _ \/ _ |- _ =>
    destruct IH as [? | [[eff [? [? ?]]] | [? [? ?]]]]; trivial
  end.

Ltac solve_mstep_progress :=
  match goal with
  | eff : effect |- _ =>
    try solve [solve_with_steps];
    destruct eff; inversion_mstep; try solve [solve_with_steps]
  end.

Theorem progress : forall m t T,
  valid_accesses m t ->
  empty |-- t is T ->
  (value t
    \/ (exists eff m' t', m / t ==[eff]==> m' / t')
    \/ (exists block t', t --[EF_Spawn block]--> t')).
Proof.
  intros. induction_type; try inversion_va;
  try solve [left; eauto using value]; right;
  try solve [right; eauto using step];
  try solve [left; solve_mstep_progress].
  - destruct_IH.
    + left. solve_with_steps.
    + left. destruct eff; inversion_mstep; solve_with_steps.
    + right. eauto using step.
  - destruct_IH.
    + left. solve_with_steps.
    + left. destruct eff; inversion_mstep; solve_with_steps.
    + right. eauto using step.
  - destruct_IH.
    + left. inversion H1; subst; inversion_type.
      eexists. eexists. eexists. eauto using step, mstep, access.
    + left. destruct eff; inversion_mstep; solve_with_steps.
    + right. eauto using step.
  - destruct_IH.
    + left. inversion H1; subst; inversion_type.
      eexists. eexists. eexists. eauto using step, mstep, access.
    + left. destruct eff; inversion_mstep; solve_with_steps.
    + right. eauto using step.
  - shelve.
  - shelve.
  - shelve.
Qed.

