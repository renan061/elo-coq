From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.

Inductive well_behaved_locations (m : mem) : tm -> Prop :=
  | wbl_unit :
    well_behaved_locations m TM_Unit 

  | wbl_num : forall n,
    well_behaved_locations m (TM_Num n)

  | wbl_loc : forall T ad,
    empty |-- (getTM m ad) is T ->
    well_behaved_locations m (TM_Loc T ad)

  | wbl_new : forall T t,
    well_behaved_locations m t ->
    well_behaved_locations m (TM_New T t) 

  | wbl_load : forall t,
    well_behaved_locations m t ->
    well_behaved_locations m (TM_Load t) 

  | wbl_asg : forall t1 t2,
    well_behaved_locations m t1 ->
    well_behaved_locations m t2 ->
    well_behaved_locations m (TM_Asg t1 t2) 

  | wbl_id : forall id,
    well_behaved_locations m (TM_Id id)

  | wbl_fun : forall x Tx t,
    well_behaved_locations m t ->
    well_behaved_locations m (TM_Fun x Tx t) 

  | wbl_call : forall t1 t2,
    well_behaved_locations m t1 ->
    well_behaved_locations m t2 ->
    well_behaved_locations m (TM_Call t1 t2) 

  | wbl_seq : forall t1 t2,
    well_behaved_locations m t1 ->
    well_behaved_locations m t2 ->
    well_behaved_locations m (TM_Seq t1 t2) 

  | wbl_spawn : forall t,
    well_behaved_locations m t ->
    well_behaved_locations m (TM_Spawn t) 
  .

Lemma context_weakening : forall Gamma Gamma' t T,
  Gamma includes Gamma' ->
  Gamma' |-- t is T ->
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

Lemma substitution_preservation : forall t tx T Tx Tx' Gamma x,
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

Definition memprop m m' :=
  (forall ad T,
  ad < length m ->
  empty |-- (getTM m ad) is T ->
  empty |-- (getTM m' ad) is T).

Theorem preservation : forall m m' t t' eff T,
  well_behaved_locations m t ->
  empty |-- t is T ->
  m / t ==[eff]==> m' / t' ->
  empty |-- t' is T.
Proof.
  intros * Hmem Htype ?. inversion_mstep; generalize dependent t'.
  remember empty as Gamma.
  - induction Htype; intros; inversion_step; try (inversion Hmem; subst);
    eauto using well_typed_term, substitution_preservation.
  - induction Htype; intros; inversion_step; try (inversion Hmem; subst);
    eauto using well_typed_term.
  - induction Htype; intros; inversion_step; try (inversion Hmem; subst);
    eauto using well_typed_term.
    + inversion Htype; subst. shelve.
    + inversion Htype; subst. shelve.
  - induction Htype; intros; inversion_step; eauto using well_typed_term.
Qed.

