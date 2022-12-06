From Elo Require Import Core.

Reserved Notation " t 'contains' t' " (at level 30, no associativity).

Inductive Contains (t' : tm) : tm -> Prop :=
  | contains_eq : forall t,
    t = t' ->
    t contains t'

  | contains_new : forall t T,
    t contains t' ->
    <{ new T t }> contains t'

  | contains_load : forall t,
    t contains t' ->
    <{ *t }> contains t'

  | contains_asg1 : forall t1 t2,
    t1 contains t' ->
    <{ t1 = t2 }> contains t'

  | contains_asg2 : forall t1 t2,
    t2 contains t' ->
    <{ t1 = t2 }> contains t'

  | contains_fun : forall t x Tx,
    t contains t' ->
    <{ fn x Tx --> t }> contains t'

  | contains_call1 : forall t1 t2,
    t1 contains t' ->
    <{ call t1 t2 }> contains t'

  | contains_call2 : forall t1 t2,
    t2 contains t' ->
    <{ call t1 t2 }> contains t'

  | contains_seq1 : forall t1 t2,
    t1 contains t' ->
    <{ t1; t2 }> contains t'

  | contains_seq2 : forall t1 t2,
    t2 contains t' ->
    <{ t1; t2 }> contains t'

  where "t 'contains' t'" := (Contains t' t).

Lemma contains_refl : forall t,
  t contains t.
Proof.
  intros. eauto using Contains.
Qed.

Lemma contains_trans : forall t1 t2 t3,
  t1 contains t2 ->
  t2 contains t3 ->
  t1 contains t3.
Proof.
  intros * Hcon ?. induction Hcon; subst; eauto using Contains.
Qed.

Lemma step_write_contains : forall t t' ad v Tr,
  t --[EF_Write ad v Tr]--> t' ->
  t contains v.
Proof.
  intros. induction_step; eauto using Contains.
Qed.

