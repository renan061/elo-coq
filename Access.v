From Coq Require Logic.ClassicalFacts.

From Elo Require Import Array.
From Elo Require Import Core0.

Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_mem : forall ad ad',
    access m (getTM m ad') ad ->
    access m (TM_Loc ad') ad

  | access_loc : forall ad,
    access m (TM_Loc ad) ad

  | access_new : forall t ad,
    access m t ad ->
    access m (TM_New t) ad

  | access_load : forall t ad,
    access m t ad ->
    access m (TM_Load t) ad

  | access_asg1 : forall l r ad,
    access m l ad ->
    access m (TM_Asg l r) ad

  | access_asg2 : forall l r ad,
    access m r ad ->
    access m (TM_Asg l r) ad

  | access_seq1 : forall t1 t2 ad,
    access m t1 ad ->
    access m (TM_Seq t1 t2) ad

  | access_seq2 : forall t1 t2 ad,
    access m t2 ad ->
    access m (TM_Seq t1 t2) ad
  .

(* strong access_mem *)
Theorem access_get_trans : forall m t ad ad',
  access m t ad' ->
  access m (getTM m ad') ad ->
  access m t ad.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access.
Qed.

Local Axiom excluded_middle : ClassicalFacts.excluded_middle.

Lemma access_dec : forall m t ad,
  (access m t ad) \/ (~ access m t ad).
Proof.
  eauto using excluded_middle.
Qed.

Ltac inversion_access :=
  match goal with
    | H : access _ TM_Nil       _ |- _ => inversion H; clear H
    | H : access _ (TM_Num _)   _ |- _ => inversion H; clear H
    | H : access _ (TM_Loc _)   _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_New _)   _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_Load _)  _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_Asg _ _) _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_Seq _ _) _ |- _ => inversion H; subst; clear H
  end.

Lemma inversion_not_access_loc : forall m ad ad',
  ~ access m (TM_Loc ad) ad' ->
  ~ access m (getTM m ad) ad'.
Proof.
  intros * ? F. inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_new : forall m t ad,
  ~ access m (TM_New t) ad ->
  ~ access m t ad.
Proof.
  intros * ? F. inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_load : forall m t ad,
  ~ access m (TM_Load t) ad ->
  ~ access m t ad.
Proof.
  intros * ? F. inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_asg : forall m l r ad,
  ~ access m (TM_Asg l r) ad ->
  ~ access m l ad /\ ~ access m r ad.
Proof.
  intros * ?. split; intros F; inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_seq : forall m t1 t2 ad,
  ~ access m (TM_Seq t1 t2) ad ->
  ~ access m t1 ad /\ ~ access m t2 ad.
Proof.
  intros * ?. split; intros F; inversion F; subst; eauto using access.
Qed.

Ltac inversion_not_access :=
  match goal with
    | H : _ |- ~ access _ TM_Nil _   =>
        intros F; inversion F 
    | H : _ |- ~ access _ (TM_Num _) _   =>
        intros F; inversion F 
    | H : ~ access _ (TM_Loc _) _   |- _ =>
        eapply inversion_not_access_loc in H
    | H : ~ access _ (TM_New _) _   |- _ =>
        eapply inversion_not_access_new in H
    | H : ~ access _ (TM_Load _) _  |- _ =>
        eapply inversion_not_access_load in H
    | H : ~ access _ (TM_Asg _ _) _ |- _ =>
        eapply inversion_not_access_asg in H as [? ?]
    | H : ~ access _ (TM_Seq _ _) _ |- _ =>
        eapply inversion_not_access_seq in H as [? ?]
  end.

Lemma not_access_new : forall m t ad,
  ~ access m t ad ->
  ~ access m (TM_New t) ad.
Proof.
  intros * ? ?. inversion_access. eauto.
Qed.

Lemma not_access_load : forall m t ad,
  ~ access m t ad ->
  ~ access m (TM_Load t) ad.
Proof.
  intros * ? ?. inversion_access. eauto.
Qed.

Lemma not_access_asg : forall m l r ad,
  ~ access m l ad ->
  ~ access m r ad ->
  ~ access m (TM_Asg l r) ad.
Proof.
  intros * ? ? ?. inversion_access; eauto.
Qed.

Lemma not_access_seq : forall m t1 t2 ad,
  ~ access m t1 ad ->
  ~ access m t2 ad ->
  ~ access m (TM_Seq t1 t2) ad.
Proof.
  intros * ? ? ?. inversion_access; eauto.
Qed.

