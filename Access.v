From Coq Require Logic.ClassicalFacts.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.

Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_mem : forall ad ad' T,
    access m (getTM m ad') ad ->
    access m (TM_Ref T ad') ad

  | access_loc : forall ad T,
    access m (TM_Ref T ad) ad

  | access_new : forall T t ad,
    access m t ad ->
    access m (TM_New T t) ad

  | access_load : forall t ad,
    access m t ad ->
    access m (TM_Load t) ad

  | access_asg1 : forall l r ad,
    access m l ad ->
    access m (TM_Asg l r) ad

  | access_asg2 : forall l r ad,
    access m r ad ->
    access m (TM_Asg l r) ad

  | access_fun : forall x X t ad,
    access m t ad ->
    access m (TM_Fun x X t) ad

  | access_call1 : forall t1 t2 ad,
    access m t1 ad ->
    access m (TM_Call t1 t2) ad

  | access_call2 : forall t1 t2 ad,
    access m t2 ad ->
    access m (TM_Call t1 t2) ad

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
Proof. eauto using excluded_middle. Qed.

Ltac inversion_access :=
  match goal with
  | H : access _ TM_Unit        _ |- _ => inversion H; clear H
  | H : access _ (TM_Num _)     _ |- _ => inversion H; clear H
  | H : access _ (TM_Ref _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_New _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Load _)    _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Asg _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Id _)      _ |- _ => inversion H; clear H
  | H : access _ (TM_Fun _ _ _) _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Call _ _)  _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Seq _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Spawn _)   _ |- _ => inversion H; clear H
  end.

Definition well_behaved_access (m : mem) (t : tm) :=
  forall ad, access m t ad -> ad < length m.

(* -------------------------------------------------------------------------- *)
(* not_access --------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_not_access :=
  intros; intros ?; inversion_access; eauto.

Lemma not_access_new : forall m t ad T,
  ~ access m t ad ->
  ~ access m (TM_New T t) ad.
Proof. solve_not_access. Qed.

Lemma not_access_load : forall m t ad,
  ~ access m t ad ->
  ~ access m (TM_Load t) ad.
Proof. solve_not_access. Qed.

Lemma not_access_fun : forall m x X t ad,
  ~ access m t ad ->
  ~ access m (TM_Fun x X t) ad.
Proof. solve_not_access. Qed.

Lemma not_access_call : forall m t1 t2 ad,
  ~ access m t1 ad ->
  ~ access m t2 ad ->
  ~ access m (TM_Call t1 t2) ad.
Proof. solve_not_access. Qed.

Lemma not_access_asg : forall m t1 t2 ad,
  ~ access m t1 ad ->
  ~ access m t2 ad ->
  ~ access m (TM_Asg t1 t2) ad.
Proof. solve_not_access. Qed.

Lemma not_access_seq : forall m t1 t2 ad,
  ~ access m t1 ad ->
  ~ access m t2 ad ->
  ~ access m (TM_Seq t1 t2) ad.
Proof. solve_not_access. Qed.

(* -------------------------------------------------------------------------- *)
(* inversion_not_access ----------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_inversion_not_access :=
  intros;
  match goal with
  | |- _ /\ _ => split 
  | |- _  => idtac
  end;
  intros F; inversion F; subst; eauto using access.

Local Lemma inversion_not_access_loc : forall m ad ad' T,
  ~ access m (TM_Ref T ad) ad' ->
  ~ access m (getTM m ad) ad'.
Proof. solve_inversion_not_access. Qed.

Local Lemma inversion_not_access_new : forall m t ad T,
  ~ access m (TM_New T t) ad ->
  ~ access m t ad.
Proof. solve_inversion_not_access. Qed.

Local Lemma inversion_not_access_load : forall m t ad,
  ~ access m (TM_Load t) ad ->
  ~ access m t ad.
Proof. solve_inversion_not_access. Qed.

Local Lemma inversion_not_access_asg : forall m l r ad,
  ~ access m (TM_Asg l r) ad ->
  ~ access m l ad /\ ~ access m r ad.
Proof. solve_inversion_not_access. Qed.

Local Lemma inversion_not_access_fun : forall m x X t ad,
  ~ access m (TM_Fun x X t) ad ->
  ~ access m t ad.
Proof. solve_inversion_not_access. Qed.

Local Lemma inversion_not_access_call : forall m t1 t2 ad,
  ~ access m (TM_Call t1 t2) ad ->
  ~ access m t1 ad /\ ~ access m t2 ad.
Proof. solve_inversion_not_access. Qed.

Local Lemma inversion_not_access_seq : forall m t1 t2 ad,
  ~ access m (TM_Seq t1 t2) ad ->
  ~ access m t1 ad /\ ~ access m t2 ad.
Proof. solve_inversion_not_access. Qed.

Ltac inversion_not_access :=
  match goal with
    | H : _ |- ~ access _ TM_Unit _   =>
        intros F; inversion F 
    | H : _ |- ~ access _ (TM_Num _) _   =>
        intros F; inversion F 
    | H : ~ access _ (TM_Ref _ _) _   |- _ =>
        eapply inversion_not_access_loc in H
    | H : ~ access _ (TM_New _ _) _   |- _ =>
        eapply inversion_not_access_new in H
    | H : ~ access _ (TM_Load _) _  |- _ =>
        eapply inversion_not_access_load in H
    | H : _ |- ~ access _ (TM_Id _) _   =>
        intros F; inversion F 
    | H : ~ access _ (TM_Fun _ _ _) _ |- _ =>
        eapply inversion_not_access_fun in H
    | H : ~ access _ (TM_Call _ _) _ |- _ =>
        eapply inversion_not_access_call in H as [? ?]
    | H : ~ access _ (TM_Asg _ _) _ |- _ =>
        eapply inversion_not_access_asg in H as [? ?]
    | H : ~ access _ (TM_Seq _ _) _ |- _ =>
        eapply inversion_not_access_seq in H as [? ?]
  end.

(* -------------------------------------------------------------------------- *)
(* subst -------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(*
Lemma access_subst : forall m x X t t' ad,
  access m ([x := t'] t) ad ->
  access m (TM_Call (TM_Fun x X t) t') ad.
Proof.
  intros. induction t; eauto using access; simpl in *;
  try (destruct String.eqb; eauto using access);
  try solve [ 
    inversion_access; auto_specialize;
    inversion_access; try inversion_access; eauto using access
  ].
Qed.

Lemma not_access_subst : forall m id t x ad,
  ~ access m t ad ->
  ~ access m x ad ->
  ~ access m ([id := x] t) ad.
Proof.
  intros. induction t; trivial;
  try solve [
    inversion_not_access;
    eauto using not_access_new, not_access_load, not_access_asg,
      not_access_fun, not_access_call, not_access_seq
  ];
  simpl; destruct String.eqb; trivial.
  try solve [inversion_not_access; eauto using not_access_fun].
  - shelve.
  - shelve.
Qed.
*)
