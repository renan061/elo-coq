From Coq Require Import Arith.

From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.

Inductive SafeAccess (m : mem) : tm -> addr -> Prop :=
  | safe_access_mem : forall ad ad' T,
    ad <> ad' ->
    SafeAccess m m[ad'] ad ->
    SafeAccess m <{ &ad' :: T }> ad

  | safe_access_ref : forall ad T,
    SafeAccess m <{ &ad :: i&T }> ad

  | safe_access_new : forall T t ad,
    SafeAccess m t ad ->
    SafeAccess m <{ new T t }> ad

  | safe_access_load : forall t ad,
    SafeAccess m t ad ->
    SafeAccess m <{ *t }> ad

  | safe_access_asg1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m <{ t1 = t2 }> ad

  | safe_access_asg2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    SafeAccess m <{ t1 = t2 }> ad

  | safe_access_fun : forall x Tx t ad,
    SafeAccess m t ad ->
    SafeAccess m <{ fn x Tx --> t }> ad

  | safe_access_call1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  | safe_access_call2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  | safe_access_seq1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m <{ t1; t2 }> ad

  | safe_access_seq2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    SafeAccess m <{ t1; t2 }> ad
  .

Inductive UnsafeAccess (m : mem) : tm -> addr -> Prop :=
  | unsafe_access_mem : forall ad ad' T,
    ad <> ad' ->
    UnsafeAccess m m[ad'] ad ->
    UnsafeAccess m <{ &ad' :: T }> ad

  | unsafe_access_ref : forall ad T,
    UnsafeAccess m <{ &ad :: &T }> ad

  | unsafe_access_new : forall T t ad,
    UnsafeAccess m t ad ->
    UnsafeAccess m <{ new T t }> ad

  | unsafe_access_load : forall t ad,
    UnsafeAccess m t ad ->
    UnsafeAccess m <{ *t }> ad

  | unsafe_access_asg1 : forall t1 t2 ad,
    UnsafeAccess m t1 ad ->
    UnsafeAccess m <{ t1 = t2 }> ad

  | unsafe_access_asg2 : forall t1 t2 ad,
    UnsafeAccess m t2 ad ->
    UnsafeAccess m <{ t1 = t2 }> ad

  | unsafe_access_fun : forall x Tx t ad,
    UnsafeAccess m t ad ->
    UnsafeAccess m <{ fn x Tx --> t }> ad

  | unsafe_access_call1 : forall t1 t2 ad,
    UnsafeAccess m t1 ad ->
    UnsafeAccess m <{ call t1 t2 }> ad

  | unsafe_access_call2 : forall t1 t2 ad,
    UnsafeAccess m t2 ad ->
    UnsafeAccess m <{ call t1 t2 }> ad

  | unsafe_access_seq1 : forall t1 t2 ad,
    UnsafeAccess m t1 ad ->
    UnsafeAccess m <{ t1; t2 }> ad

  | unsafe_access_seq2 : forall t1 t2 ad,
    UnsafeAccess m t2 ad ->
    UnsafeAccess m <{ t1; t2 }> ad
  .

Theorem safe_access_then_access : forall m t ad,
  SafeAccess m t ad ->
  access m t ad.
Proof.
  intros * Hsacc. induction Hsacc; eauto using access.
Qed.

Theorem unsafe_access_then_access : forall m t ad,
  UnsafeAccess m t ad ->
  access m t ad.
Proof.
  intros * Huacc. induction Huacc; eauto using access.
Qed.

Theorem access_then_safe_or_unsafe_access : forall Gamma m t ad T,
  Gamma |-- t is T ->
  access m t ad ->
  (SafeAccess m t ad \/ UnsafeAccess m t ad).
Proof.
  intros * Htype Hacc. generalize dependent Gamma. generalize dependent T.
  induction Hacc; intros; inversion Htype; subst;
  try (
    match goal with
    | H  : _ |-- ?t is _,
      IH : forall _ _, _ |-- ?t is _ -> _ \/ _
      |- _ =>
      specialize (IH _ _ H) as [? | ?]
    end
  );
  try solve
    [ left; eauto using SafeAccess
    | right; eauto using UnsafeAccess
    ].
  - right. destruct (Nat.eq_dec ad ad'); subst; eauto using UnsafeAccess.
    eapply unsafe_access_mem; trivial.
    admit.
  - left.
    admit.
Qed.





