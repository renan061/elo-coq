From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import References.

(* ------------------------------------------------------------------------- *)
(* SafeAccess & UnsafeAccess                                                 *)
(* ------------------------------------------------------------------------- *)

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

Inductive SafeAccess (m : mem) : tm -> addr -> Prop :=
  | safe_access_mem : forall ad ad' T,
    ad <> ad' ->
    SafeAccess m m[ad'] ad ->
    SafeAccess m <{ &ad' :: T }> ad

  | safe_access_ref : forall ad T,
    SafeAccess m <{ &ad :: i&T }> ad

  | safe_access_new : forall t ad T,
    SafeAccess m t ad ->
    SafeAccess m <{ new T t }> ad

  | safe_access_load : forall t ad,
    SafeAccess m t ad ->
    SafeAccess m <{ *t }> ad

  | safe_access_asg : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m t2 ad ->
    SafeAccess m <{ t1 = t2 }> ad

  | safe_access_asg1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    ~ UnsafeAccess m t2 ad ->
    SafeAccess m <{ t1 = t2 }> ad

  | safe_access_asg2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    ~ UnsafeAccess m t1 ad ->
    SafeAccess m <{ t1 = t2 }> ad

  | safe_access_fun : forall x Tx t ad,
    SafeAccess m t ad ->
    SafeAccess m <{ fn x Tx --> t }> ad

  | safe_access_call : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m t2 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  | safe_access_call1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    ~ UnsafeAccess m t2 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  | safe_access_call2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    ~ UnsafeAccess m t1 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  | safe_access_seq : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m t2 ad ->
    SafeAccess m <{ t1; t2 }> ad

  | safe_access_seq1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    ~ UnsafeAccess m t2 ad ->
    SafeAccess m <{ t1; t2 }> ad

  | safe_access_seq2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    ~ UnsafeAccess m t1 ad ->
    SafeAccess m <{ t1; t2 }> ad
  .

Ltac inversion_sacc :=
  match goal with
  | H : SafeAccess _ <{ unit }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ (_ _)      _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ (_ _ _)    _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ (_ _ _ _)  _ |- _ => inversion_subst_clear H
  end.

Ltac inversion_uacc :=
  match goal with
  | H : UnsafeAccess _ <{ unit }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ (_ _)      _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ (_ _ _)    _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ (_ _ _ _)  _ |- _ => inversion_subst_clear H
  end.

(* ------------------------------------------------------------------------- *)
(* Properties                                                                *)
(* ------------------------------------------------------------------------- *)

Theorem safe_access_then_access : forall m t ad,
  SafeAccess m t ad ->
  access m t ad.
Proof.
  intros * H. induction H; eauto using access.
Qed.

Theorem unsafe_access_then_access : forall m t ad,
  UnsafeAccess m t ad ->
  access m t ad.
Proof.
  intros * H. induction H; eauto using access.
Qed.

Theorem safe_then_not_unsafe : forall m t ad,
  SafeAccess m t ad ->
  ~ UnsafeAccess m t ad.
Proof.
  intros * Hsacc Huacc. induction Hsacc; inversion Huacc; subst; eauto.
Qed.

Corollary unsafe_then_not_safe : forall m t ad,
  UnsafeAccess m t ad ->
  ~ SafeAccess m t ad.
Proof.
  intros * F ?. contradict F. eauto using safe_then_not_unsafe.
Qed.

Corollary not_safe_and_unsafe : forall m t ad,
  ~ (UnsafeAccess m t ad /\ SafeAccess m t ad).
Proof.
  intros * [F ?]. contradict F. eauto using safe_then_not_unsafe.
Qed.

Local Lemma length_ad' : forall m ad ad',
  ad <> ad' ->
  well_typed_memory m ->
  access m m[ad'] ad ->
  ad' < length m.
Proof.
  intros * ? ? Hacc.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; trivial;
  rewrite (get_default TM_Unit) in Hacc; try lia; inversion Hacc.
Qed.

Theorem access_to_unsafe_access : forall Gamma m t ad T,
  Gamma |-- t is T ->
  well_typed_memory m ->
  access m t ad ->
  ~ SafeAccess m t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * ? Hwtm Hacc ?.
  generalize dependent Gamma. generalize dependent T.
  induction Hacc; intros; inversion_type; eauto using UnsafeAccess;
  solve 
    [ exfalso; eauto using SafeAccess
    | assert (~ SafeAccess m t ad) by shelve; eauto using UnsafeAccess
    | assert (H1' : ~ (SafeAccess m t1 ad /\ SafeAccess m t2 ad)) by shelve;
      assert (H2' : ~ (SafeAccess m t1 ad /\ ~ UnsafeAccess m t2 ad)) by shelve;
      assert (H3' : ~ (SafeAccess m t2 ad /\ ~ UnsafeAccess m t1 ad)) by shelve;
      eapply not_and_or in H1' as [? | ?];
      eapply not_and_or in H2' as [? | H1''];
      eapply not_and_or in H3' as [? | H2''];
      try (eapply NNPP in H1'');
      try (eapply NNPP in H2'');
      eauto using UnsafeAccess
    | assert (Hlen : ad' < length m) by eauto using length_ad';
      assert (~ SafeAccess m m[ad'] ad) by eauto using SafeAccess;
      specialize (Hwtm _ Hlen) as [[? Htype'] ?]; eauto using UnsafeAccess
    ].
  Unshelve. all: intros F; destruct F; eauto using SafeAccess.
Qed.

Theorem access_to_safe_access : forall Gamma m t ad T,
  Gamma |-- t is T ->
  well_typed_memory m ->
  access m t ad ->
  ~ UnsafeAccess m t ad ->
  SafeAccess m t ad.
Proof.
  intros * ? Hwtm Hacc ?.
  generalize dependent Gamma. generalize dependent T.
  induction Hacc; intros; inversion_type; eauto using SafeAccess;
  solve 
    [ exfalso; eauto using UnsafeAccess
    | assert (~ UnsafeAccess m t ad) by shelve; eauto using SafeAccess
    | assert (~ UnsafeAccess m t1 ad) by shelve;
      assert (~ UnsafeAccess m t2 ad) by shelve;
      eauto using SafeAccess
    | assert (Hlen : ad' < length m) by eauto using length_ad';
      assert (~ UnsafeAccess m m[ad'] ad) by eauto using UnsafeAccess;
      specialize (Hwtm _ Hlen) as [[? Htype'] ?]; eauto using SafeAccess
    ].
  Unshelve. all: intros F; destruct F; eauto using UnsafeAccess.
Qed.

Corollary safe_unsafe_dec : forall Gamma m t ad T,
  well_typed_memory m ->
  Gamma |-- t is T ->
  access m t ad ->
  (SafeAccess m t ad \/ UnsafeAccess m t ad).
Proof.
  intros.
  assert (decidable (UnsafeAccess m t ad))
    as [? | ?]. { unfold decidable. eauto using excluded_middle. } (* TODO *)
  - right. assumption.
  - left. eauto using access_to_safe_access.
Qed.

