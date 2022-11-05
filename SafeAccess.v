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

Corollary not_access_then_not_safe_access : forall m t ad,
  ~ access m t ad ->
  SafeAccess m t ad ->
  False.
Proof.
  intros. eauto using safe_access_then_access.
Qed.

Corollary not_access_then_not_unsafe_access : forall m t ad,
  ~ access m t ad ->
  UnsafeAccess m t ad ->
  False.
Proof.
  intros. eauto using unsafe_access_then_access.
Qed.

Theorem safe_then_not_unsafe : forall m t ad,
  SafeAccess m t ad ->
  UnsafeAccess m t ad ->
  False.
Proof.
  intros * Hsacc Huacc. induction Hsacc;
  inversion Huacc; subst; eauto;
  try solve [eapply not_access_then_not_unsafe_access; eauto].
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

Lemma safe_access_dec : forall m t ad,
  (SafeAccess m t ad) \/ (~ SafeAccess m t ad).
Proof. eauto using excluded_middle. Qed.

Lemma unsafe_access_dec : forall m t ad,
  (UnsafeAccess m t ad) \/ (~ UnsafeAccess m t ad).
Proof. eauto using excluded_middle. Qed.

From Coq Require Import Logic.Classical_Prop.

Lemma todo : forall m t1 t2 ad,
  ~ SafeAccess m <{ t1 = t2 }> ad ->
  ~
  (~ SafeAccess m t1 ad \/ ~ SafeAccess m t2 ad) /\ 
  (~ SafeAccess m t1 ad \/ UnsafeAccess m t2 ad) /\
  (~ SafeAccess m t2 ad \/ UnsafeAccess m t1 ad).
Proof.
  intros. split.
  - intros F. eapply or_not_and in F.
    eapply H; clear F. eauto using SafeAccess.
  - split.
    + intros [? ?]. eapply H; clear H. eauto using SafeAccess.
    + intros [? ?]. eapply H; clear H. eauto using SafeAccess.
Qed.

Theorem access_then_safe_or_unsafe_access : forall Gamma m t ad T,
  Gamma |-- t is T ->
  well_typed_memory m ->
  access m t ad ->
  ~ SafeAccess m t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * Htype Hwtm Hacc Hnsacc.
  generalize dependent Gamma. generalize dependent T.
  induction Hacc; intros; inversion_type; eauto using UnsafeAccess;
  try solve [
    assert (~ SafeAccess m t ad) by shelve;
    eauto using UnsafeAccess
  ];
  try solve [
    assert (
      (~ SafeAccess m t1 ad /\ ~ SafeAccess m t2 ad) \/
      (~ SafeAccess m t1 ad /\ UnsafeAccess m t2 ad) \/
      (~ SafeAccess m t2 ad /\ UnsafeAccess m t1 ad)
    ) as [[? ?] | [[? ?] | [? ?]]] by shelve;
    eauto using UnsafeAccess
  ].
  - eapply unsafe_access_mem; trivial.
    assert (H' : forall ad ad',
      ad' <> ad ->
      ~ SafeAccess m <{ & ad :: (& T1) }> ad' ->
      ~ SafeAccess m m[ad] ad'
    ). {
      intros. eauto using SafeAccess.
    }
    eapply H' in Hnsacc; trivial; clear H'.
    auto_specialize; clear Hnsacc.
    assert (Hlen : ad' < length m) by shelve.
    specialize (Hwtm _ Hlen) as [[? Htype'] ?].
    eauto.
  - eapply unsafe_access_mem; trivial.
    assert (H' : forall ad ad',
      ad' <> ad ->
      ~ SafeAccess m <{ & ad :: (i& T1) }> ad' ->
      ~ SafeAccess m m[ad] ad'
    ). {
      intros. eauto using SafeAccess.
    }
    eapply H' in Hnsacc; trivial; clear H'.
    auto_specialize; clear Hnsacc.
    assert (Hlen : ad' < length m) by shelve.
    specialize (Hwtm _ Hlen) as [[? Htype'] ?].
    eauto.
  - exfalso. eauto using SafeAccess.

  Unshelve.
  all: try solve [intros ?; eapply Hnsacc; eauto using SafeAccess].
  all: try solve [
    decompose sum (lt_eq_lt_dec ad' (length m)); subst; trivial;
    rewrite (get_default TM_Unit) in Hacc; try lia; inversion Hacc
  ].
  + (* TODO: extrait o não implicito dos "or"s (ou reformular) *)
Qed.
















Theorem access_then_safe_or_unsafe_access : forall Gamma m t ad T,
  well_typed_memory m ->
  Gamma |-- t is T ->
  access m t ad ->
  (SafeAccess m t ad \/ UnsafeAccess m t ad).
Proof.
  intros * Hwtm Htype Hacc.
  generalize dependent Gamma. generalize dependent T.
  induction Hacc; intros; inversion Htype; subst;
  try match goal with
  | H  : _ |-- _ is _, IH : forall _, _ |- _ =>
    destruct(IH _ _ H) as [? | ?]
  end;
  try solve [left; eauto using SafeAccess | right; eauto using UnsafeAccess].
  - admit.
  - admit.
  - assert (SafeAccess m t2 ad \/ ~ SafeAccess m t2 ad)
      as [? | ?] by eauto using safe_access_dec.
    + left. eauto using SafeAccess.
    + assert (access m t2 ad \/ ~ access m t2 ad)
      as [? | ?] by eauto using access_dec.
      * right. eapply unsafe_access_asg2.

  assert (Hlen : ad' < length m) by shelve;
  specialize (Hwtm _ Hlen) as [[? Htype'] ?];
  specialize (IHHacc _ empty Htype') as [? | ?];
  destruct (Nat.eq_dec ad ad'); subst;
  eauto using SafeAccess, UnsafeAccess.
  Unshelve. all:
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; trivial;
  rewrite (get_default TM_Unit) in Hacc; try lia; inversion Hacc.
Qed.

Theorem not_safe_and_unsafe : forall m t ad,
  SafeAccess m t ad ->
  UnsafeAccess m t ad ->
  False.
Proof.
  intros * Hsacc Huacc. induction Hsacc;
  inversion Huacc; subst; eauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.

