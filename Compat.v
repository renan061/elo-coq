From Coq Require Import Arith.Arith.

From Elo Require Import Array.
From Elo Require Import Core0.
From Elo Require Import Access.

Definition compat m m' t := forall ad,
  access m t ad ->
  getTM m ad = getTM m' ad.

Lemma compat_symmetry : forall m m' t, 
  compat m m' t ->
  compat m' m t. 
Proof.
  intros * Hcompat ad Hacc. unfold compat in *.
  induction Hacc; eauto using access;
  try solve [symmetry; eauto using access].
  eapply IHHacc. intros ? ?.
  eapply Hcompat. eapply access_mem.
  rewrite (Hcompat _ (access_loc _ _)).
  trivial.
Qed.

Local Lemma compat_access : forall m m' t ad,
  compat m m' t ->
  access m t ad ->
  access m' t ad.
Proof.
  intros * Hcompat Hacc. unfold compat in *.
  induction Hacc; eauto using access.
  eapply access_mem.
  rewrite <- (Hcompat _ (access_loc _ _)).
  eapply IHHacc. intros ? ?.
  eapply Hcompat. eauto using access.
Qed.

Lemma compat_access_symmetry : forall m m' t ad,
  compat m m' t ->
  access m t ad <-> access m' t ad.
Proof.
  intros * ?. split; eauto using compat_access, compat_symmetry.
Qed.

Lemma compat_set : forall m m' t ad v,
  compat m m' t ->
  ~ access m t ad ->
  compat m (set m' ad v) t.
Proof.
  intros * Hcompat Hnacc ad Hacc. unfold compat in *.
  induction Hacc. 
  - eapply IHHacc; eauto using access.
  - match goal with H : ~ access _ _ ?ad' |- _ => 
      destruct (Nat.eq_dec ad ad'); subst
    end.
    + exfalso. eauto using access.
    + rewrite (get_set_neq TM_Nil); eauto using access.
  - eauto using access, inversion_not_access_new.
  - eauto using access, inversion_not_access_load.
  - eapply inversion_not_access_asg in Hnacc as [? ?]. eauto using access.
  - eapply inversion_not_access_asg in Hnacc as [? ?]. eauto using access.
  - eapply inversion_not_access_seq in Hnacc as [? ?]. eauto using access.
  - eapply inversion_not_access_seq in Hnacc as [? ?]. eauto using access.
Qed.

Lemma
  access m t ad ->
  ~ access m t ad' ->
  access (set m ad' v) t ad.
Usar o de cima.
  

Def NonInterf m ths := forall tid1 tid2 ad,
  access m (get tid1) ad ->
  access m (get tid2) ad ->
  tid1 = tid2.


Lemma  noninterf_preservation
  has_type t // sí
  noninter t
  t --> t'
  noninter t'
