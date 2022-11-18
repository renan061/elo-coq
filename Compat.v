From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.

Definition compat m m' t := forall ad,
  access m t ad ->
  m[ad] = m'[ad].

Lemma compat_refl : forall m t, 
  compat m m t.
Proof.
  intros. unfold compat. trivial.
Qed.

Lemma compat_symmetry : forall m m' t, 
  compat m  m' t ->
  compat m' m  t. 
Proof.
  intros * Hcompat ad Hacc. unfold compat in *.
  induction Hacc; eauto using access;
  try solve [symmetry; eauto using access].
  eapply IHHacc. intros ad'' ?. eapply Hcompat.
  destruct (Nat.eq_dec ad'' ad'); subst; eauto using access.
  eapply access_mem; trivial.
  rewrite (Hcompat _ (access_ref _ _ _)).
  trivial.
Qed.

Lemma compat_access : forall m m' t ad,
  compat m m' t ->
  access m  t ad ->
  access m' t ad.
Proof.
  intros * Hcompat Hacc. unfold compat in *.
  induction Hacc; eauto using access.
  eapply access_mem; eauto using not_eq_sym.
  rewrite <- (Hcompat _ (access_ref _ _ _)).
  eapply IHHacc. intros ad'' ?.
  eapply Hcompat. destruct (Nat.eq_dec ad'' ad'); subst; eauto using access.
Qed.

Lemma compat_access_not : forall m m' t ad,
  compat m m' t ->
  ~ access m  t ad ->
  ~ access m' t ad.
Proof.
  intros * ? ? ?. eauto using compat_symmetry, compat_access.
Qed.

Corollary compat_access_iff : forall m m' t ad,
  compat m m' t ->
  access m t ad <-> access m' t ad.
Proof.
  intros * ?. split; eauto using compat_symmetry, compat_access.
Qed.

Lemma compat_nacc_set : forall m m' t ad v,
  compat m' m t ->
  ~ access m' t ad ->
  compat m' m[ad <- v] t.
Proof.
  intros * Hcompat Hnacc ad Hacc. unfold compat in *.
  induction Hacc; try solve [inversion_not_access Hnacc];
  match goal with H : ~ access _ _ ?ad' |- _ => 
    destruct (Nat.eq_dec ad ad'); subst
  end;
  try solve [exfalso; eauto using access];
  do 2 (simpl_array; eauto using access).
Qed.

Lemma compat_inaccessible_address_add : forall m m' t v,
  compat m m' t ->
  ~ access m t (length m') ->
  compat m (m' +++ v) t.
Proof.
  intros * Hcompat Hnacc ad Hacc. unfold compat in *.
  induction Hacc; try solve [inversion_not_access Hnacc; eauto using access].
  - destruct (Nat.eq_dec ad (length m')); subst.
    + exfalso. eauto using access.
    + destruct (not_eq ad (length m')); trivial;
      do 2 simpl_array; eauto using access.
      assert (Hacc' : access m <{ &ad' :: T}> ad) by eauto using access.
      specialize (Hcompat ad Hacc').
      rewrite (get_default TM_Unit m') in Hcompat; trivial; lia.
  - destruct (Nat.eq_dec ad (length m')); subst.
    + exfalso. eauto using access.
    + destruct (not_eq ad (length m')); trivial;
      simpl_array; eauto using access.
      specialize (Hcompat ad (access_ref _ _ _)).
      rewrite (get_default TM_Unit m') in Hcompat; trivial; lia.
Qed.

Corollary inaccessible_address_set_1 : forall m t ad ad' v,
  ~ access m t ad' ->
  access m[ad' <- v] t ad ->
  access m t ad.
Proof.
  intros.
  eauto using compat_refl, compat_symmetry, compat_access, compat_nacc_set.
Qed.

Corollary inaccessible_address_set_2  : forall m t ad ad' v,
  ~ access m t ad' ->
  ~ access m t ad ->
  ~ access m[ad' <- v] t ad.
Proof.
  intros.
  eauto using compat_refl, compat_access_not, compat_nacc_set.
Qed.

Corollary inaccessible_address_add_1 : forall m t ad v,
  ~ access m t (length m) ->
  access (m +++ v) t ad ->
  access m t ad.
Proof.
  intros.
  eauto using compat_refl, compat_symmetry, compat_access,
              compat_inaccessible_address_add.
Qed.

(* TODO *)
Corollary inaccessible_address_add_2 : forall m t ad v,
  ~ access m t (length m) ->
  ~ access m t ad ->
  ~ access (m +++ v) t ad.
Proof.
  intros.
  eauto using compat_refl, compat_access_not, compat_inaccessible_address_add.
Qed.

