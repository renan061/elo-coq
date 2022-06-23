From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core0.
From Elo Require Import Access.

Module Compat.
  Definition compat m m' t := forall ad,
    access m t ad ->
    getTM m ad = getTM m' ad.

  Lemma refl : forall m t, 
    compat m m t.
  Proof.
    intros. unfold compat. trivial.
  Qed.

  Lemma sym : forall m m' t, 
    compat m  m' t ->
    compat m' m  t. 
  Proof.
    intros * Hcompat ad Hacc. unfold compat in *.
    induction Hacc; eauto using access;
    try solve [symmetry; eauto using access].
    eapply IHHacc. intros ? ?.
    eapply Hcompat. eapply access_mem.
    rewrite (Hcompat _ (access_loc _ _)).
    trivial.
  Qed.

  Lemma acc : forall m m' t ad,
    compat m m' t ->
    access m  t ad ->
    access m' t ad.
  Proof.
    intros * Hcompat Hacc. unfold compat in *.
    induction Hacc; eauto using access.
    eapply access_mem.
    rewrite <- (Hcompat _ (access_loc _ _)).
    eapply IHHacc. intros ? ?.
    eapply Hcompat. eauto using access.
  Qed.

  Lemma acc_not : forall m m' t ad,
    compat m m' t ->
    ~ access m  t ad ->
    ~ access m' t ad.
  Proof.
    intros * ? ? ?. eauto using acc, sym.
  Qed.

  Corollary access_iff : forall m m' t ad,
    compat m m' t ->
    access m t ad <-> access m' t ad.
  Proof.
    intros * ?. split; eauto using acc, sym.
  Qed.

  Lemma inaccessible_address_set : forall m m' t ad v,
    compat m m' t ->
    ~ access m t ad ->
    compat m (set m' ad v) t.
  Proof.
    intros * Hcompat Hnacc ad Hacc. unfold compat in *.
    induction Hacc; try solve [inversion_not_access; eauto using access].
    match goal with H : ~ access _ _ ?ad' |- _ => 
      destruct (Nat.eq_dec ad ad'); subst
    end.
    - exfalso. eauto using access.
    - rewrite (get_set_neq TM_Nil); eauto using access.
  Qed.

  Lemma inaccessible_address_add : forall m m' t v,
    compat m m' t ->
    ~ access m t (length m') ->
    compat m (add m' v) t.
  Proof.
    intros * Hcompat Hnacc ad Hacc. unfold compat in *.
    induction Hacc; try solve [inversion_not_access; eauto using access].
    destruct (Nat.eq_dec ad (length m')); subst.
    + exfalso. eauto using access.
    + destruct (not_eq ad (length m')); trivial.
      * rewrite (get_add_lt TM_Nil); eauto using access.
      * specialize (Hcompat ad (access_loc m ad)).
        rewrite (get_default TM_Nil m') in Hcompat; try lia.
        rewrite (get_add_gt TM_Nil); trivial.
  Qed.
End Compat.

(*
  Changing the contents of an inaccessible
  address does not interfere with access.
*)
Lemma access_inaccessible_address : forall m t ad ad' v,
  ~ access m t ad' ->
  access (set m ad' v) t ad ->
  access m t ad.
Proof.
  intros * ? ?.
  eauto using Compat.refl,
              Compat.sym,
              Compat.inaccessible_address_set,
              Compat.acc.
Qed.

(*
  Changing the contents of an inaccessible
  address does not interfere with access.
*)
Lemma not_access_inaccessible_address  : forall m t ad ad' v,
  ~ access m t ad ->
  ~ access m t ad' ->
  ~ access (set m ad' v) t ad.
Proof.
  intros * Hnacc Hnacc'.
  eauto using Compat.refl, Compat.inaccessible_address_set, Compat.acc_not.
Qed.

Lemma inaccessible_address_add_1 : forall m t ad v,
  ~ access m t (length m) ->
  access (add m v) t ad ->
  access m t ad.
Proof.
  intros * ? ?.
  eauto using Compat.refl,
              Compat.sym,
              Compat.inaccessible_address_add,
              Compat.acc.
Qed.

Lemma inaccessible_address_add_2 : forall m t ad v,
  ~ access m t ad ->
  ~ access m t (length m) ->
  ~ access (add m v) t ad.
Proof.
  intros * Hnacc Hnacc'.
  eauto using Compat.refl, Compat.inaccessible_address_add, Compat.acc_not.
Qed.

Definition disjoint_memory m ths := forall tid1 tid2 ad,
  access m (getTM ths tid1) ad ->
  tid1 <> tid2 ->
  ~ access m (getTM ths tid2) ad.

Theorem disjoint_memory_preservation : forall m m' ths t' tid eff,
  disjoint_memory m ths ->
  tid < length ths ->
  m / (getTM ths tid) ==[eff]==> m' / t' ->
  disjoint_memory m' (set ths tid t').
Proof.
  intros * Hdis ? Hmstep tid1 tid2 ad' Hacc Hneq. inversion Hmstep; subst.
  - destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
    + rewrite (get_set_neq TM_Nil);
      rewrite (get_set_eq TM_Nil) in *;
      eauto using MStep.None.inherits_access.
    + rewrite (get_set_eq TM_Nil);
      rewrite (get_set_neq TM_Nil) in *;
      eauto using MStep.None.preserves_not_access.
    + rewrite (get_set_neq TM_Nil) in *; eauto.
  - destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto;
    (rewrite (get_set_eq TM_Nil) || rewrite (get_set_neq TM_Nil));
    (rewrite (get_set_eq TM_Nil) in * || rewrite (get_set_neq TM_Nil) in *);
    eauto 8 using inaccessible_address_add_1,
                  inaccessible_address_add_2.
    + specialize (Hdis tid1 tid2 ad') as Hdis1.
      eapply inaccessible_address_add_2.
    + admit.
    + admit.
  - destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
    + rewrite (get_set_neq TM_Nil);
      rewrite (get_set_eq TM_Nil) in *;
      eauto using MStep.Load.inherits_access.
    + rewrite (get_set_eq TM_Nil);
      rewrite (get_set_neq TM_Nil) in *;
      eauto using MStep.Load.preserves_not_access.
    + rewrite (get_set_neq TM_Nil) in *; eauto.
  - destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto;
    (rewrite (get_set_eq TM_Nil) || rewrite (get_set_neq TM_Nil));
    (rewrite (get_set_eq TM_Nil) in * || rewrite (get_set_neq TM_Nil) in *);
    eauto 8 using Step.Store.address_access,
                  Step.store_access_backwards,
                  Step.store_does_not_grant_access1,
                  access_inaccessible_address,
                  not_access_inaccessible_address.
Qed.

