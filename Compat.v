From Coq Require Import Arith.Arith.

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

  Corollary access_symmetry : forall m m' t ad,
    compat m m' t ->
    access m t ad <-> access m' t ad.
  Proof.
    intros * ?. split; eauto using acc, sym.
  Qed.

  Lemma inaccessible_address : forall m m' t ad v,
    compat m m' t ->
    ~ access m t ad ->
    compat m (set m' ad v) t.
  Proof.
    intros * Hcompat Hnacc ad Hacc. unfold compat in *.
    induction Hacc; try solve [inversion_not_access; eauto using access].
    - eapply IHHacc; eauto using access.
    - match goal with H : ~ access _ _ ?ad' |- _ => 
        destruct (Nat.eq_dec ad ad'); subst
      end.
      + exfalso. eauto using access.
      + rewrite (get_set_neq TM_Nil); eauto using access.
  Qed.
End Compat.

(* changing an inaccessible address does not interfere with access *)
(* TODO: maybe remove this one. *)
Lemma access_inaccessible_address1 : forall m t ad ad' v,
  access m t ad ->
  ~ access m t ad' ->
  access (set m ad' v) t ad.
Proof.
  intros * ? ?.
  eauto using Compat.refl, Compat.inaccessible_address, Compat.acc.
Qed.

Lemma access_inaccessible_address2 : forall m t ad ad' v,
  ~ access m t ad' ->
  access (set m ad' v) t ad ->
  access m t ad.
Proof.
  intros * ? ?.
  eauto using Compat.refl, Compat.sym, Compat.inaccessible_address, Compat.acc.
Qed.

Lemma access_inaccessible_address3 : forall m t ad ad' v,
  ~ access m t ad ->
  ~ access m t ad' ->
  ~ access (set m ad' v) t ad.
Proof.
  intros * Hnacc Hnacc'.
  eauto using Compat.refl, Compat.inaccessible_address, Compat.acc_not.
Qed.

Definition disjoint_memory m ths := forall tid1 tid2 ad,
  access m (getTM ths tid1) ad ->
  tid1 <> tid2 ->
  ~ access m (getTM ths tid2) ad.

Theorem disjoint_memory_preservation' : forall m m' ths ths' tid eff,
  (forall block, eff <> EF_Spawn block) ->
  disjoint_memory m ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  disjoint_memory m' ths'.
Proof.
  intros * Hspawn Hdis Hcstep tid1 tid2 ad' Hacc Hneq.
  inversion Hcstep; subst.
  - clear Hcstep; inversion H1; subst.
    + admit.
    + admit.
    + admit.
    + destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto;
      (rewrite (get_set_eq TM_Nil) || rewrite (get_set_neq TM_Nil));
      (rewrite (get_set_eq TM_Nil) in * || rewrite (get_set_neq TM_Nil) in *);
      eauto 8 using Step.store_ad_access,
                    Step.store_access_backwards,
                    Step.store_does_not_grant_access1,
                    access_inaccessible_address2,
                    access_inaccessible_address3.
  - exfalso. eapply Hspawn. trivial.
Qed.

Theorem disjoint_memory_preservation : forall m m' ths ths' tid eff,
  disjoint_memory m ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  disjoint_memory m' ths'.
Proof.
  intros * Hdis Hcstep tid1 tid2 ad Hacc1 Hacc2.
  specialize (Hdis tid1 tid2 ad) as Hdis'.
  inversion Hcstep; subst.
  - clear Hcstep; inversion H1; subst.
    + destruct (Nat.eq_dec tid tid1) as [? | Hneq]; 
      destruct (Nat.eq_dec tid tid2);
      subst; trivial.
      * rewrite (get_set_eq TM_Nil) in Hacc1;
        rewrite (get_set_neq TM_Nil) in Hacc2;
        eauto using mstep_none_does_not_grant_access.
      * rewrite (get_set_eq TM_Nil) in Hacc2;
        rewrite (get_set_neq TM_Nil) in Hacc1;
        eauto using mstep_none_does_not_grant_access.
      * rewrite (get_set_neq TM_Nil) in *; eauto.
    + admit.
    + destruct (Nat.eq_dec tid tid1) as [? | Hneq]; 
      destruct (Nat.eq_dec tid tid2);
      subst; trivial.
      * rewrite (get_set_eq TM_Nil) in Hacc1;
        rewrite (get_set_neq TM_Nil) in Hacc2;
        eauto using mstep_load_does_not_grant_access.
      * rewrite (get_set_eq TM_Nil) in Hacc2;
        rewrite (get_set_neq TM_Nil) in Hacc1;
        eauto using mstep_load_does_not_grant_access.
      * rewrite (get_set_neq TM_Nil) in *; eauto.
    + destruct (Nat.eq_dec tid tid1) as [? | Hneq]; 
      destruct (Nat.eq_dec tid tid2);
      subst; trivial.
      * rewrite (get_set_eq TM_Nil) in Hacc1;
        rewrite (get_set_neq TM_Nil) in Hacc2; eauto.
        
      * exfalso.
        eapply not_eq_sym in Hneq.
        rewrite (get_set_eq TM_Nil) in Hacc2;
        rewrite (get_set_neq TM_Nil) in Hacc1;
        eauto using mstep_load_does_not_grant_access. admit.
      * rewrite (get_set_neq TM_Nil) in *; eauto. admit.
  - admit.
Qed.

