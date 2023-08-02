From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.

Inductive not_access (m : mem) : tm -> addr -> Prop :=
  | nacc_unit : forall ad,
    not_access m <{ unit }> ad

  | nacc_num : forall n ad,
    not_access m <{ N n }> ad

  | nacc_ad : forall T ad ad',
    ad <> ad' ->
    ~ access m m[ad].tm ad' ->
    not_access m <{ &ad :: T }> ad'

  | nacc_new : forall T t ad,
    ~ access m t ad ->
    not_access m <{ new T t }> ad

  | nacc_load : forall t ad,
    ~ access m t ad ->
    not_access m <{ *t }> ad

  | nacc_asg : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1 = t2 }> ad

  | nacc_var : forall x ad,
    not_access m <{ var x }> ad

  | nacc_fun : forall x Tx t ad,
    ~ access m t ad ->
    not_access m <{ fn x Tx t }> ad

  | nacc_call : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ call t1 t2 }> ad

  | nacc_seq : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1; t2 }> ad

  | nacc_spawn : forall t ad,
    not_access m <{ spawn t }> ad
  .

Theorem nacc_iff : forall m t ad,
  ~ access m t ad <-> not_access m t ad.
Proof.
  intros. split; intros Hnacc; destruct t;
  try (eapply nacc_ad
    || eapply nacc_asg
    || eapply nacc_call
    || eapply nacc_seq);
  eauto using access, not_access;
  intros ?; subst; try (inv_acc; inv_clear Hnacc); eauto using access.
  match goal with
  | Hnacc : ~ access _ <{ & ?ad :: _ }> ?ad' |- _ =>
    destruct (nat_eq_dec ad ad'); subst
  end;
  eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Ltac inv_nacc Hnacc :=
  eapply nacc_iff in Hnacc; inversion Hnacc; subst; eauto using access.
