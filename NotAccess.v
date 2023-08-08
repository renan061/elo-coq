From Elo Require Import Util.
From Elo Require Import Core.
From Elo Require Import Access.

Inductive not_access (ad : addr) (m : mem) : tm -> Prop :=
  | nacc_unit :
    not_access ad m <{unit}>

  | nacc_num : forall n,
    not_access ad m <{N n}>

  | nacc_ad : forall T ad',
    ad <> ad' ->
    ~ access ad m (m[ad'].tm) ->
    not_access ad m <{&ad' :: T}>

  | nacc_new : forall T t,
    ~ access ad m t ->
    not_access ad m <{new T t}>

  | nacc_load : forall t,
    ~ access ad m t ->
    not_access ad m <{*t}>

  | nacc_asg : forall t1 t2,
    ~ access ad m t1 ->
    ~ access ad m t2 ->
    not_access ad m <{t1 = t2}>

  | nacc_var : forall x,
    not_access ad m <{var x}>

  | nacc_fun : forall x Tx t,
    ~ access ad m t ->
    not_access ad m <{fn x Tx t}>

  | nacc_call : forall t1 t2,
    ~ access ad m t1 ->
    ~ access ad m t2 ->
    not_access ad m <{call t1 t2}>

  | nacc_seq : forall t1 t2,
    ~ access ad m t1 ->
    ~ access ad m t2 ->
    not_access ad m <{t1; t2}>

  | nacc_spawn : forall t,
    not_access ad m <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Theorem nacc_iff : forall m t ad,
  ~ access ad m t <-> not_access ad m t.
Proof.
  intros. split; intros Hnacc; destruct t;
  try (eapply nacc_ad
    || eapply nacc_asg
    || eapply nacc_call
    || eapply nacc_seq);
  eauto using access, not_access;
  intros ?; subst; try (inv_acc; invc Hnacc); eauto using access.
  match goal with
  | Hnacc : ~ access ?ad' _ <{& ?ad :: _}> |- _ =>
    destruct (nat_eq_dec ad ad'); subst
  end;
  eauto using access.
Qed.

Local Ltac manual_inv_nacc Hnacc :=
  eapply nacc_iff in Hnacc; inv Hnacc; eauto using access.

Local Ltac manual_invc_nacc Hnacc :=
  manual_inv_nacc; clear Hnacc.

Local Ltac match_nacc tactic :=
  match goal with
  (* irrelevant for unit  *)
  (* irrelevant for num   *)
  | H : ~ access _ _ <{& _ :: _}>   |- _ => tactic H
  | H : ~ access _ _ <{new _ _ }>   |- _ => tactic H
  | H : ~ access _ _ <{* _     }>   |- _ => tactic H
  | H : ~ access _ _ <{_ = _   }>   |- _ => tactic H
  (* irrelevant for var   *)
  | H : ~ access _ _ <{fn _ _ _}>   |- _ => tactic H
  | H : ~ access _ _ <{call _ _}>   |- _ => tactic H
  | H : ~ access _ _ <{_ ; _   }>   |- _ => tactic H
  (* irrelevant for spawn *)
  end.

Ltac inv_nacc := match_nacc manual_inv_nacc.

Ltac invc_nacc := match_nacc manual_invc_nacc.

