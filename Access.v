From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.

(* A term accesses an address if it refers to the address directly or 
indirectly. *)
Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_mem : forall ad ad' T,
    ad <> ad' ->
    access m m[ad'].tm ad ->
    access m <{ &ad' :: T }> ad

  | access_ref : forall ad T,
    access m <{ &ad :: T }> ad

  | access_new : forall T t ad,
    access m t ad ->
    access m <{ new T t }> ad

  | access_load : forall t ad,
    access m t ad ->
    access m <{ *t }> ad

  | access_asg1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ t1 = t2 }> ad

  | access_asg2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ t1 = t2 }> ad

  | access_fun : forall x Tx t ad,
    access m t ad ->
    access m <{ fn x Tx --> t }> ad

  | access_call1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ call t1 t2 }> ad

  | access_call2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ call t1 t2 }> ad

  | access_seq1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ t1; t2 }> ad

  | access_seq2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ t1; t2 }> ad
  .

(* strong access_mem *)
Theorem access_get_trans : forall m t ad ad',
  ad <> ad' ->
  access m t ad' ->
  access m m[ad'].tm ad ->
  access m t ad.
Proof.
  intros * ? Hacc ?. induction Hacc; eauto using access.
  destruct (Nat.eq_dec ad ad'); subst; eauto using access.
Qed.

Ltac inversion_access :=
  match goal with
  | H : access _ memory_default _ |- _ => inversion H; clear H
  | H : access _ thread_default _ |- _ => inversion H; clear H
  | H : access _ TM_Unit        _ |- _ => inversion H; clear H
  | H : access _ (TM_Num _)     _ |- _ => inversion H; clear H
  | H : access _ (TM_Ref _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_New _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Load _)    _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Asg _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Var _)     _ |- _ => inversion H; clear H
  | H : access _ (TM_Fun _ _ _) _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Call _ _)  _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Seq _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Spawn _)   _ |- _ => inversion H; clear H
  end.

Lemma access_length : forall m ad ad',
  access m m[ad'].tm ad ->
  ad' < length m.
Proof.
  intros * Hacc.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; trivial;
  simpl_array; try lia; inversion Hacc.
Qed.

Lemma access_dec : forall m t ad,
  Decidable.decidable (access m t ad).
Proof. eauto using classic_decidable. Qed.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Inductive not_access (m : mem) : tm -> addr -> Prop :=
  | not_access_unit : forall ad,
    not_access m <{ unit }> ad

  | not_access_num : forall n ad,
    not_access m <{ N n }> ad

  | not_access_ref : forall T ad ad',
    ad <> ad' ->
    ~ access m m[ad].tm ad' ->
    not_access m <{ &ad :: T }> ad'

  | not_access_new : forall T t ad,
    ~ access m t ad ->
    not_access m <{ new T t }> ad

  | not_access_load : forall t ad,
    ~ access m t ad ->
    not_access m <{ *t }> ad

  | not_access_asg : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1 = t2 }> ad

  | not_access_var : forall x ad,
    not_access m <{ var x }> ad

  | not_access_fun : forall x Tx t ad,
    ~ access m t ad ->
    not_access m <{ fn x Tx --> t }> ad

  | not_access_call : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ call t1 t2 }> ad

  | not_access_seq : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1; t2 }> ad

  | not_access_spawn : forall t ad,
    not_access m <{ spawn t }> ad
  .

Theorem not_access_iff : forall m t ad,
  ~ access m t ad <-> not_access m t ad.
Proof.
  intros. split; intros Hnacc; destruct t;
  try (eapply not_access_ref
    || eapply not_access_asg
    || eapply not_access_call
    || eapply not_access_seq);
  eauto using access, not_access;
  intros ?; subst;
  try (inversion_access; inversion_clear Hnacc); eauto using access.
  match goal with
  | Hnacc : ~ access _ <{ & ?ad :: _ }> ?ad' |- _ =>
    destruct (Nat.eq_dec ad ad'); subst; eauto using access
  end.
Qed.

Ltac inversion_not_access H :=
  eapply not_access_iff in H; inversion H; subst; eauto using access.

(* ------------------------------------------------------------------------- *)
(* access-subst * not-access-subst                                           *)
(* ------------------------------------------------------------------------- *)

Lemma access_subst : forall m x Tx t t' ad,
  access m ([x := t'] t) ad ->
  access m <{ call <{ fn x Tx --> t }> t' }> ad.
Proof.
  intros. induction t; eauto using access; simpl in *;
  try (destruct String.string_dec; eauto using access);
  try solve [ 
    inversion_access; auto_specialize;
    inversion_access; try inversion_access; eauto using access
  ].
Qed.

Lemma not_access_subst : forall m t tx ad x,
  ~ access m t ad ->
  ~ access m tx ad ->
  ~ access m ([x := tx] t) ad.
Proof.
  intros * Hnacc ?.
  generalize dependent tx.
  induction t; intros; trivial; simpl;
  try solve [
    eapply not_access_iff;
    inversion_not_access Hnacc; eauto using not_access
  ];
  destruct String.string_dec; trivial.
  inversion_not_access Hnacc. eapply not_access_iff. eauto using not_access.
Qed.

Lemma not_access_subst_fun : forall m t tx ad x Tx,
  ~ access m <{ fn x Tx --> t }> ad ->
  ~ access m tx ad ->
  ~ access m ([x := tx] t) ad.
Proof.
  intros * Hnacc ?. inversion_not_access Hnacc; eauto using not_access_subst.
Qed.

