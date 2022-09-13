From Coq Require Logic.ClassicalFacts.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.

Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_mem : forall ad ad' T,
    access m m[ad'] ad ->
    access m <{ & ad' :: T }> ad

  | access_ref : forall ad T,
    access m <{ & ad :: T }> ad

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
  access m t ad' ->
  access m m[ad'] ad ->
  access m t ad.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access.
Qed.

Local Axiom excluded_middle : ClassicalFacts.excluded_middle.

Lemma access_dec : forall m t ad,
  (access m t ad) \/ (~ access m t ad).
Proof. eauto using excluded_middle. Qed.

Ltac inversion_access :=
  match goal with
  | H : access _ TM_Unit        _ |- _ => inversion H; clear H
  | H : access _ (TM_Num _)     _ |- _ => inversion H; clear H
  | H : access _ (TM_Ref _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_New _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Load _)    _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Asg _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Id _)      _ |- _ => inversion H; clear H
  | H : access _ (TM_Fun _ _ _) _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Call _ _)  _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Seq _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Spawn _)   _ |- _ => inversion H; clear H
  end.

Definition well_behaved_access (m : mem) (t : tm) :=
  forall ad, access m t ad -> ad < length m.

(* ------------------------------------------------------------------------- *)
(* not_access                                                                *)
(* ------------------------------------------------------------------------- *)

Inductive not_access (m : mem) : tm -> addr -> Prop :=
  | not_access_unit : forall ad,
    not_access m <{ unit }> ad

  | not_access_num : forall n ad,
    not_access m <{ N n }> ad

  | not_access_ref : forall T ad ad',
    ad <> ad' ->
    ~ access m m[ad] ad' ->
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

  | not_access_id : forall x ad,
    not_access m <{ ID x }> ad

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
  intros. split; intros H; destruct t;
  try ( eapply not_access_ref
       || eapply not_access_asg
       || eapply not_access_call
       || eapply not_access_seq);
  eauto using access, not_access;
  intros ?; subst;
  try (inversion_access; inversion_clear H);
  eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* subst                                                                     *)
(* ------------------------------------------------------------------------- *)

(*
Lemma access_subst : forall m x X t t' ad,
  access m ([x := t'] t) ad ->
  access m (TM_Call (TM_Fun x X t) t') ad.
Proof.
  intros. induction t; eauto using access; simpl in *;
  try (destruct String.eqb; eauto using access);
  try solve [ 
    inversion_access; auto_specialize;
    inversion_access; try inversion_access; eauto using access
  ].
Qed.

Lemma not_access_subst : forall m id t x ad,
  ~ access m t ad ->
  ~ access m x ad ->
  ~ access m ([id := x] t) ad.
Proof.
  intros. induction t; trivial;
  try solve [
    inversion_not_access;
    eauto using not_access_new, not_access_load, not_access_asg,
      not_access_fun, not_access_call, not_access_seq
  ];
  simpl; destruct String.eqb; trivial.
  try solve [inversion_not_access; eauto using not_access_fun].
  - shelve.
  - shelve.
Qed.
*)
