From Coq Require Import Arith.Arith.

From Coq Require Logic.ClassicalFacts.

From Elo Require Import Array.
From Elo Require Import Core0.

Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_mem : forall ad ad',
    access m (getTM m ad') ad ->
    access m (TM_Loc ad') ad

  | access_loc : forall ad,
    access m (TM_Loc ad) ad

  | access_new : forall t ad,
    access m t ad ->
    access m (TM_New t) ad

  | access_load : forall t ad,
    access m t ad ->
    access m (TM_Load t) ad

  | access_asg1 : forall l r ad,
    access m l ad ->
    access m (TM_Asg l r) ad

  | access_asg2 : forall l r ad,
    access m r ad ->
    access m (TM_Asg l r) ad

  | access_seq1 : forall t1 t2 ad,
    access m t1 ad ->
    access m (TM_Seq t1 t2) ad

  | access_seq2 : forall t1 t2 ad,
    access m t2 ad ->
    access m (TM_Seq t1 t2) ad
  .

(* strong access_mem *)
Theorem access_get_trans : forall m t ad ad',
  access m t ad' ->
  access m (getTM m ad') ad ->
  access m t ad.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access.
Qed.

Local Axiom excluded_middle : ClassicalFacts.excluded_middle.

Lemma access_dec : forall m t ad,
  (access m t ad) \/ (~ access m t ad).
Proof.
  eauto using excluded_middle.
Qed.

Ltac inversion_access :=
  match goal with
    | H : access _ TM_Nil       _ |- _ => inversion H; clear H
    | H : access _ (TM_Num _)   _ |- _ => inversion H; clear H
    | H : access _ (TM_Loc _)   _ |- _ => inversion H; clear H
    | H : access _ (TM_New _)   _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_Load _)  _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_Asg _ _) _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_Seq _ _) _ |- _ => inversion H; subst; clear H
  end.

Lemma inversion_not_access_new : forall m t ad,
  ~ access m (TM_New t) ad ->
  ~ access m t ad.
Proof.
  intros * ? F. inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_load : forall m t ad,
  ~ access m (TM_Load t) ad ->
  ~ access m t ad.
Proof.
  intros * ? F. inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_asg : forall m l r ad,
  ~ access m (TM_Asg l r) ad ->
  ~ access m l ad /\ ~ access m r ad.
Proof.
  intros * ?. split; intros F; inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_seq : forall m t1 t2 ad,
  ~ access m (TM_Seq t1 t2) ad ->
  ~ access m t1 ad /\ ~ access m t2 ad.
Proof.
  intros * ?. split; intros F; inversion F; subst; eauto using access.
Qed.

Ltac inversion_not_access :=
  match goal with
    | H : ~ access _ (TM_New _) _   |- _ =>
        eapply inversion_not_access_new in H
    | H : ~ access _ (TM_Load _) _  |- _ =>
        eapply inversion_not_access_load in H
    | H : ~ access _ (TM_Asg _ _) _ |- _ =>
        eapply inversion_not_access_asg in H as [? ?]
    | H : ~ access _ (TM_Seq _ _) _ |- _ =>
        eapply inversion_not_access_seq in H as [? ?]
  end.

Lemma not_access_new : forall m t ad,
  ~ access m t ad ->
  ~ access m (TM_New t) ad.
Proof.
  intros * ? ?. inversion_access. eauto.
Qed.

Lemma not_access_load : forall m t ad,
  ~ access m t ad ->
  ~ access m (TM_Load t) ad.
Proof.
  intros * ? ?. inversion_access. eauto.
Qed.

Lemma not_access_asg : forall m l r ad,
  ~ access m l ad /\ ~ access m r ad ->
  ~ access m (TM_Asg l r) ad.
Proof.
  intros * [? ?] ?. inversion_access; eauto.
Qed.

Lemma not_access_seq : forall m t1 t2 ad,
  ~ access m t1 ad /\ ~ access m t2 ad ->
  ~ access m (TM_Seq t1 t2) ad.
Proof.
  intros * [? ?] ?. inversion_access; eauto.
Qed.

(* Properties of access over step. *)

Local Lemma memory_add_preserves_access : forall m t ad v,
  access m t ad ->
  access (add m v) t ad.
Proof.
  intros * Hacc. induction Hacc; eauto using access.
  eapply access_mem. destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]. 
  - rewrite (get_add_lt TM_Nil); trivial.
  - subst. rewrite (get_default TM_Nil) in IHHacc; eauto using Nat.le_refl.
    inversion_access.
  - rewrite (get_default TM_Nil) in IHHacc; eauto using Nat.lt_le_incl.
    inversion_access.
Qed.

Local Lemma memory_set_preserves_access : forall m t ad ad' v,
  ~ access m v ad ->
  access (set m ad' v) t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (set m ad' v) as m'.
  induction Hacc; inversion Heqm'; subst; eauto using access.
  match goal with 
    IH : ~ _ -> access _ (getTM (set _ ?ad1 _) ?ad2) ?ad3 |- _ =>
      destruct (Nat.eq_dec ad1 ad2); subst;
      try solve [rewrite (get_set_neq TM_Nil) in IH; eauto using access];
      destruct (Nat.eq_dec ad2 ad3); subst; eauto using access
  end.
  exfalso. rewrite (get_set_eq TM_Nil) in IHHacc; eauto.
  eapply not_le. intros F. rewrite (get_default TM_Nil) in Hacc.
  - inversion_access.
  - rewrite set_preserves_length. trivial.
Qed.

Ltac induction_step :=
  match goal with
    | H : _ --[_]--> _ |- _ => induction H
  end.

Lemma mstep_none_does_not_grant_access : forall m m' t t' ad,
  access m' t' ad ->
  m / t ==[EF_None]==> m' / t' ->
  access m t ad.
Proof.
  intros * Hacc Hmstep. inversion Hmstep; subst; clear Hmstep.
  remember EF_None as eff. induction_step; inversion Heqeff; subst;
  try inversion_access; eauto using access.
Qed.

Lemma mstep_load_does_not_grant_access : forall m m' t t' ad ad' v,
  access m' t' ad ->
  m / t ==[EF_Load ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros * Hacc Hmstep. inversion Hmstep; subst; clear Hmstep.
  remember (EF_Load ad' (getTM m' ad')) as eff. 
  induction_step; inversion Heqeff; subst;
  try inversion_access; eauto using access.
Qed.

Lemma mstep_store_does_not_grant_access : forall m m' t t' ad ad' v,
  access m' t' ad ->
  m / t ==[EF_Store ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros * Hacc Hmstep. inversion Hmstep; subst; clear Hmstep.
  remember (EF_Store ad' v) as eff. 
  induction_step; inversion Heqeff; subst;
  try inversion_access; eauto using access.
  - eapply access_asg2.
Qed.
















Lemma alloc_preserves_access : forall m m' t t' ad ad' v,
  access m t ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros * Hacc Hmstep. inversion Hmstep; subst; clear Hmstep.
  remember (EF_Alloc (length m) v) as eff.
  induction_step; inversion Heqeff; subst; inversion_access;
  eauto using access, memory_add_preserves_access.
  eapply access_mem. rewrite (get_add_eq TM_Nil).
  eauto using memory_add_preserves_access.
Qed.

Lemma when_load_preserves_access : forall m m' t t' ad ad' v,
  ad <> ad' ->
  access m t ad ->
  m / t ==[EF_Load ad' v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros * Hneq Hacc Hmstep. inversion Hmstep; subst; clear Hmstep.
  remember (EF_Load ad' (getTM m' ad')) as eff.
  induction_step; inversion Heqeff; subst; inversion_access; eauto using access.
  inversion_access; subst; trivial. exfalso. eauto.
Qed.

Lemma when_store_preserves_access : forall m m' t t' ad ad' v,
  ad <> ad' ->
  access m t ad ->
  m / t ==[EF_Store ad' v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros * Hneq Hacc Hmstep. inversion Hmstep; subst; clear Hmstep.
  remember (EF_Store ad' v) as eff.
  induction_step; inversion Heqeff; subst; inversion_access;
  eauto using access.
  - eapply access_asg2.
Abort.

(*
  | EF_Alloc (ad : addr) (t : tm)
  | EF_Load  (ad : addr) (t : tm)
  | EF_Store (ad : addr) (t : tm)
*)
