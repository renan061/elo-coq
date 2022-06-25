From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core0.
From Elo Require Import Access.

Definition well_behaved_access m t :=
  forall ad, access m t ad -> ad < length m.

Lemma wba_destruct_new : forall m t,
  well_behaved_access m (TM_New t) ->
  well_behaved_access m t.
Proof.
  intros. unfold well_behaved_access in *. eauto using access.
Qed.

Lemma wba_destruct_load : forall m t,
  well_behaved_access m (TM_Load t) ->
  well_behaved_access m t.
Proof.
  intros. unfold well_behaved_access in *. eauto using access.
Qed.

Lemma wba_destruct_asg : forall m l r,
  well_behaved_access m (TM_Asg l r) ->
  well_behaved_access m l /\ well_behaved_access m r.
Proof.
  intros. unfold well_behaved_access in *.
  split; eauto using access.
Qed.

Lemma wba_destruct_seq : forall m t1 t2,
  well_behaved_access m (TM_Seq t1 t2) ->
  well_behaved_access m t1 /\ well_behaved_access m t2.
Proof.
  intros. unfold well_behaved_access in *.
  split; eauto using access.
Qed.

Ltac destruct_wba :=
  match goal with
    | H : well_behaved_access _ (TM_New _)   |- _ =>
        eapply wba_destruct_new in H
    | H : well_behaved_access _ (TM_Load _)  |- _ =>
        eapply wba_destruct_load in H
    | H : well_behaved_access _ (TM_Asg _ _) |- _ => 
        eapply wba_destruct_asg in H as [? ?]
    | H : well_behaved_access _ (TM_Seq _ _) |- _ => 
        eapply wba_destruct_seq in H as [? ?]
  end.

Local Lemma wba_load : forall m t,
  well_behaved_access m t ->
  well_behaved_access m (TM_Load t).
Proof.
  intros * ? ? ?. inversion_access. eauto.
Qed.

Local Lemma wba_asg : forall m l r,
  well_behaved_access m l ->
  well_behaved_access m r ->
  well_behaved_access m (TM_Asg l r).
Proof.
  intros * ? ? ? ?. inversion_access; eauto.
Qed.

Local Lemma wba_seq : forall m t1 t2,
  well_behaved_access m t1 ->
  well_behaved_access m t2 ->
  well_behaved_access m (TM_Seq t1 t2).
Proof.
  intros * ? ? ? ?. inversion_access; eauto.
Qed.

Local Lemma wba_added_value : forall m v,
  well_behaved_access (add m v) v ->
  well_behaved_access (add m v) (TM_Loc (length m)).
Proof.
  intros * ? ? Hacc.
  remember (add m v) as m'.
  remember (TM_Loc (length m)) as t'.
  induction Hacc; inversion Heqt'; subst.
  - rewrite (get_add_eq TM_Nil) in *; eauto using access.
  - rewrite add_increments_length. lia.
Qed.

Local Lemma wba_stored_value : forall m t t' ad v,
  well_behaved_access m t ->
  t --[EF_Store ad v]--> t' ->
  well_behaved_access m v.
Proof.
  intros * ? ? ? ?.
  remember (EF_Store ad v) as eff.
  induction_step; try inversion Heqeff; subst;
  destruct_wba; eauto using access. 
Qed.

Lemma wba_mem_add: forall m t v,
  well_behaved_access m t ->
  well_behaved_access (add m v) t.
Proof.
  intros * Hwba ? Hacc. remember (add m v) as m'.
  induction Hacc; subst; try destruct_wba; eauto.
  - eapply IHHacc. intros ad'' Hacc''.
    destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]; subst.
    + rewrite (get_add_lt TM_Nil) in *; eauto using access.
    + specialize (Hwba (length m) (access_loc m (length m))). lia.
    + rewrite (get_add_gt TM_Nil) in *; eauto. inversion_access.
  - rewrite add_increments_length. eauto using access, Nat.lt_lt_succ_r.
Qed.

Lemma wba_mem_set: forall m t ad v,
  well_behaved_access m t ->
  well_behaved_access m v ->
  well_behaved_access (set m ad v) t.
Proof.
  intros * ? ? ? Hacc.
  rewrite set_preserves_length.
  remember (set m ad v) as m'.
  induction Hacc; subst; try destruct_wba; eauto using access.
  eapply IHHacc. destruct (Nat.eq_dec ad ad'); subst.
  - rewrite (get_set_eq TM_Nil); eauto using access.
  - rewrite (get_set_neq TM_Nil) in *; eauto.
    intros ? ?. eauto using access.
Qed.

Local Lemma none_preservation : forall m t t',
  well_behaved_access m t ->
  t --[EF_None]--> t' ->
  well_behaved_access m t'.
Proof.
  intros. remember (EF_None) as eff.
  induction_step; inversion Heqeff; subst;
  destruct_wba; eauto using wba_load, wba_asg, wba_seq. 
Qed.

Local Lemma alloc_preservation : forall m t t' v,
  well_behaved_access m t ->
  t --[EF_Alloc (length m) v]--> t' ->
  well_behaved_access (add m v) t'.
Proof.
  intros. remember (EF_Alloc (length m) v) as eff.
  induction_step; inversion Heqeff; subst;
  destruct_wba;
  eauto using wba_load, wba_asg, wba_seq, wba_mem_add, wba_added_value. 
Qed.

Local Lemma load_preservation : forall m t t' ad,
  well_behaved_access m t ->
  t --[EF_Load ad (get TM_Nil m ad)]--> t' ->
  well_behaved_access m t'.
Proof.
  intros. remember (EF_Load ad (get TM_Nil m ad)) as eff.
  induction_step; inversion Heqeff; subst;
  destruct_wba; eauto using wba_load, wba_asg, wba_seq.
  intros ? ?. eauto using access.
Qed.

Local Lemma store_preservation : forall m t t' ad v,
  well_behaved_access m t ->
  t --[EF_Store ad v]--> t' ->
  well_behaved_access (set m ad v) t'.
Proof.
  intros.
  assert (well_behaved_access m v); eauto using wba_stored_value.
  remember (EF_Store ad v) as eff.
  induction_step; inversion Heqeff; subst;
  destruct_wba; eauto using wba_load, wba_asg, wba_seq, wba_mem_set.
  intros ? ?. inversion_access.
Qed.

Lemma wba_mstep_preservation : forall m m' t t' eff,
  well_behaved_access m t ->
  m / t ==[eff]==> m' / t' ->
  well_behaved_access m' t'.
Proof.
  intros * ? ?. inversion_mstep;
  eauto using none_preservation, 
    alloc_preservation,
    load_preservation,
    store_preservation.
Qed.

