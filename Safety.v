From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core0.

Reserved Notation "m / t '==[' tc ']==>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_mem : forall t ad ad',
    get_tm m ad' = t ->
    access m t ad ->
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
  .

Lemma new_access : forall m t ad,
  access m (TM_New t) ad ->
  access m t ad.
Proof.
  intros * Hacc. remember (TM_New t) as t'.
  induction Hacc; inversion Heqt'; subst; eauto using access.
Qed.

Lemma load_access : forall m t ad,
  access m (TM_Load t) ad ->
  access m t ad.
Proof.
  intros * Hacc. remember (TM_Load t) as t'.
  induction Hacc; inversion Heqt'; subst; eauto using access.
Qed.

Lemma asg_access : forall m l r ad,
  access m (TM_Asg l r) ad ->
  access m l ad \/ access m r ad.
Proof.
  intros * Hacc. remember (TM_Asg l r) as t.
  induction Hacc; inversion Heqt; subst; eauto.
Qed.

Definition trace := list effect.

(* reflexive transitive closure *)
Inductive multistep : mem -> tm -> trace -> mem -> tm -> Prop :=
  | multistep_refl: forall m t,
      m / t ==[nil]==>* m / t

  | multistep_trans : forall m m' m'' t t' t'' tc eff,
    m  / t  ==[tc]==>* m'  / t'  ->
    m' / t' ==[eff]==> m'' / t'' ->
    m  / t  ==[eff :: tc]==>* m'' / t''

  where "m / t '==[' tc ']==>*' m' / t'" := (multistep m t tc m' t').

(* PART 1 *)

Lemma monotonic_nondecreasing_memory_length: forall m m' eff t t',
  m / t ==[eff]==>* m' / t' ->
  length m <= length m'.
Proof.
  assert (forall m m' eff t t',
    m / t ==[eff]==> m' / t' ->
    length m <= length m').
  {
    intros * Hmstep. inversion Hmstep; subst;
    try (rewrite <- Array.set_preserves_length);
    eauto using Nat.lt_le_incl, Array.length_lt_add.
  }
  intros * Hmultistep. induction Hmultistep; eauto using Nat.le_trans.
Qed.

Lemma alloc_increments_memory_length : forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  length m' = S (length m).
Proof.
  intros * Hmstep. inversion Hmstep; subst. eauto using length_add.
Qed.

Lemma destruct_multistep : forall tc eff m0 mF t0 tF,
  m0 / t0  ==[tc ++ eff :: nil]==>* mF / tF ->
  (exists m t, m0 / t0 ==[eff]==> m / t /\ m / t ==[tc]==>* mF / tF).
Proof.
  intros ?. induction tc as [| eff tc IH];
  intros * Hmultistep; inversion Hmultistep; subst.
  - eexists. eexists. inversion H3; subst. split; eauto using multistep.
  - specialize (IH _ _ _ _ _ H3) as [? [? [? ?]]].
    eexists. eexists. split; eauto using multistep.
Qed.

Theorem duplicate_alloc : forall m m' t t' tc ad v v',
  ~ (m / t ==[EF_Alloc ad v :: tc ++ EF_Alloc ad v' :: nil]==>* m' / t').
Proof.
  assert (not_Sn_le_n : forall n, ~ (S n <= n)). {
    unfold not. intros * F. induction n;
    eauto using le_S_n. inversion F.
  }
  unfold not. intros * Hmultistep.
  inversion Hmultistep; subst; clear Hmultistep;
  destruct tc; try discriminate.
  - match goal with H : _ / _ ==[_]==>* _ / _ |- _ =>
      rewrite app_nil_l in H; inversion H; subst
    end.
    match goal with
    H1 : _ / _ ==[_]==> _ / _,
    H2 : _ / _ ==[_]==> _ / _ |- _ =>
      inversion H1; inversion H2; subst;
      eapply alloc_increments_memory_length in H1;
      eapply alloc_increments_memory_length in H2
    end.
    match goal with
    F : length ?x = length (add ?x _) |- _ =>
      rewrite length_add in F; eapply n_Sn in F
    end.
    assumption.
  - match goal with
    H : _ / _ ==[_]==>* _ / _ |- _ =>
      eapply destruct_multistep in H as [? [? [? Hmultistep']]]
    end.
    eapply monotonic_nondecreasing_memory_length in Hmultistep'.
    match goal with
    H1 : _ / _ ==[_]==> _ / _,
    H2 : _ / _ ==[_]==> _ / _ |- _ =>
      inversion H1; inversion H2; subst
    end.
    match goal with
    | H1 : length _ = length ?x, H2 : length _ <= length ?x |- _ =>
        rewrite <- H1 in H2; rewrite length_add in H2
    end.
    eapply not_Sn_le_n in Hmultistep'.
    assumption.
Qed.

(* PART 2 *)

Lemma load_if_access: forall m m' t t' ad v,
  m / t ==[EF_Load ad v]==> m' / t' ->
  access m t ad.
Proof.
  assert (forall m t t' ad,
    t --[ EF_Load ad (get_tm m ad) ]--> t' ->
    access m t ad). {
      intros * Hstep.
      remember (EF_Load ad (get_tm m ad)) as eff.
      induction Hstep; eauto using access;
      inversion Heqeff; subst. eauto using access.
  }
  intros * Hmstep. inversion Hmstep; subst. eauto.
Qed.

Lemma store_if_access: forall m m' t t' ad v,
  m / t ==[EF_Store ad v]==> m' / t' ->
  access m t ad.
Proof.
  assert (forall m t t' ad v,
    t --[ EF_Store ad v ]--> t' ->
    access m t ad). {
      intros * Hstep.
      remember (EF_Store ad v) as eff.
      induction Hstep; eauto using access;
      inversion Heqeff; subst. eauto using access.
  }
  intros * Hmstep. inversion Hmstep; subst. eauto.
Qed.

Lemma access_if_alloc : forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  access m' t' ad.
Proof.
  assert (forall m t t' ad v, t --[EF_Alloc ad v]--> t' -> access m t' ad). {
    intros ? ?. induction t; intros * Hstep;
    inversion Hstep; subst; eauto using access.
  }
  intros * Hmstep. destruct t'; inversion Hmstep; subst; eauto.
Qed.

Definition well_behaved_access m t :=
  forall ad, access m t ad -> ad < length m.

Lemma alloc_grants_access: forall m m' t t' ad v,
  well_behaved_access m t ->
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  ~ access m t ad /\ access m' t' ad.
Proof.
  intros * Hwba Hmstep. split; eauto using access_if_alloc.
  intros F. eapply Hwba in F.
  inversion Hmstep; subst.
  eapply Nat.lt_irrefl; eauto.
Qed.

(* TODO *)

Module wba.

Local Lemma wba_new : forall m t,
  well_behaved_access m (TM_New t) ->
  well_behaved_access m t.
Proof.
  intros * ? ?; eauto using access.
Qed.

Local Lemma wba_load : forall m t,
  well_behaved_access m (TM_Load t) ->
  well_behaved_access m t.
Proof.
  intros * ? ?; eauto using access.
Qed.

Local Lemma wba_load' : forall m t,
  well_behaved_access m t ->
  well_behaved_access m (TM_Load t).
Proof.
  intros * ? ? ?. eauto using load_access.
Qed.

Local Lemma wba_asg1 : forall m l r,
  well_behaved_access m (TM_Asg l r) ->
  well_behaved_access m l.
Proof.
  intros * ? ?. eauto using access.
Qed.

Local Lemma wba_asg2 : forall m l r,
  well_behaved_access m (TM_Asg l r) ->
  well_behaved_access m r.
Proof.
  intros * ? ?. eauto using access.
Qed.

Local Lemma wba_asg' : forall m l r,
  well_behaved_access m l ->
  well_behaved_access m r ->
  well_behaved_access m (TM_Asg l r).
Proof.
  intros * ? ? ? Hacc. eapply asg_access in Hacc as [? | ?]; eauto.
Qed.

Local Lemma wba_access_nil : forall m ad, 
  ~ access m TM_Nil ad.
Proof.
  intros * Hacc. inversion Hacc.
Qed.

Local Lemma wba_added_value : forall m v,
  well_behaved_access (add m v) v ->
  well_behaved_access (add m v) (TM_Loc (length m)).
Proof.
  intros * Hwba ad Hacc.
  remember (add m v) as m'.
  remember (TM_Loc (length m)) as t'.
  induction Hacc; inversion Heqt'; subst; try (rewrite length_add; lia).
  rewrite (get_add_last TM_Nil) in *; eauto using access.
Qed.

Local Lemma wba_stored_value : forall m t t' ad v,
  well_behaved_access m t ->
  t --[EF_Store ad v]--> t' ->
  well_behaved_access m v.
Proof.
  intros * ? Hstep ? ?.
  remember (EF_Store ad v) as eff.
  induction Hstep; try inversion Heqeff; subst;
  eauto using access, wba_new, wba_load, wba_asg1, wba_asg2.
Qed.

Local Lemma wba_mem_add: forall m t v,
  well_behaved_access m t ->
  well_behaved_access (add m v) t.
Proof.
  intros * Hwba ad Hacc.
  remember (add m v) as m'.
  induction Hacc; subst;
  eauto using wba_new, wba_load, wba_asg1, wba_asg2.
  - match goal with IH : _ -> ?x |- ?x => eapply IH end.
    intros ad'' Hacc''.
    destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]; subst.
    + rewrite (get_add_lt TM_Nil) in *; eauto using access.
    + specialize (Hwba (length m) (access_loc m (length m))). lia.
    + rewrite (get_add_gt TM_Nil) in *; eauto.
      contradict Hacc''. eauto using wba_access_nil.
  - rewrite length_add. eauto using access, Nat.lt_lt_succ_r.
Qed.

Local Lemma wba_mem_set: forall m t ad v,
  well_behaved_access m t ->
  well_behaved_access m v ->
  well_behaved_access (set m ad v) t.
Proof.
  intros * HwbaT HwbaV ad' Hacc'.
  rewrite <- set_preserves_length.
  remember (set m ad v) as m'.
  induction Hacc'; subst;
  eauto using access, wba_new, wba_load, wba_asg1, wba_asg2.
  match goal with IH : _ -> ?x |- ?x => eapply IH; clear IH end.
  destruct (Nat.eqb ad ad') eqn:E.
  - eapply Nat.eqb_eq in E; subst.
    rewrite (get_i_set_i TM_Nil); eauto using access.
  - eapply Nat.eqb_neq in E.
    rewrite (get_i_set_j TM_Nil) in *; fold get_tm in *; eauto.
    intros ? ?. eauto using access.
Qed.
  
Local Lemma alloc_preservation : forall m t t' v,
  well_behaved_access m t ->
  t --[ EF_Alloc (length m) v ]--> t' ->
  well_behaved_access (add m v) t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_Alloc (length m) v) as eff.
  induction Hstep; inversion Heqeff; subst;
  eauto using wba_new, wba_load, wba_load', wba_mem_add, wba_added_value;
  eapply wba_asg'; eauto using wba_asg1, wba_asg2, wba_mem_add.
Qed.

Local Lemma load_preservation : forall m t t' ad,
  well_behaved_access m t ->
  t --[ EF_Load ad (get_tm m ad) ]--> t' ->
  well_behaved_access m t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_Load ad (get_tm m ad)) as eff.
  induction Hstep; subst; try (inversion Heqeff);
  eauto using wba_new, wba_load, wba_load', wba_asg', wba_asg1, wba_asg2;
  eapply wba_load in Hwba; intros ? ?; eauto using access.
Qed.

Local Lemma store_preservation : forall m t t' ad v,
  well_behaved_access m t ->
  t --[EF_Store ad v]--> t' ->
  well_behaved_access (set m ad v) t'.
Proof.
  intros * Hwba Hstep.
  assert (well_behaved_access m v); eauto using wba_stored_value. 
  remember (EF_Store ad v) as eff.
  induction Hstep; subst; try (inversion Heqeff; subst);
  eauto using wba_new, wba_load, wba_load';
  try solve [eapply wba_asg'; eauto using wba_asg1, wba_asg2, wba_mem_set].
  intros ? F. contradict F. eauto using wba_access_nil.
Qed.

Lemma well_behaved_access_preservation : forall m m' t t' eff,
  well_behaved_access m t ->
  m / t ==[eff]==> m' / t' ->
  well_behaved_access m' t'.
Proof.
  intros * Hwba Hmstep. inversion Hmstep; subst;
  eauto using alloc_preservation, load_preservation, store_preservation.
Qed.

End wba.









(* BAGUNÇA *)

Lemma alloc_grants_access_multistep : forall m m' tc t t' ad v,
  m / t ==[EF_Alloc ad v :: tc]==>* m' / t' ->
  access m' t' ad.
Proof.
  intros * Hmulti. destruct t';
  inversion Hmulti; subst;
  eauto using alloc_grants_access_memory_step.
Qed.

(*

Inductive something :
  | Something_Load
    tid = alguma thread
    m / ths ==> m' / ths' # Load tid 23
    em todas as outras threads que não são tid,
    não pode ter Loc 23

*)
