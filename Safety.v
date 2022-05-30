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
  | access_mem : forall ad ad',
    access m (get TM_Nil m ad') ad ->
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

Local Lemma access_nil : forall m ad,
  ~ access m TM_Nil ad.
Proof.
  intros * Hacc. inversion Hacc.
Qed.

Local Lemma access_num : forall m ad n,
  ~ access m (TM_Num n) ad.
Proof.
  intros * Hacc. inversion Hacc.
Qed.

Lemma new_access : forall m t ad,
  access m (TM_New t) ad ->
  access m t ad.
Proof.
  intros * Hacc. remember (TM_New t) as t'.
  induction Hacc; inversion Heqt'; subst; eauto using access.
Qed.

Lemma new_access_inverse: forall m t ad,
  ~ access m (TM_New t) ad ->
  ~ access m t ad.
Proof.
  intros * ? Hacc. inversion Hacc; subst; eauto using access.
Qed.

Lemma load_access : forall m t ad,
  access m (TM_Load t) ad ->
  access m t ad.
Proof.
  intros * Hacc. remember (TM_Load t) as t'.
  induction Hacc; inversion Heqt'; subst; eauto using access.
Qed.

Lemma load_access_inverse : forall m t ad,
  ~ access m (TM_Load t) ad ->
  ~ access m t ad.
Proof.
  intros * ? Hacc. inversion Hacc; subst; eauto using access.
Qed.

Lemma access_load_inverse : forall m t ad,
  ~ access m t ad ->
  ~ access m (TM_Load t) ad.
Proof.
  intros * ? Hacc. inversion Hacc; subst; eauto.
Qed.

Lemma asg_access : forall m l r ad,
  access m (TM_Asg l r) ad ->
  access m l ad \/ access m r ad.
Proof.
  intros * Hacc. remember (TM_Asg l r) as t.
  induction Hacc; inversion Heqt; subst; eauto.
Qed.

Lemma asg_access_inverse : forall m l r ad,
  ~ access m (TM_Asg l r) ad ->
  ~ access m l ad /\ ~ access m r ad.
Proof.
  intros * ?. split; intros Hacc; inversion Hacc; subst; eauto using access.
Qed.

Lemma access_asg_inverse : forall m l r ad,
  ~ access m l ad /\ ~ access m r ad ->
  ~ access m (TM_Asg l r) ad.
Proof.
  intros * [? ?] Hacc. inversion Hacc; subst; eauto.
Qed.

Lemma seq_access : forall m t1 t2 ad,
  access m (TM_Seq t1 t2) ad ->
  access m t1 ad \/ access m t2 ad.
Proof.
  intros * Hacc. remember (TM_Seq t1 t2) as t.
  induction Hacc; inversion Heqt; subst; eauto.
Qed.

Lemma seq_access_inverse : forall m t1 t2 ad,
  ~ access m (TM_Seq t1 t2) ad ->
  ~ access m t1 ad /\ ~ access m t2 ad.
Proof.
  intros * ?. split; intros Hacc; inversion Hacc; subst; eauto using access.
Qed.

Lemma access_seq_inverse : forall m t1 t2 ad,
  ~ access m t1 ad /\ ~ access m t2 ad ->
  ~ access m (TM_Seq t1 t2) ad.
Proof.
  intros * [? ?] Hacc. inversion Hacc; subst; eauto.
Qed.

(* strong mem access *)
Local Lemma access_get_trans : forall m t ad ad',
  access m t ad' ->
  access m (get TM_Nil m ad') ad ->
  access m t ad.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access.
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
    intros * Hmstep. inversion Hmstep; subst; try lia.
    - rewrite add_increments_length . lia.
    - eauto using Nat.eq_le_incl, set_preserves_length.
  }
  intros * Hmultistep. induction Hmultistep; eauto using Nat.le_trans.
Qed.

Lemma alloc_increments_memory_length : forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  length m' = S (length m).
Proof.
  intros * Hmstep. inversion Hmstep; subst.
  eauto using add_increments_length.
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
    lia.
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
    | H1 : length ?x = length _, H2 : length _ <= length ?x |- _ =>
      rewrite H1 in H2;
      rewrite add_increments_length in H2
    end.
    lia.
Qed.

(* PART 2 *)

Lemma load_if_access: forall m m' t t' ad v,
  m / t ==[EF_Load ad v]==> m' / t' ->
  access m t ad.
Proof.
  assert (forall m t t' ad,
    t --[ EF_Load ad (get TM_Nil m ad) ]--> t' ->
    access m t ad). {
      intros * Hstep.
      remember (EF_Load ad (get TM_Nil m ad)) as eff.
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

(* PART 3 *)

Module wba.

Lemma new : forall m t,
  well_behaved_access m (TM_New t) ->
  well_behaved_access m t.
Proof.
  intros * ? ?; eauto using access.
Qed.

Lemma load : forall m t,
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

Lemma asg1 : forall m l r,
  well_behaved_access m (TM_Asg l r) ->
  well_behaved_access m l.
Proof.
  intros * ? ?. eauto using access.
Qed.

Lemma asg2 : forall m l r,
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

Lemma seq1 : forall m t1 t2,
  well_behaved_access m (TM_Seq t1 t2) ->
  well_behaved_access m t1.
Proof.
  intros * ? ?. eauto using access.
Qed.

Lemma seq2 : forall m t1 t2,
  well_behaved_access m (TM_Seq t1 t2) ->
  well_behaved_access m t2.
Proof.
  intros * ? ?. eauto using access.
Qed.

Local Lemma wba_seq' : forall m t1 t2,
  well_behaved_access m t1 ->
  well_behaved_access m t2 ->
  well_behaved_access m (TM_Seq t1 t2).
Proof.
  intros * ? ? ? Hacc. eapply seq_access in Hacc as [? | ?]; eauto.
Qed.

Local Lemma wba_added_value : forall m v,
  well_behaved_access (add m v) v ->
  well_behaved_access (add m v) (TM_Loc (length m)).
Proof.
  intros * Hwba ad Hacc.
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
  intros * ? Hstep ? ?.
  remember (EF_Store ad v) as eff.
  induction Hstep; try inversion Heqeff; subst;
  eauto using access, new, load, asg1, asg2, seq1, seq2.
Qed.

Lemma mem_add: forall m t v,
  well_behaved_access m t ->
  well_behaved_access (add m v) t.
Proof.
  intros * Hwba ad Hacc.
  remember (add m v) as m'.
  induction Hacc; subst;
  eauto using new, load, asg1, asg2, seq1, seq2.
  - match goal with IH : _ -> ?x |- ?x => eapply IH end.
    intros ad'' Hacc''.
    destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]; subst.
    + rewrite (get_add_lt TM_Nil) in *; eauto using access.
    + specialize (Hwba (length m) (access_loc m (length m))). lia.
    + rewrite (get_add_gt TM_Nil) in *; eauto.
      contradict Hacc''. eauto using access_nil.
  - rewrite add_increments_length. eauto using access, Nat.lt_lt_succ_r.
Qed.

Local Lemma wba_mem_set: forall m t ad v,
  well_behaved_access m t ->
  well_behaved_access m v ->
  well_behaved_access (set m ad v) t.
Proof.
  intros * HwbaT HwbaV ad' Hacc'.
  rewrite set_preserves_length.
  remember (set m ad v) as m'.
  induction Hacc'; subst;
  eauto using access, new, load, asg1, asg2, seq1, seq2.
  match goal with IH : _ -> ?x |- ?x => eapply IH; clear IH end.
  destruct (Nat.eqb ad ad') eqn:E.
  - eapply Nat.eqb_eq in E; subst.
    rewrite (get_set_eq TM_Nil); eauto using access.
  - eapply Nat.eqb_neq in E.
    rewrite (get_set_neq TM_Nil) in *; eauto.
    intros ? ?. eauto using access.
Qed.

Local Lemma alloc_preservation : forall m t t' v,
  well_behaved_access m t ->
  t --[EF_Alloc (length m) v]--> t' ->
  well_behaved_access (add m v) t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_Alloc (length m) v) as eff.
  induction Hstep; inversion Heqeff; subst;
  eauto using new, load, wba_load', mem_add, wba_added_value;
  try (eapply wba_asg' || eapply wba_seq');
  eauto using asg1, asg2, seq1, seq2, mem_add.
Qed.

Local Lemma load_preservation : forall m t t' ad,
  well_behaved_access m t ->
  t --[EF_Load ad (get TM_Nil m ad)]--> t' ->
  well_behaved_access m t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_Load ad (get TM_Nil m ad)) as eff.
  induction Hstep; subst; try (inversion Heqeff; subst);
  eauto using new, load, wba_load', asg1, asg2, wba_asg', seq1, seq2, wba_seq';
  eapply load in Hwba; intros ? ?; eauto using access.
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
  eauto using new, load, wba_load';
  try (eapply wba_asg' || eapply wba_seq');
  eauto using asg1, asg2, seq1, seq2, wba_mem_set.
  intros ? F. contradict F. eauto using access_nil.
Qed.

Lemma mstep_preservation : forall m m' t t' eff,
  well_behaved_access m t ->
  m / t ==[eff]==> m' / t' ->
  well_behaved_access m' t'.
Proof.
  intros * Hwba Hmstep. inversion Hmstep; subst;
  eauto using alloc_preservation, load_preservation, store_preservation.
Qed.

End wba.

(* PART 4 *)

Local Lemma access_set : forall m t ad ad' v,
  ~ access m t ad ->
  ~ access m v ad ->
  ~ access (set m ad' v) t ad.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m).
  { intros. split; destruct n; eauto. }

  assert (forall m ad ad' v,
    access (set m ad' v) (get TM_Nil (set m ad' v) ad') ad ->
    ad' < length m). {
    intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
    rewrite get_set_invalid in H; trivial. inversion H.
  }

  intros * HnaccT HnaccV F.
  remember (set m ad' v) as m'.
  induction F; inversion Heqm'; subst; eauto using access.
  match goal with H : ~ access _ (TM_Loc ?ad) _ |- _ => 
    destruct (Nat.eq_dec ad' ad) as [? | Hneq]; subst
  end. 
  - match goal with H : ~ access _ (TM_Loc ?ad) _ |- _ => 
      assert (ad < length m); eauto
    end. 
    rewrite get_set_eq in F; trivial.
    rewrite get_set_eq in IHF; eauto.
  - eapply not_eq_sym in Hneq.
    rewrite (get_set_neq TM_Nil) in *; eauto using access.
Qed.

Local Lemma access_add : forall m t ad v,
  ~ access m t ad ->
  ~ access m v ad ->
  ~ access (add m v) t ad.
Proof.
  intros * HnaccT HnaccV Hacc.
  induction Hacc; eauto using access.
  eapply IHHacc; clear IHHacc; trivial.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst.
  - rewrite get_add_lt; eauto using access.
  - rewrite get_add_eq. trivial.
  - rewrite get_add_gt; trivial. intros F. inversion F.
Qed.

Local Lemma not_access_stored_value : forall m t t' ad ad' v, 
  ~ access m t ad ->
  t --[ EF_Store ad' v ]--> t' ->
  ~ access m v ad.
Proof.
  intros * Hnacc Hstep.
  remember (EF_Store ad' v) as eff.
  induction Hstep; inversion Heqeff; subst; eauto using access.
Qed.

Local Lemma not_access_allocated_value : forall m t t' ad ad' v, 
  ~ access m t ad ->
  t --[ EF_Alloc ad' v ]--> t' ->
  ~ access m v ad.
Proof.
  intros * Hnacc Hstep.
  remember (EF_Alloc ad' v) as eff.
  induction Hstep; inversion Heqeff; subst; eauto using access.
Qed.

Lemma load_does_not_grant_access : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Load ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc Hmstep. inversion Hmstep; subst; clear Hmstep.
  remember (EF_Load ad' (get TM_Nil m' ad')) as eff.
  match goal with Hstep : _ --[_]--> _ |- _ => induction Hstep end;
  inversion Heqeff; subst; eauto using access.
  - eapply access_load_inverse; eauto using load_access_inverse.
  - eapply asg_access_inverse in Hnacc as [? ?].
    eauto using access_asg_inverse.
  - eapply asg_access_inverse in Hnacc as [? ?].
    eauto using access_asg_inverse.
  - eapply seq_access_inverse in Hnacc as [? ?].
    eauto using access_seq_inverse.
Qed.

Lemma store_does_not_grant_access : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Store ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc Hmstep. inversion Hmstep; subst.
  remember (EF_Store ad' v) as eff; clear Hmstep.
  match goal with Hstep : _ --[_]--> _ |- _ => induction Hstep end;
  inversion Heqeff; subst; eauto using access.
  - eapply access_load_inverse; eauto using load_access_inverse.
  - eapply asg_access_inverse in Hnacc as [? ?].
    eapply access_asg_inverse; split;
    eauto using access_set, (not_access_stored_value _ l).
  - eapply asg_access_inverse in Hnacc as [? ?].
    eapply access_asg_inverse; split;
    eauto using access_set, (not_access_stored_value _ r).
  - intros F. inversion F.
  - eapply seq_access_inverse in Hnacc as [? ?].
    eapply access_seq_inverse; split;
    eauto using access_set, (not_access_stored_value _ t1).
Qed.

Lemma access_granted_by_alloc_is_memory_length : forall m t t' ad v,
  ~ access m t ad ->
  t --[ EF_Alloc (length m) v ]--> t' ->
  access (add m v) t' ad ->
  ad = length m.
Proof.
  intros * Hnacc Hstep Hacc.
  remember (EF_Alloc (length m) v) as eff.
  induction Hstep; inversion Heqeff; subst; try (clear Heqeff);
  eauto using access, load_access, load_access_inverse.
  - eapply new_access_inverse in Hnacc.
    inversion Hacc; clear Hacc; subst; trivial.
    match goal with F : access _ _ _ |- _ => contradict F end.
    rewrite get_add_eq. eapply access_add; eauto.
  - eapply asg_access_inverse in Hnacc as [HnaccL ?].
    match goal with IH : _ -> _ -> _ -> ?x |- ?x => eapply IH; eauto end.
    eapply asg_access in Hacc as [? | ?]; eauto.
    exfalso. eapply (not_access_allocated_value _ l) in HnaccL; eauto. 
    eapply (access_add _ r); eauto.
  - eapply asg_access_inverse in Hnacc as [? HnaccR].
    match goal with IH : _ -> _ -> _ -> ?x |- ?x => eapply IH; eauto end.
    eapply asg_access in Hacc as [? | ?]; eauto.
    exfalso. eapply (not_access_allocated_value _ r) in HnaccR; eauto. 
    eapply (access_add _ l); eauto.
  - eapply seq_access_inverse in Hnacc as [HnaccT1 ?].
    match goal with IH : _ -> _ -> _ -> ?x |- ?x => eapply IH; eauto end.
    eapply seq_access in Hacc as [? | ?]; eauto.
    exfalso. eapply (not_access_allocated_value _ t1) in HnaccT1; eauto. 
    eapply (access_add _ t2); eauto.
Qed.

Theorem access_needs_alloc : forall m m' t t' eff ad,
  well_behaved_access m t ->
  ~ access m t ad ->
  m / t ==[eff]==> m' / t' ->
  access m' t' ad ->
  exists v, eff = (EF_Alloc ad v).
Proof.
  intros * Hwba Hnacc Hmstep Hacc. inversion Hmstep; subst.
  - eexists. erewrite <- access_granted_by_alloc_is_memory_length; eauto.
  - contradict Hacc. eauto using load_does_not_grant_access.
  - contradict Hacc. eauto using store_does_not_grant_access.
Qed.




















(* BAGUNÇA)

(*
quando tiver concorrencia, usar esse para provar o principal
se não tinha acesso e agora tem, então teve um alloc no meio do caminho
*)

Lemma
  ~ access m t ad
  m / t ==[tc]==>* m' / t'
  access m' t' ad
  exists v, tc contains (Alloc ad v)

Lemma inverse : forall m ad ad',
  ad <> ad' ->
  access m (TM_Loc ad') ad ->
  access m (get TM_Nil m ad') ad.
Proof.
  intros * Hneq Hacc.
  remember (TM_Loc ad') as t.
  induction Hacc; inversion Heqt; subst; trivial.
  lia.
Qed.

Lemma alloc_grants_access_multistep : forall m m' tc t t' ad v,
  m / t ==[EF_Alloc ad v :: tc]==>* m' / t' ->
  access m' t' ad.
Proof.
  intros * Hmulti. destruct t';
  inversion Hmulti; subst;
  eauto using alloc_grants_access_memory_step.
Qed.

Inductive something :
  | Something_Load
    tid = alguma thread
    m / ths ==> m' / ths' # Load tid 23
    em todas as outras threads que não são tid,
    não pode ter Loc 23

*)
