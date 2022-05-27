From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Lia.
From Coq Require Import Logic.FunctionalExtensionality.

From Elo Require Import Mem.
From Elo Require Import Core0.

Reserved Notation "m / t '==[' tc ']==>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Inductive access (m : mem tm) : tm -> addr -> Prop :=
  | access_mem : forall ad ad',
    access m (get m ad') ad ->
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
  access m (get m ad') ad ->
  access m t ad.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access.
Qed.

Definition trace := list effect.

(* reflexive transitive closure *)
Inductive multistep : mem tm -> tm -> trace -> mem tm -> tm -> Prop :=
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
    - rewrite add_increments_memory_length. lia.
    - eauto using Nat.eq_le_incl, set_preserves_memory_length.
  }
  intros * Hmultistep. induction Hmultistep; eauto using Nat.le_trans.
Qed.

Lemma alloc_increments_memory_length : forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  length m' = S (length m).
Proof.
  intros * Hmstep. inversion Hmstep; subst.
  eauto using add_increments_memory_length.
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
    | H1 : S (length ?x) = S (length _), H2 : length _ <= length ?x |- _ =>
        idtac H1; idtac H2; inversion H1 as [H3];
        rewrite H3 in H2;
        rewrite add_increments_memory_length in H2
    end.
    lia.
Qed.

(* PART 2 *)

Lemma load_if_access: forall m m' t t' ad v,
  m / t ==[EF_Load ad v]==> m' / t' ->
  access m t ad.
Proof.
  assert (forall m t t' ad,
    t --[ EF_Load ad (get m ad) ]--> t' ->
    access m t ad). {
      intros * Hstep.
      remember (EF_Load ad (get m ad)) as eff.
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

Lemma wba_new : forall m t,
  well_behaved_access m (TM_New t) ->
  well_behaved_access m t.
Proof.
  intros * ? ?; eauto using access.
Qed.

Lemma wba_load : forall m t,
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

Lemma wba_asg1 : forall m l r,
  well_behaved_access m (TM_Asg l r) ->
  well_behaved_access m l.
Proof.
  intros * ? ?. eauto using access.
Qed.

Lemma wba_asg2 : forall m l r,
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

Lemma wba_seq1 : forall m t1 t2,
  well_behaved_access m (TM_Seq t1 t2) ->
  well_behaved_access m t1.
Proof.
  intros * ? ?. eauto using access.
Qed.

Local Lemma wba_seq2 : forall m t1 t2,
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
(*
Local Lemma wba_added_value : forall m v,
  well_behaved_access (add m v) v ->
  well_behaved_access (add m v) (TM_Loc (length m)).
Proof.
  intros * Hwba ad Hacc.
  remember (add m v) as m'.
  remember (TM_Loc (length m)) as t'.
  induction Hacc; inversion Heqt'; subst.
  - rewrite (get_add_eq TM_Nil) in *; eauto using access.
  - rewrite add_increments_memory_length. lia.
Qed.
*)
Local Lemma wba_stored_value : forall m t t' ad v,
  well_behaved_access m t ->
  t --[EF_Store ad v]--> t' ->
  well_behaved_access m v.
Proof.
  intros * ? Hstep ? ?.
  remember (EF_Store ad v) as eff.
  induction Hstep; try inversion Heqeff; subst;
  eauto using access, wba_new, wba_load, wba_asg1, wba_asg2, wba_seq1,
    wba_seq2.
Qed.

Local Lemma wba_mem_add: forall m t v,
  well_behaved_access m t ->
  well_behaved_access (add m v) t.
Proof.
  intros * Hwba ad Hacc.
  remember (add m v) as m'.
  induction Hacc; subst;
  eauto using wba_new, wba_load, wba_asg1, wba_asg2, wba_seq1, wba_seq2.
  - match goal with IH : _ -> ?x |- ?x => eapply IH end.
    intros ad'' Hacc''.
    destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]; subst.
    + rewrite (get_add_lt TM_Nil) in *; eauto using access.
    + specialize (Hwba (length m) (access_loc m (length m))). lia.
    + rewrite (get_add_gt TM_Nil) in *; eauto.
      contradict Hacc''. eauto using access_nil.
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
  eauto using access, wba_new, wba_load, wba_asg1, wba_asg2, wba_seq1,
    wba_seq2.
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
  t --[EF_Alloc (length m) v]--> t' ->
  well_behaved_access (add m v) t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_Alloc (length m) v) as eff.
  induction Hstep; inversion Heqeff; subst;
  eauto using wba_new, wba_load, wba_load', wba_mem_add, wba_added_value;
  try (eapply wba_asg' || eapply wba_seq');
  eauto using wba_asg1, wba_asg2, wba_seq1, wba_seq2, wba_mem_add.
Qed.

Local Lemma load_preservation : forall m t t' ad,
  well_behaved_access m t ->
  t --[EF_Load ad (get_tm m ad)]--> t' ->
  well_behaved_access m t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_Load ad (get_tm m ad)) as eff.
  induction Hstep; subst; try (inversion Heqeff; subst);
  eauto using wba_new, wba_load, wba_load', wba_asg1, wba_asg2, wba_asg',
    wba_seq1, wba_seq2, wba_seq';
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
  try (eapply wba_asg' || eapply wba_seq');
  eauto using wba_asg1, wba_asg2, wba_seq1, wba_seq2, wba_mem_set.
  intros ? F. contradict F. eauto using access_nil.
Qed.

Lemma wba_mstep_preservation : forall m m' t t' eff,
  well_behaved_access m t ->
  m / t ==[eff]==> m' / t' ->
  well_behaved_access m' t'.
Proof.
  intros * Hwba Hmstep. inversion Hmstep; subst;
  eauto using alloc_preservation, load_preservation, store_preservation.
Qed.

End wba.

Import wba.

(* PART 4 *)

Lemma load_does_not_grant_access : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Load ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc Hmstep.
  destruct (Nat.eqb ad ad') eqn:E.
  - eapply Nat.eqb_eq in E; subst.
    eapply load_if_access in Hmstep. contradiction.
  - eapply Nat.eqb_neq in E.
    inversion Hmstep; subst; clear Hmstep.
    remember (EF_Load ad' (get_tm m' ad')) as eff.
    match goal with Hstep : _ --[_]--> _ |- _ => induction Hstep end;
    inversion Heqeff; subst.
    + eauto using new_access_inverse.
    + eapply access_load_inverse; eauto using load_access_inverse.
    + eauto using access.
    + eapply asg_access_inverse in Hnacc as [? ?].
      eauto using access_asg_inverse.
    + eapply asg_access_inverse in Hnacc as [? ?].
      eauto using access_asg_inverse.
    + eapply seq_access_inverse in Hnacc as [? ?].
      eauto using access_seq_inverse.
Qed.

(*
Lemma auxaux : forall m ad v loc i,
  loc <> i ->
  access (set m i v) (get_tm m loc) ad ->
  access m (get_tm m loc) ad.
Proof.
  intros * Hneq Hacc.
Admitted.

Lemma aux_1 : forall m ad ad' i,
  i < length m ->
  access (set m i (TM_Loc ad')) (TM_Loc ad') ad <->
  access m (TM_Loc ad') ad.
Proof.
  intros * Hlen. split; intros Hacc.
  - remember (TM_Loc ad') as v.
    remember (set m i v) as m'.
    induction Hacc; inversion Heqm'; subst; inversion Heqv; subst;
    eauto using access.
    destruct (Nat.eqb ad' i) eqn:E.
    + eapply Nat.eqb_eq in E; subst.
      rewrite (get_i_set_i TM_Nil) in *; eauto.
    + eapply Nat.eqb_neq in E.
      rewrite (get_i_set_j TM_Nil) in *; eauto using access, auxaux.
Admitted.

Lemma aux0 : forall m ad ad' v,
  value v ->
  ~ access m v ad ->
  ~ access (set m ad' v) v ad.
Proof.
  intros * Hvalue Hnacc.
  destruct Hvalue; eauto using access_nil, access_num.
  rewrite aux_1. eauto.
Admitted.

Lemma aux1 : forall m t t' ad ad' v,
  ~ access m t ad ->
  t --[EF_Store ad' v]--> t' ->
  ad' < length m ->
  ~ access (set m ad' v) v ad.
Proof.
  intros * Hnacc Hstep Hlen.
  remember (EF_Store ad' v) as eff.
  induction Hstep; inversion Heqeff; subst.
  - eauto using new_access_inverse.
  - eauto using load_access_inverse.
  - eapply asg_access_inverse in Hnacc as [? ?]; eauto.
  - eapply asg_access_inverse in Hnacc as [? ?]; eauto.
  - eapply asg_access_inverse in Hnacc as [? ?].
    
  - eapply seq_access_inverse in Hnacc as [? ?]; eauto.
Qed.



Lemma not_access_stored_value : forall m t t' ad v, 
  ~ access m t ad ->
  t --[ EF_Store ad v ]--> t' ->
  ~ access m v ad.
Proof.
  intros * Hnacc Hstep.
  remember (EF_Store ad v) as eff.
  induction Hstep; inversion Heqeff; subst; eauto using access.
Qed.
*)

Lemma aux1 : forall m t ad ad' v,
  ~ access m t ad ->
  ~ access m v ad ->
  ~ access (set m ad' v) t ad.
Proof.
  intros * HnaccT HnaccV F.
  remember (set m ad' v) as m'.
  induction F; inversion Heqm'; subst.
  - destruct (Nat.eq_dec ad' ad'0); subst.
    eapply IHF; trivial; admit.
    admit.
  - eauto using access.
  - eauto using new_access_inverse.
  - eauto using load_access_inverse.
  - eapply asg_access_inverse in HnaccT as [? ?]; eauto.
  - eapply asg_access_inverse in HnaccT as [? ?]; eauto.
  - eapply seq_access_inverse in HnaccT as [? ?]; eauto.
  - eapply seq_access_inverse in HnaccT as [? ?]; eauto.
Admitted.

Lemma store_does_not_grant_access : forall m m' t t' ad ad' v,
  well_behaved_access m t ->
  ~ access m t ad ->
  m / t ==[EF_Store ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hwba Hnacc Hmstep.
  destruct (Nat.eqb ad ad') eqn:E.
  - eapply Nat.eqb_eq in E; subst.
    eapply store_if_access in Hmstep.
    contradiction.
  - eapply Nat.eqb_neq in E.
    inversion Hmstep; subst.
    remember (EF_Store ad' v) as eff; clear Hmstep.
    match goal with Hstep : _ --[_]--> _ |- _ => induction Hstep end;
    inversion Heqeff; subst.
    + eauto using wba_new, new_access_inverse.
    + eapply access_load_inverse; eauto using wba_load, load_access_inverse.
    + eapply asg_access_inverse in Hnacc as [? ?].
      eapply wba_asg in Hwba.
      eapply access_asg_inverse; split; eauto.
    + eapply asg_access_inverse in Hnacc as [? ?].
      eauto using access_asg_inverse, aux2.
    + eapply asg_access_inverse in Hnacc as [? ?].
      shelve.
    + eapply seq_access_inverse in Hnacc as [? ?].
      eauto using access_seq_inverse, aux2.
Qed.

Theorem access_needs_alloc : forall m m' t t' eff ad,
  well_behaved_access m t ->
  ~ access m t ad ->
  m / t ==[eff]==> m' / t' ->
  access m' t' ad ->
  exists v, eff = (EF_Alloc ad v).
Proof.
  intros * Hwba Hnacc Hmstep Hacc. inversion Hmstep; subst.
  - shelve.
  - contradict Hacc; eauto using load_does_not_grant_access.
  - contradict Hacc.
Qed.

(*
quando tiver concorrencia, usar esse para provar o principal
se não tinha acesso e agora tem, então teve um alloc no meio do caminho
*)
Lemma
  ~ access m t ad
  m / t ==[tc]==>* m' / t'
  access m' t' ad
  exists v, tc contains (Alloc ad v)








(* BAGUNÇA)

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
