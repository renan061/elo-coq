From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import UnsafeAccess.
From Elo Require Import SMS.

Reserved Notation "m / t '==[' tc ']==>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Definition mtrace := list effect.

(* ------------------------------------------------------------------------- *)
(* reflexive transitive closure                                              *)
(* ------------------------------------------------------------------------- *)

Inductive mmultistep : mem -> tm -> mtrace -> mem -> tm -> Prop :=
  | mmultistep_refl: forall m t,
    m / t ==[nil]==>* m / t

  | mmultistep_trans : forall m m' m'' t t' t'' tc eff,
    m  / t  ==[tc]==>* m'  / t'  ->
    m' / t' ==[eff]==> m'' / t'' ->
    m  / t  ==[eff :: tc]==>* m'' / t''

  where "m / t '==[' tc ']==>*' m' / t'" := (mmultistep m t tc m' t').

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma monotonic_nondecreasing_memory_length: forall m m' eff t t',
  m / t ==[eff]==>* m' / t' ->
  #m <= #m'.
Proof.
  assert (forall m m' eff t t',
    m / t ==[eff]==> m' / t' ->
    length m <= length m'). {
    intros * Hmstep. inversion Hmstep; subst; try lia.
    - rewrite add_increments_length. lia.
    - eauto using Nat.eq_le_incl, set_preserves_length.
  }
  intros * Hmmultistep. induction Hmmultistep; eauto using Nat.le_trans.
Qed.

Lemma alloc_increments_memory_length : forall m m' t t' ad v Tr,
  m / t ==[EF_Alloc ad v Tr]==> m' / t' ->
  #m' = S (#m).
Proof.
  intros. inversion_mstep. eauto using add_increments_length.
Qed.

Lemma destruct_multistep : forall tc eff m0 mF t0 tF,
  m0 / t0  ==[tc ++ eff :: nil]==>* mF / tF ->
  (exists m t, m0 / t0 ==[eff]==> m / t /\ m / t ==[tc]==>* mF / tF).
Proof.
  intros ?. induction tc as [| eff tc IH];
  intros * Hmultistep; inversion Hmultistep; subst.
  - eexists. eexists. inversion H3; subst. split; eauto using mmultistep.
  - specialize (IH _ _ _ _ _ H3) as [? [? [? ?]]].
    eexists. eexists. split; eauto using mmultistep.
Qed.

Theorem duplicate_alloc : forall m m' t t' tc ad v v' Tr Tr',
  ~ (m / t ==[EF_Alloc ad v Tr :: tc ++ EF_Alloc ad v' Tr' :: nil]==>* m' / t').
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

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Local Lemma cstep_read_requires_acc : forall m m' ths ths' tid ad v,
  m / ths ~~[tid, EF_Read ad v]~~> m' / ths' ->
  access m ths[tid] ad.
Proof.
  intros. inversion_clear_cstep. inversion_clear_mstep. induction_step;
  eauto using access.
Qed.

Local Lemma cstep_write_requires_uacc : forall m m' ths ths' tid ad v Tr,
  forall_threads ths well_typed ->
  m / ths ~~[tid, EF_Write ad v Tr]~~> m' / ths' ->
  UnsafeAccess m ths[tid] ad.
Proof.
  intros * Htype. intros. destruct (Htype tid) as [T ?].
  inversion_clear_cstep. inversion_clear_mstep. generalize dependent T.
  induction_step; intros; inversion_type; eauto using UnsafeAccess.
  inversion_type. eauto using UnsafeAccess.
Qed.

Theorem safety : forall m m' ths ths' tid1 tid2 ad v1 v2 tc Tr,
  forall_threads ths well_typed ->
  safe_memory_sharing m ths ->
  tid1 <> tid2 ->
  m / ths ~~[(tid1, EF_Read  ad v1   ) :: tc ++
             (tid2, EF_Write ad v2 Tr) :: nil]~~>* m' / ths' ->
  False.
Proof.
  intros * Htype Hsms Hneq Hmultistep.
  inversion_subst_clear Hmultistep.
  assert (Hacc' : access m'0 ths'0[tid1] ad)
    by eauto using cstep_read_requires_acc.
  induction tc.
  - inversion_multistep.
    inversion_multistep.
    assert (Huacc : UnsafeAccess m'1 ths'1[tid2] ad)
      by eauto using cstep_write_requires_uacc.

    rename m'1 into m;  rename ths'1 into ths;

    rename H9 into First.
    rename H7 into Second.

    inversion First; subst. inversion H0; subst.
    inversion Second; subst. inversion H2; subst.

    simpl_array.
    eapply (Hsms tid2 tid1); eauto.
    destruct (acc_dec m ths[tid1] ad);
    eauto using mem_set_acc.
  - rename m' into m'''. rename ths' into ths'''.
    rename m'0 into m''. rename ths'0 into ths''.
    inversion_clear_multistep.


Qed.


(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma access_add : forall m t ad v Tr,
  ~ access m t ad ->
  ~ access m v ad ->
  ~ access (m +++ (v, Tr)) t ad.
Proof.
  intros * HnaccT HnaccV Hacc.
  induction Hacc; eauto using access.
  eapply IHHacc; clear IHHacc; trivial.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; simpl_array;
  eauto using access. intros ?. unfold memory_default in *. simpl in *.
  inversion_acc.
Qed.

Local Lemma not_access_stored_value : forall m t t' ad ad' v Tr,
  ~ access m t ad ->
  t --[EF_Write ad' v Tr]--> t' ->
  ~ access m v ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Local Lemma not_access_allocated_value : forall m t t' ad ad' v Tr,
  ~ access m t ad ->
  t --[EF_Alloc ad' v Tr]--> t' ->
  ~ access m v ad.
Proof.
  intros * Hnacc Hstep. induction_step; eauto using access.
Qed.

Lemma access_granted_by_alloc_is_memory_length : forall m t t' ad v Tr,
  ~ access m t ad ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  access (m +++ (v, Tr)) t' ad ->
  ad = length m.
Proof.
  intros * Hnacc ? Hacc.
  induction_step; inversion_nacc Hnacc; inversion_acc; eauto using access.
  - match goal with F : access _ _ _ |- _ => contradict F end.
    simpl_array. eapply access_add; eauto.
  - do 2 auto_specialize. eapply IHstep.
    eapply acc_asg in Hacc as [? | ?]; eauto.
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
  ~ access m t ad ->
  m / t ==[eff]==> m' / t' ->
  access m' t' ad ->
  exists v, eff = (EF_Alloc ad v).
Proof.
  intros * Hnacc Hmstep Hacc. inversion Hmstep; subst.
  - contradict Hacc. eauto using none_does_not_grant_access.
  - eexists. erewrite <- access_granted_by_alloc_is_memory_length; eauto.
  - contradict Hacc. eauto using load_does_not_grant_access.
  - contradict Hacc. eauto using store_does_not_grant_access.
Qed.

Theorem access_needs_alloc_multistep : forall m m' t t' ad tc,
  ~ access m t ad ->
  m / t ==[tc]==>* m' / t' ->
  access m' t' ad ->
  exists v, In (EF_Alloc ad v) tc.
Proof.
  intros * Hnacc Hmultistep Hacc.
  induction Hmultistep; try solve [exfalso; eauto].
  destruct (access_dec m' t' ad) as [Hacc' | ?].
  - destruct (IHHmultistep Hnacc Hacc').
    eexists. right. eauto.
  - assert (Heq : exists v, eff = EF_Alloc ad v);
    eauto using access_needs_alloc.
    destruct Heq. eexists. left. eauto.
Qed.

(*

(* PART 6 *)

Theorem concurrent_duplicate_alloc :
  forall m m' ths ths' tid tid' tc1 tc2 ad v v',
  ~ (m / ths ~~[tc1 ++ (tid , EF_Alloc ad v ) ::
                tc2 ++ (tid', EF_Alloc ad v') :: nil]~~>* m' / ths').
Proof.
  intros * F. inversion F; subst; clear F.
Abort.

*)
