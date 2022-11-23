From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Contains.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.
From Elo Require Import References.
From Elo Require Import AccessProp.

Inductive UnsafeAccess (m : mem) : tm -> addr -> Prop :=
  | uacc_mem : forall ad ad' T,
    ad <> ad' ->
    UnsafeAccess m m[ad'] ad ->
    UnsafeAccess m <{ &ad' :: &T }> ad

  | uacc_ref : forall ad T,
    UnsafeAccess m <{ &ad :: &T }> ad

  | uacc_new : forall T t ad,
    UnsafeAccess m t ad ->
    UnsafeAccess m <{ new T t }> ad

  | uacc_load : forall t ad,
    UnsafeAccess m t ad ->
    UnsafeAccess m <{ *t }> ad

  | uacc_asg1 : forall t1 t2 ad,
    UnsafeAccess m t1 ad ->
    UnsafeAccess m <{ t1 = t2 }> ad

  | uacc_asg2 : forall t1 t2 ad,
    UnsafeAccess m t2 ad ->
    UnsafeAccess m <{ t1 = t2 }> ad

  | uacc_fun : forall x Tx t ad,
    UnsafeAccess m t ad ->
    UnsafeAccess m <{ fn x Tx --> t }> ad

  | uacc_call1 : forall t1 t2 ad,
    UnsafeAccess m t1 ad ->
    UnsafeAccess m <{ call t1 t2 }> ad

  | uacc_call2 : forall t1 t2 ad,
    UnsafeAccess m t2 ad ->
    UnsafeAccess m <{ call t1 t2 }> ad

  | uacc_seq1 : forall t1 t2 ad,
    UnsafeAccess m t1 ad ->
    UnsafeAccess m <{ t1; t2 }> ad

  | uacc_seq2 : forall t1 t2 ad,
    UnsafeAccess m t2 ad ->
    UnsafeAccess m <{ t1; t2 }> ad
  .

Ltac inversion_uacc :=
  match goal with
  | H : UnsafeAccess _ <{ unit         }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ N _          }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ & _ :: _     }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ new _ _      }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ * _          }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ _ = _        }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ var _        }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ fn _ _ --> _ }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ call _ _     }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ _ ; _        }> _ |- _ => inversion H; subst
  | H : UnsafeAccess _ <{ spawn _      }> _ |- _ => inversion H; subst
  end.

Ltac inversion_clear_uacc :=
  match goal with
  | H : UnsafeAccess _ <{ unit         }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ N _          }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ & _ :: _     }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ new _ _      }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ * _          }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ _ = _        }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ var _        }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ fn _ _ --> _ }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ call _ _     }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ _ ; _        }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ spawn _      }> _ |- _ => inversion_subst_clear H
  end.

Lemma uacc_dec : forall m t ad,
  Decidable.decidable (UnsafeAccess m t ad).
Proof. eauto using classic_decidable. Qed.

(* ------------------------------------------------------------------------- *)
(* negation                                                                  *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_nuacc :=
  intros; try (split; intros); eauto using UnsafeAccess.

Lemma nuacc_new : forall m t ad T,
  ~ UnsafeAccess m <{ new T t }> ad ->
  ~ UnsafeAccess m t ad.
Proof. solve_nuacc. Qed.

Lemma nuacc_load : forall m t ad,
  ~ UnsafeAccess m <{ *t }> ad ->
  ~ UnsafeAccess m t ad.
Proof. solve_nuacc. Qed.

Lemma nuacc_asg : forall m t1 t2 ad,
  ~ UnsafeAccess m <{ t1 = t2 }> ad ->
  ~ UnsafeAccess m t1 ad /\ ~ UnsafeAccess m t2 ad.
Proof. solve_nuacc. Qed.

Lemma nuacc_call : forall m t1 t2 ad,
  ~ UnsafeAccess m <{ call t1 t2 }> ad ->
  ~ UnsafeAccess m t1 ad /\ ~ UnsafeAccess m t2 ad.
Proof. solve_nuacc. Qed.

Lemma nuacc_seq : forall m t1 t2 ad,
  ~ UnsafeAccess m <{ t1; t2 }> ad ->
  ~ UnsafeAccess m t1 ad /\ ~ UnsafeAccess m t2 ad.
Proof. solve_nuacc. Qed.

Ltac inversion_nuacc :=
  match goal with
  | H: ~ UnsafeAccess _ <{ new _ _  }> _ |- _ => eapply nuacc_new  in H
  | H: ~ UnsafeAccess _ <{ * _      }> _ |- _ => eapply nuacc_load in H
  | H: ~ UnsafeAccess _ <{ _ = _    }> _ |- _ => eapply nuacc_asg  in H as [? ?]
  | H: ~ UnsafeAccess _ <{ call _ _ }> _ |- _ => eapply nuacc_call in H as [? ?]
  | H: ~ UnsafeAccess _ <{ _ ; _    }> _ |- _ => eapply nuacc_seq  in H as [? ?]
  end.

(* ------------------------------------------------------------------------- *)
(* core properties                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem nuacc_refI : forall m ad v T,
  value v ->
  empty |-- v is (TY_Immut T) ->
  ~ UnsafeAccess m v ad.
Proof.
  intros * Hval Htype Huacc. destruct Hval;
  inversion_type; inversion_uacc; eauto using UnsafeAccess.
Qed.

Theorem uacc_soundness : forall m m' t t' ad eff T,
  ad < length m ->
  empty |-- t is T ->
  ~ UnsafeAccess m t ad ->
  m / t ==[eff]==> m' / t' ->
  m[ad] = m'[ad].
Proof.
  intros * ? ? Hnuacc ?. rename ad into ad'. inversion_mstep; trivial.
  - decompose sum (lt_eq_lt_dec ad' (length m)); subst;
    simpl_array; trivial. lia.
  - decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array; trivial.
    generalize dependent T. induction_step; intros;
    inversion_nuacc; inversion_type; eauto using UnsafeAccess.
    inversion_type. exfalso. eauto using UnsafeAccess.
Qed.

Lemma uacc_then_acc : forall m t ad,
  UnsafeAccess m t ad ->
  access m t ad.
Proof.
  intros * Huacc. induction Huacc; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* mem -- set                                                                *)
(* ------------------------------------------------------------------------- *)

Local Lemma simpl_uacc : forall m ad ad' v,
  UnsafeAccess m[ad' <- v] m[ad' <- v][ad'] ad ->
  ad' < length m.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m)
    by (intros; split; destruct n; eauto).
  intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
  rewrite (get_set_invalid TM_Unit) in H; trivial. inversion H.
Qed.

Lemma mem_set_preserves_nuacc : forall m t ad ad' v,
  ~ UnsafeAccess m v ad ->
  ~ UnsafeAccess m t ad ->
  ~ UnsafeAccess m[ad' <- v] t ad.
Proof.
  intros * ? ? Huacc. remember (m[ad' <- v]) as m'.
  induction Huacc; inversion_subst_clear Heqm'; eauto using UnsafeAccess.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  destruct (Nat.eq_dec ad' ad'') as [? | Hneq]; subst;
  try (assert (ad'' < length m) by eauto using simpl_uacc);
  do 2 simpl_array; eauto using UnsafeAccess.
Qed.

(* ------------------------------------------------------------------------- *)
(* other properties                                                          *)
(* ------------------------------------------------------------------------- *)

Local Lemma contains_nuacc : forall m t t' ad,
  ~ UnsafeAccess m t ad ->
  t contains t' ->
  ~ UnsafeAccess m t' ad.
Proof.
  intros * ? Hcon ?. induction Hcon; subst; eauto;
  inversion_nuacc; eauto.
Qed.

Lemma mstep_write_preserves_nuacc : forall m m' t t' ad ad' v,
  ~ UnsafeAccess m t ad ->
  m / t ==[EF_Write ad' v]==> m' / t' ->
  ~ UnsafeAccess m' t' ad.
Proof.
  intros * ? ? ?. inversion_mstep. induction_step;
  inversion_nuacc; inversion_clear_uacc; eauto using UnsafeAccess;
  match goal with H : UnsafeAccess _ ?t _ |- _ => rename t into tx end;
  eapply (mem_set_preserves_nuacc _ tx _ _ v);
  eauto using step_write_contains_val, contains_nuacc.
Qed.

(* ------------------------------------------------------------------------- *)
(* safe memory sharing                                                       *)
(* ------------------------------------------------------------------------- *)

Local Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access m ths[tid1] ad ->
  access m ths[tid2] ad ->
  ~ UnsafeAccess m ths[tid1] ad.

Local Lemma length_tid : forall m m' t' ths tid eff,
  m / ths[tid] ==[eff]==> m' / t' ->
  tid < length ths.
Proof.
  intros * Hmstep.
  decompose sum (lt_eq_lt_dec tid (length ths)); subst; trivial;
  rewrite (get_default TM_Unit) in Hmstep; try lia;
  inversion_mstep; inversion_step.
Qed.

Lemma write_then_uacc : forall m t t' ad v T,
  empty |-- t is T ->
  t --[EF_Write ad v]--> t' ->
  UnsafeAccess m t ad.
Proof.
  intros * ? ?. generalize dependent T.
  induction_step; intros * ?;
  inversion_type; eauto using UnsafeAccess.
  inversion_type. eauto using UnsafeAccess.
Qed.

Local Lemma todo1 : forall m m' t ad ad' v ths tid1 tid2 T,
  tid1 <> tid2 ->
  safe_memory_sharing m ths ->
  empty |-- ths[tid1] is T ->
  m / ths[tid1] ==[EF_Write ad v]==> m' / t ->
  access m' t ad' ->
  access m' ths[tid2] ad' ->
  UnsafeAccess m' t ad' ->
  False.
Proof.
  intros * Hneq Hsms ? Hmstep ? ? Huacc. inversion Hmstep; subst.
  destruct (access_dec m ths[tid2] ad) as [Hacc2 | ?].
  - assert (Hacc1 : access m ths[tid1] ad)
      by eauto using mstep_write_requires_acc.
    specialize (Hsms _ _ _ Hneq Hacc1 Hacc2) as ?.
    eauto using write_then_uacc.
  - contradict Huacc.
    eauto using mstep_write_preserves_nuacc,
      mstep_write_inherits_acc,
      mem_set_inherits_acc2.
Qed.

Lemma mem_set_inherits_uacc1 : forall m t ad ad' v,
  ~ access m t ad' ->
  UnsafeAccess m[ad' <- v] t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * Hnacc Huacc. remember (m[ad' <- v]) as m'.
  induction Huacc; inversion_subst_clear Heqm'; inversion_not_access Hnacc;
  eauto using UnsafeAccess.
  do 2 simpl_array. eauto using UnsafeAccess.
Qed.

Local Lemma todo2 : forall m m' t ad ad' v ths tid1 tid2 T,
  tid1 <> tid2 ->
  safe_memory_sharing m ths ->
  empty |-- ths[tid1] is T ->
  m / ths[tid1] ==[EF_Write ad v]==> m' / t ->
  access m' t ad' ->
  access m' ths[tid2] ad' ->
  UnsafeAccess m' ths[tid2] ad' ->
  False.
Proof.
  intros * Hneq Hsms ? Hmstep ? ? Huacc. inversion Hmstep; subst.
  destruct (access_dec m ths[tid2] ad) as [Hacc2 | ?].
  - assert (Hacc1 : access m ths[tid1] ad)
      by eauto using mstep_write_requires_acc.
    specialize (Hsms _ _ _ Hneq Hacc1 Hacc2) as ?.
    eauto using write_then_uacc.
  - assert (~ UnsafeAccess m ths[tid1] ad'); (* TODO *)
    assert (~ UnsafeAccess m ths[tid2] ad');
    eauto using mem_set_inherits_uacc1,
      mstep_write_inherits_acc,
      mem_set_inherits_acc2.
Qed.

Local Lemma todo3 : forall m m' t ad ad' v ths tid tid1 tid2 T,
  tid1 <> tid2 ->
  safe_memory_sharing m ths ->
  empty |-- ths[tid1] is T ->
  m / ths[tid] ==[EF_Write ad v]==> m' / t ->
  access m' t ad' ->
  access m' ths[tid2] ad' ->
  UnsafeAccess m' ths[tid2] ad' ->
  False.
Proof.
  intros * Hneq Hsms ? Hmstep ? ? Huacc. inversion Hmstep; subst.
Abort.

Lemma not_sharing : forall m t ad v ths tid tid',
  tid <> tid' ->
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  safe_memory_sharing m ths ->
  ths[tid] --[EF_Write ad v]--> t ->
  ~ access m ths[tid'] ad.
Proof.
  intros * Hneq Htype Hsms ? F.
  assert (Hacc : access m ths[tid] ad) by eauto using step_write_requires_acc.
  destruct (Htype tid).
  specialize (Hsms _ _ _ Hneq Hacc F) as ?.
  eauto using write_then_uacc.
Qed.

Local Lemma mstep_write_sms_preservation : forall m m' ths t' tid ad v,
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[EF_Write ad v]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * Htype Hsms Hmstep tid1 tid2 ad' Hneq ? ? Huacc.
  assert (Hlen : tid < length ths) by eauto using length_tid.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  do 3 simpl_array.
  - destruct (Htype tid1). eauto using todo1.
  - destruct (Htype tid2). eauto using todo2.
  - inversion Hmstep; subst.
    assert (~ access m ths[tid1] ad) by eauto using not_sharing.
    assert (~ access m ths[tid2] ad) by eauto using not_sharing.
    assert (access m ths[tid1] ad') by eauto using mem_set_inherits_acc2.
    assert (access m ths[tid2] ad') by eauto using mem_set_inherits_acc2.
    assert (~ UnsafeAccess m ths[tid1] ad');
    assert (~ UnsafeAccess m ths[tid2] ad');
    eauto using mem_set_inherits_uacc1,
      mstep_write_inherits_acc,
      mem_set_inherits_acc2.
Qed.

(* ------------------------------------------------------------------------- *)
(* to remove & unused                                                        *)
(* ------------------------------------------------------------------------- *)

Lemma todo1 : forall m t t' ad v,
  t --[EF_Write ad v]--> t' ->
  access m[ad <- v] t ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma mem_set_inherits_uacc1 : forall m t ad ad' v,
  ~ access m t ad' ->
  UnsafeAccess m[ad' <- v] t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * Hnacc Huacc. remember (m[ad' <- v]) as m'.
  induction Huacc; inversion_subst_clear Heqm'; inversion_not_access Hnacc;
  eauto using UnsafeAccess.
  do 2 simpl_array. eauto using UnsafeAccess.
Qed.

Lemma mem_set_inherits_uacc2 : forall m t ad ad' v,
  ~ access m v ad ->
  UnsafeAccess m[ad' <- v] t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * Hnacc Huacc. remember (m[ad' <- v]) as m'.
  induction Huacc; try rename IHHuacc into IH;
  inversion_subst_clear Heqm'; eauto using UnsafeAccess.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end.
  destruct (Nat.eq_dec ad' ad''); subst;
  try solve [do 2 simpl_array; eauto using UnsafeAccess].
  destruct (Nat.eq_dec ad'' ad); subst; eauto using UnsafeAccess.
  auto_specialize. contradict Hnacc.
  rewrite (get_set_eq TM_Unit) in IH; eauto using uacc_then_acc.
  eapply not_le. intros Hlen. do 3 simpl_array. 
  eapply le_lt_or_eq in Hlen as [? | ?]; subst;
  do 2 simpl_array; inversion_uacc.
Qed.

Local Lemma todo : forall m t t' ad ad' v,
  ~ UnsafeAccess m[ad' <- v] t' ad ->
  t --[EF_Write ad' v]--> t' ->
  ~ UnsafeAccess m t ad.
Proof.
  intros * Hnuacc Hstep Huacc. induction_step;
  try solve [inversion_nuacc; inversion_uacc; eauto].
  - inversion_nuacc. inversion_uacc; eauto using UnsafeAccess.
Abort.

Lemma mstep_write_inherits_uacc : forall m m' t t' ad ad' v,
  UnsafeAccess m' t' ad ->
  m / t ==[EF_Write ad' v]==> m' / t' ->
  UnsafeAccess m t ad.
Proof.
  intros * Huacc ?. inversion_mstep. induction_step;
  try solve [inversion_uacc; eauto using UnsafeAccess].
  - inversion_uacc; eauto using UnsafeAccess.
    destruct (uacc_dec m[ad' <- v] t1' ad); eauto using UnsafeAccess.
    clear IHstep.
    eapply uacc_asg2.
    destruct (uacc_dec m v ad). 
    + destruct (access_dec m t2 ad'); eauto using mem_set_inherits_uacc1.
      admit.
    + destruct (uacc_dec m t2 ad); trivial; exfalso.
      contradict H3. eauto using (mem_set_preserves_nuacc _ t2).
  - admit.
  - admit.
  - admit.
  - admit.
Abort.

