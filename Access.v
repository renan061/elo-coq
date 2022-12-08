From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import HasAddress.
From Elo Require Import ValidAddresses.

(* A term accesses an address if it refers to the address directly or 
indirectly. Ignores <spawn> blocks. *)
Inductive access (m : mem) : tm -> addr -> Prop :=
  | acc_mem : forall ad ad' T,
    ad <> ad' ->
    access m m[ad'].tm ad ->
    access m <{ &ad' :: T }> ad

  | acc_ref : forall ad T,
    access m <{ &ad :: T }> ad

  | acc_new : forall T t ad,
    access m t ad ->
    access m <{ new T t }> ad

  | acc_load : forall t ad,
    access m t ad ->
    access m <{ *t }> ad

  | acc_asg1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ t1 = t2 }> ad

  | acc_asg2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ t1 = t2 }> ad

  | acc_fun : forall x Tx t ad,
    access m t ad ->
    access m <{ fn x Tx --> t }> ad

  | acc_call1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ call t1 t2 }> ad

  | acc_call2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ call t1 t2 }> ad

  | acc_seq1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ t1; t2 }> ad

  | acc_seq2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ t1; t2 }> ad
  .

Ltac inversion_acc :=
  match goal with
  | H : access _ <{ unit         }> _ |- _ => inversion H
  | H : access _ <{ N _          }> _ |- _ => inversion H
  | H : access _ <{ & _ :: _     }> _ |- _ => inversion H; subst
  | H : access _ <{ new _ _      }> _ |- _ => inversion H; subst
  | H : access _ <{ * _          }> _ |- _ => inversion H; subst
  | H : access _ <{ _ = _        }> _ |- _ => inversion H; subst
  | H : access _ <{ var _        }> _ |- _ => inversion H
  | H : access _ <{ fn _ _ --> _ }> _ |- _ => inversion H; subst
  | H : access _ <{ call _ _     }> _ |- _ => inversion H; subst
  | H : access _ <{ _ ; _        }> _ |- _ => inversion H; subst
  | H : access _ <{ spawn _      }> _ |- _ => inversion H
  end.

Ltac inversion_clear_acc :=
  match goal with
  | H : access _ <{ unit         }> _ |- _ => inversion H
  | H : access _ <{ N _          }> _ |- _ => inversion H
  | H : access _ <{ & _ :: _     }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ new _ _      }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ * _          }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ _ = _        }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ var _        }> _ |- _ => inversion H
  | H : access _ <{ fn _ _ --> _ }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ call _ _     }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ _ ; _        }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ spawn _      }> _ |- _ => inversion H
  end.

(* ------------------------------------------------------------------------- *)
(* properties                                                                *)
(* ------------------------------------------------------------------------- *)

(* strong acc_mem *)
Theorem acc_mem_trans : forall m t ad ad',
  ad <> ad' ->
  access m t ad' ->
  access m m[ad'].tm ad ->
  access m t ad.
Proof.
  intros * ? Hacc ?. induction Hacc; eauto using access.
  destruct (Nat.eq_dec ad ad'); subst; eauto using access.
Qed.

Lemma acc_length : forall m ad ad',
  access m m[ad'].tm ad ->
  ad' < #m.
Proof.
  intros * Hacc. decompose sum (lt_eq_lt_dec ad' (#m)); subst; trivial;
  simpl_array; try lia; inversion Hacc.
Qed.

Lemma acc_dec : forall m t ad,
  Decidable.decidable (access m t ad).
Proof. eauto using classic_decidable. Qed.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Inductive not_access (m : mem) : tm -> addr -> Prop :=
  | nacc_unit : forall ad,
    not_access m <{ unit }> ad

  | nacc_num : forall n ad,
    not_access m <{ N n }> ad

  | nacc_ref : forall T ad ad',
    ad <> ad' ->
    ~ access m m[ad].tm ad' ->
    not_access m <{ &ad :: T }> ad'

  | nacc_new : forall T t ad,
    ~ access m t ad ->
    not_access m <{ new T t }> ad

  | nacc_load : forall t ad,
    ~ access m t ad ->
    not_access m <{ *t }> ad

  | nacc_asg : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1 = t2 }> ad

  | nacc_var : forall x ad,
    not_access m <{ var x }> ad

  | nacc_fun : forall x Tx t ad,
    ~ access m t ad ->
    not_access m <{ fn x Tx --> t }> ad

  | nacc_call : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ call t1 t2 }> ad

  | nacc_seq : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1; t2 }> ad

  | nacc_spawn : forall t ad,
    not_access m <{ spawn t }> ad
  .

Theorem nacc_iff : forall m t ad,
  ~ access m t ad <-> not_access m t ad.
Proof.
  intros. split; intros Hnacc; destruct t;
  try (eapply nacc_ref
    || eapply nacc_asg
    || eapply nacc_call
    || eapply nacc_seq);
  eauto using access, not_access;
  intros ?; subst;
  try (inversion_acc; inversion_clear Hnacc); eauto using access.
  match goal with
  | Hnacc : ~ access _ <{ & ?ad :: _ }> ?ad' |- _ =>
    destruct (Nat.eq_dec ad ad'); subst; eauto using access
  end.
Qed.

Ltac inversion_nacc Hnacc :=
  eapply nacc_iff in Hnacc; inversion Hnacc; subst; eauto using access.

(* ------------------------------------------------------------------------- *)
(* valid-accesses                                                            *)
(* ------------------------------------------------------------------------- *)

Definition valid_accesses (m : mem) (t : tm) :=
  forall ad, access m t ad -> ad < length m.

Lemma vac_length : forall m t ad,
  valid_accesses m t ->
  access m t ad ->
  ad < #m.
Proof.
  intros * Hvac Hacc.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; trivial.
  - specialize (Hvac (#m) Hacc). lia.
  - specialize (Hvac ad Hacc). lia.
Qed.

Lemma vac_nacc_length : forall m t,
  valid_accesses m t ->
  ~ access m t (#m).
Proof.
  intros * ? F. eapply vac_length in F; eauto. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* inversion -- valid-accesses                                               *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vac_inversion := 
  intros; unfold valid_accesses in *; try split; eauto using access.

Local Lemma inv_vac_ref : forall m ad T,
  valid_accesses m <{ &ad :: T }> ->
  valid_accesses m m[ad].tm.
Proof.
  intros; unfold valid_accesses in *; eauto using access.
  intros ad'. destruct (Nat.eq_dec ad ad'); subst; eauto using access.
Qed.

Local Lemma inv_vac_new : forall m t T,
  valid_accesses m <{ new T t }> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_load : forall m t,
  valid_accesses m <{ *t }> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_asg : forall m t1 t2,
  valid_accesses m <{ t1 = t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_fun : forall m x Tx t,
  valid_accesses m <{ fn x Tx --> t }> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_call : forall m t1 t2,
  valid_accesses m <{ call t1 t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_seq : forall m t1 t2,
  valid_accesses m <{ t1; t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Ltac inversion_vac :=
  match goal with
  | H: valid_accesses _ <{ &_ :: _  }> |- _ => eapply inv_vac_ref  in H as Hwba'
  | H: valid_accesses _ <{ new _ _  }> |- _ => eapply inv_vac_new  in H
  | H: valid_accesses _ <{ * _      }> |- _ => eapply inv_vac_load in H
  | H: valid_accesses _ <{ _ = _    }> |- _ => eapply inv_vac_asg  in H as [? ?]
  | H: valid_accesses _ <{ fn _ _ --> _ }> |- _ => eapply inv_vac_fun in H
  | H: valid_accesses _ <{ call _ _ }> |- _ => eapply inv_vac_call in H as [? ?]
  | H: valid_accesses _ <{ _ ; _    }> |- _ => eapply inv_vac_seq  in H as [? ?]
  end.

(* ------------------------------------------------------------------------- *)
(* valid-accesses derives from valid-addresses                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma acc_then_hasad : forall m t ad,
  access m t ad ->
  HasAddress ad t \/ (exists ad', HasAddress ad m[ad'].tm).
Proof.
  intros * Hacc.
  induction Hacc; try destruct IHHacc as [? | [? ?]]; eauto using HasAddress.
Qed.

Theorem vad_then_vac : forall m t,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  valid_accesses m t.
Proof.
  intros. intros ? ?. unfold forall_memory in *. unfold valid_addresses in *.
  assert (HasAddress ad t \/ (exists ad', HasAddress ad m[ad'].tm))
    as [? | [? ?]];
  eauto using acc_then_hasad.
Qed.

Theorem vad_then_mem_vac : forall m t,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  forall_memory m (valid_accesses m).
Proof.
  intros. intros ad' ? ?.
  unfold forall_memory in *. unfold valid_addresses in *.
  assert (HasAddress ad m[ad'].tm \/ (exists ad'', HasAddress ad m[ad''].tm))
    as [? | [? ?]];
  eauto using acc_then_hasad.
Qed.

Corollary forall_threads_vad_then_vac : forall m ths,
  forall_threads ths (valid_addresses m) ->
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_accesses m).
Proof.
  intros. intros ?. eauto using vad_then_vac.
Qed.

(* ------------------------------------------------------------------------- *)
(* access properties -- subst                                                *)
(* ------------------------------------------------------------------------- *)

Lemma subst_acc : forall m x Tx t t' ad,
  access m ([x := t'] t) ad ->
  access m <{ call <{ fn x Tx --> t }> t' }> ad.
Proof.
  intros. induction t; eauto using access; simpl in *;
  try (destruct String.string_dec; eauto using access);
  inversion_clear_acc; auto_specialize; do 2 inversion_acc; eauto using access.
Qed.

Local Lemma subst_nacc' : forall m t tx ad x,
  ~ access m t ad ->
  ~ access m tx ad ->
  ~ access m ([x := tx] t) ad.
Proof.
  intros * Hnacc ?. generalize dependent tx.
  induction t; intros; trivial; simpl;
  try solve [eapply nacc_iff; inversion_nacc Hnacc; eauto using not_access];
  destruct String.string_dec; trivial.
  inversion_nacc Hnacc. eapply nacc_iff. eauto using not_access.
Qed.

Lemma subst_nacc : forall m t tx ad x Tx,
  ~ access m <{ fn x Tx --> t }> ad ->
  ~ access m tx ad ->
  ~ access m ([x := tx] t) ad.
Proof.
  intros * Hnacc ?. inversion_nacc Hnacc; eauto using subst_nacc'.
Qed.

(* ------------------------------------------------------------------------- *)
(* access properties -- memory                                               *)
(* ------------------------------------------------------------------------- *)

Lemma mem_add_acc : forall m t ad vTr,
  ~ access m t (#m) ->
  access (m +++ vTr) t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (m +++ vTr) as m'.
  induction Hacc; inversion Heqm'; subst; inversion_nacc Hnacc.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; try lia;
  simpl_array; eauto using access. simpl in *. inversion_acc.
Qed.

Lemma mem_set_acc : forall m t ad ad' vTr,
  ~ access m t ad' ->
  access m[ad' <- vTr] t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc.  remember (m[ad' <- vTr]) as m'.
  induction Hacc; inversion_subst_clear Heqm'; inversion_nacc Hnacc;
  simpl_array; eauto using access.
Qed.

Local Lemma mem_set_acc' : forall m t ad ad' v Tr,
  ~ access m v ad ->
  access m[ad' <- (v, Tr)] t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (m[ad' <- (v, Tr)]) as m'.
  induction Hacc; try rename IHHacc into IH;
  inversion_subst_clear Heqm'; eauto using access.
  match goal with |- access _ <{ & ?ad :: _ }> _ => rename ad into ad'' end.
  destruct (Nat.eq_dec ad' ad''); subst;
  try simpl_array; eauto using access;
  destruct (Nat.eq_dec ad'' ad); subst; eauto using access.
  auto_specialize. rewrite (get_set_eq memory_default) in IH. 1: contradiction.
  eapply not_le. intros Hlen. simpl_array. 
  eapply Nat.lt_eq_cases in Hlen as [? | ?]; subst;
  simpl_array; simpl in *; inversion_acc.
Qed.

(* ------------------------------------------------------------------------- *)
(* access properties -- inheritance                                          *)
(* ------------------------------------------------------------------------- *)

Lemma step_none_inherits_access : forall m t t' ad,
  access m t' ad ->
  t --[EF_None]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; try inversion_acc; eauto using access, subst_acc.
Qed.

Lemma step_alloc_inherits_acc : forall m t t' ad v Tr,
  valid_accesses m t ->
  ad <> #m ->
  access (m +++ (v, Tr)) t' ad ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  access m t ad.
Proof.
  intros. induction_step;
  inversion_vac; inversion_acc; eauto using access; try lia; try simpl_array;
  eauto using mem_add_acc, vac_nacc_length, access.
Qed.

Lemma step_read_inherits_acc : forall m t t' ad ad',
  access m t' ad ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; try inversion_acc; eauto using access.
  destruct (Nat.eq_dec ad' ad); subst; eauto using access.
Qed.

Lemma step_write_inherits_acc : forall m t t' ad ad' v Tr,
  access m[ad' <- (v, Tr)] t' ad ->
  t --[EF_Write ad' v Tr]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; inversion_acc; eauto using access;
  destruct (acc_dec m v ad); eauto using mem_set_acc', access;
  assert (forall t t', t --[EF_Write ad' v Tr]--> t' -> access m t ad)
    by (intros; induction_step; eauto using access);
  eauto using access.
Qed.

Lemma step_spawn_inherits_acc : forall m t t' block ad,
  access m t' ad ->
  t --[EF_Spawn block]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; inversion_acc; eauto using access.
Qed.

