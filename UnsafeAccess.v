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

(* There is a mutable pointer to <ad> in the term. *)
Inductive UnsafeAccess (m : mem) : tm -> addr -> Prop :=
  | uacc_mem : forall ad ad' T,
    ad <> ad' ->
    UnsafeAccess m m[ad'].tm ad ->
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

Lemma nuacc_unit : forall m ad,
  ~ UnsafeAccess m <{ unit }> ad.
Proof. intros * ?. inversion_uacc. Qed.

Lemma nuacc_mem : forall m ad ad' T,
  ad <> ad' ->
  ~ UnsafeAccess m <{ &ad' :: &T }> ad ->
  ~ UnsafeAccess m m[ad'].tm ad.
Proof. solve_nuacc. Qed.

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

Lemma nuacc_fun : forall m t ad x Tx,
  ~ UnsafeAccess m <{ fn x Tx --> t }> ad ->
  ~ UnsafeAccess m t ad.
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
  | H: ~ UnsafeAccess _ <{ & ?ad' :: _ }> ?ad, Hneq : ?ad <> ?ad' |- _ =>
    eapply (nuacc_mem _ _ _ _ Hneq) in H
  | H: ~ UnsafeAccess _ <{ new _ _  }> _ |- _ => eapply nuacc_new  in H
  | H: ~ UnsafeAccess _ <{ * _      }> _ |- _ => eapply nuacc_load in H
  | H: ~ UnsafeAccess _ <{ _ = _    }> _ |- _ => eapply nuacc_asg  in H as [? ?]
  | H: ~ UnsafeAccess _ <{ fn _ _ --> _ }> _ |- _ => eapply nuacc_fun in H
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
  intros * Hval ? ?. destruct Hval;
  inversion_type; inversion_uacc; eauto using UnsafeAccess.
Qed.

Theorem uacc_soundness : forall m m' t t' ad eff T,
  ad < #m ->
  empty |-- t is T ->
  ~ UnsafeAccess m t ad ->
  m / t ==[eff]==> m' / t' ->
  m[ad].tm = m'[ad].tm.
Proof.
  intros. rename ad into ad'. inversion_clear_mstep; trivial.
  - decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; trivial. lia.
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

Lemma nacc_then_nuacc : forall m t ad,
  ~ access m t ad ->
  ~ UnsafeAccess m t ad.
Proof.
  intros * ? Huacc. induction Huacc; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* helpers                                                                   *)
(* ------------------------------------------------------------------------- *)

Local Lemma subst_nuacc' : forall m t ad v x,
  ~ UnsafeAccess m v ad ->
  ~ UnsafeAccess m t ad ->
  ~ UnsafeAccess m ([x := v] t) ad.
Proof.
  intros. intros ?. induction t; eauto; simpl in *;
  try (destruct String.string_dec; eauto);
  inversion_uacc; inversion_nuacc; eauto.
Qed.

Local Corollary subst_nuacc : forall m t ad v x Tx,
  ~ UnsafeAccess m v ad ->
  ~ UnsafeAccess m <{ fn x Tx --> t }> ad ->
  ~ UnsafeAccess m ([x := v] t) ad.
Proof.
  intros. inversion_nuacc. eauto using subst_nuacc'.
Qed.

Lemma mem_add_uacc : forall m t ad vTr,
  ~ access m t (#m) ->
  UnsafeAccess (m +++ vTr) t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * Hnacc Huacc. remember (m +++ vTr) as m'.
  induction Huacc; inversion Heqm'; subst; inversion_nacc Hnacc;
  eauto using UnsafeAccess.
  eapply uacc_mem; trivial.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; eauto; lia.
Qed.

Local Lemma mem_add_nuacc : forall m t ad vTr,
  ~ UnsafeAccess m t (#m) ->
  ~ UnsafeAccess m t ad ->
  ~ UnsafeAccess (m +++ vTr) t ad.
Proof.
  intros. intros Huacc.
  induction Huacc; eauto using UnsafeAccess; inversion_nuacc;
  eauto using UnsafeAccess.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array;
  simpl in *; try inversion_uacc; eauto using UnsafeAccess.
  assert (#m <> ad') by eauto using Nat.lt_neq, Nat.neq_sym.
  inversion_nuacc. eauto.
Qed.

Lemma mem_set_uacc : forall m t ad ad' vTr,
  ~ access m t ad' ->
  UnsafeAccess m[ad' <- vTr] t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * Hnacc Huacc. remember (m[ad' <- vTr]) as m'.
  induction Huacc; inversion_subst_clear Heqm'; inversion_nacc Hnacc;
  eauto using UnsafeAccess. simpl_array. eauto using UnsafeAccess.
Qed.

Local Lemma mem_set_nuacc : forall m t ad ad' v Tr,
  ~ UnsafeAccess m v ad ->
  ~ UnsafeAccess m t ad ->
  ~ UnsafeAccess m[ad' <- (v, Tr)] t ad.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m)
    by (intros; split; destruct n; eauto).
  assert (Hlen : forall m ad ad' v Tr,
    UnsafeAccess m[ad' <- (v, Tr)] m[ad' <- (v, Tr)][ad'].tm ad ->
    ad' < #m). {
    intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
    rewrite (get_set_invalid memory_default) in H; trivial. inversion H.
  }
  (* main proof *)
  intros * ? ? Huacc. remember (m[ad' <- (v, Tr)]) as m'.
  induction Huacc; inversion_subst_clear Heqm'; eauto using UnsafeAccess.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  destruct (Nat.eq_dec ad' ad'') as [? | Hneq]; subst;
  try (assert (ad'' < #m) by eauto using Hlen);
  simpl_array; eauto using UnsafeAccess.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation-nuacc                                                        *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_alloc_nacc_value : forall m t t' v Tr,
  valid_accesses m t ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  ~ access m v (#m).
Proof.
  intros * Hvac ?. induction_step; inversion_vac; eauto using access.
  intros F. specialize (Hvac (#m) F). lia.
Qed.

Local Lemma contains_nuacc : forall m t t' ad,
  ~ UnsafeAccess m t ad ->
  t contains t' ->
  ~ UnsafeAccess m t' ad.
Proof.
  intros * ? Hcon ?. induction Hcon; subst; eauto; inversion_nuacc; eauto.
Qed.

Lemma step_none_nuacc_preservation : forall m t t' ad,
  ~ UnsafeAccess m t ad ->
  t --[EF_None]--> t' ->
  ~ UnsafeAccess m t' ad.
Proof.
  intros. intros F. induction_step;
  inversion_nuacc; try contradiction;
  try inversion_clear_uacc; eauto using UnsafeAccess.
  contradict F. eauto using subst_nuacc.
Qed.

Lemma step_alloc_nuacc_preservation : forall m t t' ad v Tr,
  ad <> #m ->
  valid_accesses m t ->
  ~ UnsafeAccess m t ad ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  ~ UnsafeAccess (m +++ (v, Tr)) t' ad.
Proof.
  intros. intros ?. induction_step;
  inversion_vac; inversion_nuacc; inversion_uacc;
  eauto using UnsafeAccess; try simpl_array;
  match goal with F : UnsafeAccess (_ +++ _) _ _ |- _ => contradict F end;
  eauto using mem_add_nuacc, vac_nacc_length, nacc_then_nuacc.
Qed.

Lemma step_read_nuacc_preservation : forall m t t' ad ad' T,
  forall_memory m value ->
  empty |-- t is T ->
  well_typed_references m t ->
  ~ UnsafeAccess m t ad ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  ~ UnsafeAccess m t' ad.
Proof.
  intros * Hval. intros. intros ?. generalize dependent T.
  induction_step; intros;
  inversion_wtr; inversion_type; inversion_nuacc; try inversion_clear_uacc;
  eauto; inversion_type; destruct (Nat.eq_dec ad' ad); subst;
  eauto using UnsafeAccess; inversion_wtr;
  match goal with F : UnsafeAccess _ _[_].tm _ |- _ => contradict F end;
  eauto using nuacc_refI.
Qed.

Lemma step_write_nuacc_preservation : forall m t t' ad ad' v Tr,
  ~ UnsafeAccess m t ad ->
  t --[EF_Write ad' v Tr]--> t' ->
  ~ UnsafeAccess m[ad' <- (v, Tr)] t' ad.
Proof.
  intros. intros ?. induction_step;
  inversion_nuacc; inversion_clear_uacc; eauto using UnsafeAccess;
  match goal with H : UnsafeAccess _ ?t _ |- _ => rename t into tx end;
  eapply (mem_set_nuacc _ tx _ _ v);
  eauto using step_write_contains, contains_nuacc.
Qed.

Lemma step_spawn_nuacc_preservation : forall m t t' ad block,
  ~ UnsafeAccess m t ad ->
  t --[EF_Spawn block]--> t' ->
  ~ UnsafeAccess m t' ad.
Proof.
  intros. intros ?. induction_step; try inversion_nuacc; inversion_uacc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* inheritance-uacc                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma step_spawn_uacc_inheritance : forall m t t' ad block,
  UnsafeAccess m t' ad ->
  t --[EF_Spawn block]--> t' ->
  UnsafeAccess m t ad.
Proof.
  intros. induction_step; inversion_uacc; eauto using UnsafeAccess.
Qed.

