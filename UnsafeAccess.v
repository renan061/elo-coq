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

Lemma nuacc_mem : forall m ad ad' T,
  ad <> ad' ->
  ~ UnsafeAccess m <{ &ad' :: &T }> ad ->
  ~ UnsafeAccess m m[ad'] ad.
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

Lemma nacc_then_nuacc : forall m t ad,
  ~ access m t ad ->
  ~ UnsafeAccess m t ad.
Proof.
  intros * ? F. induction F; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* subst                                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma nuacc_subst : forall m t ad v x,
  ~ UnsafeAccess m v ad ->
  ~ UnsafeAccess m t ad ->
  ~ UnsafeAccess m ([x := v] t) ad.
Proof.
  intros. intros ?. induction t; eauto; simpl in *;
  try (destruct String.string_dec; eauto);
  inversion_uacc; inversion_nuacc; eauto.
Qed.

Corollary nuacc_subst_call : forall m t ad v x Tx,
  ~ UnsafeAccess m v ad ->
  ~ UnsafeAccess m <{ fn x Tx --> t }> ad ->
  ~ UnsafeAccess m ([x := v] t) ad.
Proof.
  intros. inversion_nuacc. eauto using nuacc_subst.
Qed.

(* ------------------------------------------------------------------------- *)
(* mem                                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma mem_add_uacc : forall m t ad v,
  ~ access m t (length m) ->
  UnsafeAccess (m +++ v) t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * Hnacc Huacc. remember (m +++ v) as m'.
  induction Huacc; inversion Heqm'; subst; inversion_not_access Hnacc;
  eauto using UnsafeAccess.
  eapply uacc_mem; trivial.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst;
  do 2 simpl_array; eauto; do 2 simpl_array; eauto; lia.
Qed.

Lemma mem_add_nuacc : forall m t ad v,
  ~ UnsafeAccess m t (length m) ->
  ~ UnsafeAccess m t ad ->
  ~ UnsafeAccess (m +++ v) t ad.
Proof.
  intros. intros Huacc.
  induction Huacc; eauto using UnsafeAccess; inversion_nuacc;
  try solve [inversion_nuacc; eauto using UnsafeAccess].
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; do 2 simpl_array;
  try inversion_uacc; eauto using UnsafeAccess.
  assert (length m <> ad') by eauto using Nat.lt_neq, Nat.neq_sym.
  inversion_nuacc. eauto.
Qed.

Lemma mem_set_uacc : forall m t ad ad' v,
  ~ access m t ad' ->
  UnsafeAccess m[ad' <- v] t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * Hnacc Huacc. remember (m[ad' <- v]) as m'.
  induction Huacc; inversion_subst_clear Heqm'; inversion_not_access Hnacc;
  eauto using UnsafeAccess. do 2 simpl_array. eauto using UnsafeAccess.
Qed.

Lemma mem_set_nuacc : forall m t ad ad' v,
  ~ UnsafeAccess m v ad ->
  ~ UnsafeAccess m t ad ->
  ~ UnsafeAccess m[ad' <- v] t ad.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m)
    by (intros; split; destruct n; eauto).
  assert (Hlen : forall m ad ad' v,
    UnsafeAccess m[ad' <- v] m[ad' <- v][ad'] ad ->
    ad' < length m). {
    intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
    rewrite (get_set_invalid TM_Unit) in H; trivial. inversion H.
  }
  (* main proof *)
  intros * ? ? Huacc. remember (m[ad' <- v]) as m'.
  induction Huacc; inversion_subst_clear Heqm'; eauto using UnsafeAccess.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  destruct (Nat.eq_dec ad' ad'') as [? | Hneq]; subst;
  try (assert (ad'' < length m) by eauto using Hlen);
  do 2 simpl_array; eauto using UnsafeAccess.
Qed.

(* ------------------------------------------------------------------------- *)
(* step-preserves-nuacc                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_alloc_value_nacc : forall m t t' v,
  valid_accesses m t ->
  t --[EF_Alloc (length m) v]--> t' ->
  ~ access m v (length m).
Proof.
  intros * Hva ?. induction_step; inversion_va; eauto using access.
  intros F. specialize (Hva (length m) F). lia.
Qed.

Local Lemma contains_nuacc : forall m t t' ad,
  ~ UnsafeAccess m t ad ->
  t contains t' ->
  ~ UnsafeAccess m t' ad.
Proof.
  intros * ? Hcon ?. induction Hcon; subst; eauto; inversion_nuacc; eauto.
Qed.

Lemma step_none_preserves_nuacc : forall m t t' ad,
  ~ UnsafeAccess m t ad ->
  t --[EF_None]--> t' ->
  ~ UnsafeAccess m t' ad.
Proof.
  intros. intros F. induction_step;
  inversion_nuacc; try contradiction;
  try inversion_clear_uacc; eauto using UnsafeAccess.
  contradict F. eauto using nuacc_subst_call.
Qed.

Lemma step_alloc_preserves_nuacc : forall m t t' ad v,
  ad <> length m ->
  valid_accesses m t ->
  ~ UnsafeAccess m t ad ->
  t --[EF_Alloc (length m) v]--> t' ->
  ~ UnsafeAccess (m +++ v) t' ad.
Proof.
  intros. intros ?. induction_step;
  inversion_va; inversion_nuacc; inversion_uacc;
  eauto using UnsafeAccess; try simpl_array;
  match goal with F : UnsafeAccess (_ +++ _) _ _ |- _ => contradict F end;
  eauto using mem_add_nuacc, va_nacc_length, nacc_then_nuacc.
Qed.

Lemma step_read_preserves_nuacc : forall m t t' ad ad' T,
  forall_memory m value ->
  empty |-- t is T ->
  well_typed_references m t ->
  ~ UnsafeAccess m t ad ->
  t --[EF_Read ad' m[ad']]--> t' ->
  ~ UnsafeAccess m t' ad.
Proof.
  intros * Hval ? Hwtr ? ? ?. generalize dependent T. induction_step; intros;
  inversion_wtr m; inversion_type; inversion_nuacc; try inversion_clear_uacc;
  eauto; inversion_type; destruct (Nat.eq_dec ad' ad); subst;
  eauto using UnsafeAccess;
  inversion_wtr m; contradict H2; eauto using nuacc_refI. (* TODO *)
Qed.

Lemma step_write_preserves_nuacc : forall m t t' ad ad' v,
  ~ UnsafeAccess m t ad ->
  t --[EF_Write ad' v]--> t' ->
  ~ UnsafeAccess m[ad' <- v] t' ad.
Proof.
  intros. intros ?. induction_step;
  inversion_nuacc; inversion_clear_uacc; eauto using UnsafeAccess;
  match goal with H : UnsafeAccess _ ?t _ |- _ => rename t into tx end;
  eapply (mem_set_nuacc _ tx _ _ v);
  eauto using step_write_contains_val, contains_nuacc.
Qed.

Lemma step_spawn_preserves_nuacc : forall m t t' ad block,
  ~ UnsafeAccess m t ad ->
  t --[EF_Spawn block]--> t' ->
  ~ UnsafeAccess m t' ad.
Proof.
  intros. intros ?. induction_step; try inversion_nuacc; inversion_uacc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* step-inherits-uacc                                                        *)
(* ------------------------------------------------------------------------- *)

Lemma step_spawn_inherits_uacc : forall m t t' ad block,
  UnsafeAccess m t' ad ->
  t --[EF_Spawn block]--> t' ->
  UnsafeAccess m t ad.
Proof.
  intros. induction_step; inversion_uacc; eauto using UnsafeAccess.
Qed.

