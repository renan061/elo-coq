From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import Contains.
From Elo Require Import Access.
From Elo Require Import References.

(* There is a mutable pointer to <ad> in the term. *)
Inductive unsafe_access (ad : addr) (m : mem) : tm  -> Prop :=
  | uacc_mem : forall ad' T,
    ad <> ad' ->
    unsafe_access ad m (m[ad'].tm) ->
    unsafe_access ad m <{&ad' :: &T}>

  | uacc_ad : forall T,
    unsafe_access ad m <{&ad :: &T}>

  | uacc_new : forall T t,
    unsafe_access ad m t ->
    unsafe_access ad m <{new T t}>

  | uacc_load : forall t,
    unsafe_access ad m t ->
    unsafe_access ad m <{*t}>

  | uacc_asg1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{t1 = t2}>

  | uacc_asg2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{t1 = t2}>

  | uacc_fun : forall x Tx t,
    unsafe_access ad m t ->
    unsafe_access ad m <{fn x Tx t}>

  | uacc_call1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{call t1 t2}>

  | uacc_call2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{call t1 t2}>

  | uacc_seq1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{t1; t2}>

  | uacc_seq2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{t1; t2}>
  .

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_uacc tactic :=
  match goal with
  | H : unsafe_access _ _ <{unit    }> |- _ => tactic H
  | H : unsafe_access _ _ <{N _     }> |- _ => tactic H
  | H : unsafe_access _ _ <{& _ :: _}> |- _ => tactic H
  | H : unsafe_access _ _ <{new _ _ }> |- _ => tactic H
  | H : unsafe_access _ _ <{* _     }> |- _ => tactic H
  | H : unsafe_access _ _ <{_ = _   }> |- _ => tactic H
  | H : unsafe_access _ _ <{var _   }> |- _ => tactic H
  | H : unsafe_access _ _ <{fn _ _ _}> |- _ => tactic H
  | H : unsafe_access _ _ <{call _ _}> |- _ => tactic H
  | H : unsafe_access _ _ <{_ ; _   }> |- _ => tactic H
  | H : unsafe_access _ _ <{spawn _ }> |- _ => tactic H
  end.

Ltac inv_uacc := match_uacc inv.

Ltac inv_clear_uacc := match_uacc inv_clear.

(* ------------------------------------------------------------------------- *)
(* dec                                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma uacc_dec : forall m t ad,
  Decidable.decidable (unsafe_access ad m t).
Proof. eauto using classic_decidable. Qed.

(* ------------------------------------------------------------------------- *)
(* negation                                                                  *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_nuacc :=
  intros; try (split; intros); eauto using unsafe_access.

Lemma nuacc_unit : forall m ad,
  ~ unsafe_access ad m <{unit}>.
Proof. intros * ?. inv_uacc. Qed.

Lemma nuacc_mem : forall m ad ad' T,
  ad <> ad' ->
  ~ unsafe_access ad m <{&ad' :: &T}> ->
  ~ unsafe_access ad m (m[ad'].tm).
Proof. solve_nuacc. Qed.

Lemma nuacc_new : forall m t ad T,
  ~ unsafe_access ad m <{new T t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc. Qed.

Lemma nuacc_load : forall m t ad,
  ~ unsafe_access ad m <{*t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc. Qed.

Lemma nuacc_asg : forall m t1 t2 ad,
  ~ unsafe_access ad m <{t1 = t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc. Qed.

Lemma nuacc_fun : forall m t ad x Tx,
  ~ unsafe_access ad m <{fn x Tx t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc. Qed.

Lemma nuacc_call : forall m t1 t2 ad,
  ~ unsafe_access ad m <{call t1 t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc. Qed.

Lemma nuacc_seq : forall m t1 t2 ad,
  ~ unsafe_access ad m <{t1; t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc. Qed.

Ltac inv_nuacc :=
  match goal with
  | H: ~ unsafe_access _ ?ad <{& ?ad' :: _}>, Hneq : ?ad <> ?ad' |- _ =>
    eapply (nuacc_mem _ _ _ _ Hneq) in H
  | H: ~ unsafe_access _ ?ad <{& ?ad :: & _}> |- _ =>
    contradict H; eauto using unsafe_access
  | H: ~ unsafe_access _ _ <{new _ _ }> |- _ => eapply nuacc_new  in H
  | H: ~ unsafe_access _ _ <{* _     }> |- _ => eapply nuacc_load in H
  | H: ~ unsafe_access _ _ <{_ = _   }> |- _ => eapply nuacc_asg  in H as [? ?]
  | H: ~ unsafe_access _ _ <{fn _ _ _}> |- _ => eapply nuacc_fun  in H
  | H: ~ unsafe_access _ _ <{call _ _}> |- _ => eapply nuacc_call in H as [? ?]
  | H: ~ unsafe_access _ _ <{_ ; _   }> |- _ => eapply nuacc_seq  in H as [? ?]
  end.

(* ------------------------------------------------------------------------- *)
(* core properties                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem nuacc_immutable_reference : forall m ad v T,
  value v ->
  empty |-- v is <{{ Immut T }}> ->
  ~ unsafe_access ad m v.
Proof.
  intros * Hval ? ?. destruct Hval;
  inversion_type; inv_uacc; eauto using unsafe_access.
Qed.

Theorem uacc_soundness : forall m m' t t' ad e T,
  ad < #m ->
  empty |-- t is T ->
  ~ unsafe_access ad m t ->
  m / t ==[e]==> m' / t' ->
  m[ad].tm = m'[ad].tm.
Proof.
  intros. rename ad into ad'. inversion_clear_mstep; trivial.
  - decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; trivial. lia.
  - decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array; trivial.
    generalize dependent T.
    induction_step; intros; inversion_type; inv_nuacc; eauto.
    inversion_type. exfalso. eauto using unsafe_access.
Qed.

Lemma uacc_then_acc : forall m t ad,
  unsafe_access ad m t ->
  access m t ad.
Proof.
  intros * Huacc. induction Huacc; eauto using access.
Qed.

Lemma nacc_then_nuacc : forall m t ad,
  ~ access m t ad ->
  ~ unsafe_access m t ad.
Proof.
  intros * ? Huacc. induction Huacc; eauto using access.
Qed.

Lemma step_write_requires_uacc : forall m t t' ad v Tr T,
  empty |-- t is T ->
  t --[EF_Write ad v Tr]--> t' ->
  unsafe_access m t ad.
Proof.
  intros. generalize dependent T.
  induction_step; intros * ?; inversion_type; eauto using unsafe_access.
  inversion_type. eauto using unsafe_access.
Qed.

(* ------------------------------------------------------------------------- *)
(* helpers                                                                   *)
(* ------------------------------------------------------------------------- *)

Local Lemma subst_nuacc' : forall m t ad v x,
  ~ unsafe_access ad m v ->
  ~ unsafe_access ad m t ->
  ~ unsafe_access m ([x := v] t) ad.
Proof.
  intros. intros ?. induction t; eauto; simpl in *;
  try (destruct String.string_dec; eauto);
  inv_uacc; inv_nuacc; eauto.
Qed.

Local Corollary subst_nuacc : forall m t ad v x Tx,
  ~ unsafe_access ad m v ->
  ~ unsafe_access ad m <{fn x Tx t}> ->
  ~ unsafe_access m ([x := v] t) ad.
Proof.
  intros. inv_nuacc. eauto using subst_nuacc'.
Qed.

Lemma mem_add_uacc : forall m t ad vTr,
  ~ access m t (#m) ->
  unsafe_access ad (m +++ vTr) t ->
  unsafe_access m t ad.
Proof.
  intros * Hnacc Huacc. remember (m +++ vTr) as m'.
  induction Huacc; inversion Heqm'; subst; inversion_nacc Hnacc;
  eauto using unsafe_access.
  eapply uacc_mem; trivial.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; eauto; lia.
Qed.

Local Lemma mem_add_nuacc : forall m t ad vTr,
  ~ unsafe_access (#m) m t ->
  ~ unsafe_access ad m t ->
  ~ unsafe_access (m +++ vTr) t ad.
Proof.
  intros. intros Huacc.
  induction Huacc; eauto using unsafe_access; inv_nuacc;
  eauto using unsafe_access.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array;
  simpl in *; try inv_uacc; eauto using unsafe_access.
  assert (#m <> ad') by eauto using Nat.lt_neq, Nat.neq_sym.
  inv_nuacc. eauto.
Qed.

Lemma mem_set_uacc : forall m t ad ad' vTr,
  ~ access m t ad' ->
  unsafe_access ad m[ad' <- vTr] t ->
  unsafe_access m t ad.
Proof.
  intros * Hnacc Huacc. remember (m[ad' <- vTr]) as m'.
  induction Huacc; inversion_subst_clear Heqm'; inversion_nacc Hnacc;
  eauto using unsafe_access. simpl_array. eauto using unsafe_access.
Qed.

Local Lemma mem_set_nuacc : forall m t ad ad' v Tr,
  ~ unsafe_access ad m v ->
  ~ unsafe_access ad m t ->
  ~ unsafe_access m[ad' <- (v, Tr)] t ad.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m)
    by (intros; split; destruct n; eauto).
  assert (Hlen : forall m ad ad' v Tr,
    unsafe_access ad m[ad' <- (v, Tr)] m[ad' <- (v, Tr)][ad'].tm ->
    ad' < #m). {
    intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
    rewrite (get_set_invalid memory_default) in H; trivial. inversion H.
  }
  (* main proof *)
  intros * ? ? Huacc. remember (m[ad' <- (v, Tr)]) as m'.
  induction Huacc; inversion_subst_clear Heqm'; eauto using unsafe_access.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  destruct (Nat.eq_dec ad' ad'') as [? | Hneq]; subst;
  try (assert (ad'' < #m) by eauto using Hlen);
  simpl_array; eauto using unsafe_access.
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
  ~ unsafe_access ad m t ->
  t contains t' ->
  ~ unsafe_access m t' ad.
Proof.
  intros * ? Hcon ?. induction Hcon; subst; eauto; inv_nuacc; eauto.
Qed.

Lemma step_none_nuacc_preservation : forall m t t' ad,
  ~ unsafe_access ad m t ->
  t --[EF_None]--> t' ->
  ~ unsafe_access m t' ad.
Proof.
  intros. intros F. induction_step;
  inv_nuacc; try contradiction;
  try inversion_clear_uacc; eauto using unsafe_access.
  contradict F. eauto using subst_nuacc.
Qed.

Lemma step_alloc_nuacc_preservation : forall m t t' ad v Tr,
  ad <> #m ->
  valid_accesses m t ->
  ~ unsafe_access ad m t ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  ~ unsafe_access (m +++ (v, Tr)) t' ad.
Proof.
  intros. intros ?. induction_step;
  inversion_vac; inv_nuacc; inv_uacc;
  eauto using unsafe_access; try simpl_array;
  match goal with F : unsafe_access (_ +++ _) _ _ |- _ => contradict F end;
  eauto using mem_add_nuacc, vac_nacc_length, nacc_then_nuacc.
Qed.

Lemma step_read_nuacc_preservation : forall m t t' ad ad' T,
  forall_memory m value ->
  empty |-- t is T ->
  consistently_typed_references m t ->
  ~ unsafe_access ad m t ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  ~ unsafe_access m t' ad.
Proof.
  intros * Hval. intros. intros ?. generalize dependent T.
  induction_step; intros;
  inversion_ctr; inversion_type; inv_nuacc; try inversion_clear_uacc;
  eauto; inversion_type; destruct (Nat.eq_dec ad' ad); subst;
  eauto using unsafe_access; inversion_ctr;
  match goal with F : unsafe_access _ _[_].tm _ |- _ => contradict F end;
  eauto using nuacc_refI.
Qed.

Lemma step_write_nuacc_preservation : forall m t t' ad ad' v Tr,
  ~ unsafe_access ad m t ->
  t --[EF_Write ad' v Tr]--> t' ->
  ~ unsafe_access m[ad' <- (v, Tr)] t' ad.
Proof.
  intros. intros ?. induction_step;
  inv_nuacc; inversion_clear_uacc; eauto using unsafe_access;
  match goal with H : unsafe_access _ ?t _ |- _ => rename t into tx end;
  eapply (mem_set_nuacc _ tx _ _ v);
  eauto using step_write_contains, contains_nuacc.
Qed.

Lemma step_spawn_nuacc_preservation : forall m t t' ad block,
  ~ unsafe_access ad m t ->
  t --[EF_Spawn block]--> t' ->
  ~ unsafe_access m t' ad.
Proof.
  intros. intros ?. induction_step; try inv_nuacc; inv_uacc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* inheritance-uacc                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma step_spawn_uacc_inheritance : forall m t t' ad block,
  unsafe_access ad m t' ->
  t --[EF_Spawn block]--> t' ->
  unsafe_access m t ad.
Proof.
  intros. induction_step; inv_uacc; eauto using unsafe_access.
Qed.

