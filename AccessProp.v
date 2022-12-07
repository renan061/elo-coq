From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.

(* ------------------------------------------------------------------------- *)
(* memory                                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma mem_add_acc : forall m t ad vTr,
  ~ access m t (#m) ->
  access (m +++ vTr) t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (m +++ vTr) as m'.
  induction Hacc; inversion Heqm'; subst; inversion_nacc Hnacc.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; try lia;
  simpl_array; eauto using access. simpl in *.
  inversion_acc.
Qed.

Lemma mem_set_acc : forall m t ad ad' v,
  ~ access m t ad' ->
  access m[ad' <- v] t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc.  remember (m[ad' <- v]) as m'.
  induction Hacc; inversion_subst_clear Heqm'; inversion_nacc Hnacc;
  simpl_array; eauto using access.
Qed.

Local Lemma mem_set_acc' : forall m t ad ad' v V,
  ~ access m v ad ->
  access m[ad' <- (v, V)] t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (m[ad' <- (v, V)]) as m'.
  induction Hacc; try rename IHHacc into IH;
  inversion_subst_clear Heqm'; eauto using access.
  match goal with |- access _ <{ & ?ad :: _ }> _ => rename ad into ad'' end.
  destruct (Nat.eq_dec ad' ad''); subst;
  try solve [simpl_array; eauto using access];
  destruct (Nat.eq_dec ad'' ad); subst; eauto using access.
  auto_specialize. rewrite (get_set_eq memory_default) in IH. 1: contradiction.
  eapply not_le. intros Hlen. simpl_array. 
  eapply Nat.lt_eq_cases in Hlen as [? | ?]; subst;
  simpl_array; simpl in *; inversion_acc.
Qed.

(* ------------------------------------------------------------------------- *)
(* inheritance                                                               *)
(* ------------------------------------------------------------------------- *)

Lemma step_none_inherits_access : forall m t t' ad,
  access m t' ad ->
  t --[EF_None]--> t' ->
  access m t ad.
Proof.
  intros. induction_step;
  try inversion_acc; eauto using access, subst_acc.
Qed.

Lemma step_alloc_inherits_acc : forall m t t' ad v Tr,
  valid_accesses m t ->
  ad <> #m ->
  access (m +++ (v, Tr)) t' ad ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  access m t ad.
Proof.
  intros. induction_step;
  inversion_vac; inversion_acc; eauto using access;
  try lia; try simpl_array;
  eauto using mem_add_acc, vac_nacc_length, access.
Qed.

Lemma step_read_inherits_acc : forall m t t' ad ad',
  access m t' ad ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  access m t ad.
Proof.
  intros * ? ?. induction_step;
  try inversion_acc; eauto using access.
  destruct (Nat.eq_dec ad' ad); subst; eauto using access.
Qed.

Lemma step_write_inherits_acc : forall m t t' ad ad' v Tr,
  access m[ad' <- (v, Tr)] t' ad ->
  t --[EF_Write ad' v Tr]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; inversion_acc; eauto using access;
  destruct (acc_dec m v ad);
  eauto using mem_set_acc', access;
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

