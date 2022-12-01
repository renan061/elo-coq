From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.

(* ------------------------------------------------------------------------- *)
(* mem -- add                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma mem_add_acc : forall m t ad v,
  ~ access m t (length m) ->
  access (m +++ v) t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (m +++ v) as m'.
  induction Hacc; inversion Heqm'; subst; inversion_not_access Hnacc.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; try lia;
  do 2 simpl_array; eauto using access. simpl_array. simpl in *.
  inversion_access.
Qed.

(* ------------------------------------------------------------------------- *)
(* mem -- set                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma mem_set_acc : forall m t ad ad' v,
  ~ access m t ad' ->
  access m[ad' <- v] t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc.  remember (m[ad' <- v]) as m'.
  induction Hacc; inversion_subst_clear Heqm'; inversion_not_access Hnacc;
  try (do 2 simpl_array); eauto using access.
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
  try solve [do 2 simpl_array; eauto using access];
  destruct (Nat.eq_dec ad'' ad); subst; eauto using access.
  auto_specialize. rewrite (get_set_eq memory_default) in IH. 1: contradiction.
  eapply not_le. intros Hlen. do 3 simpl_array. 
  eapply Nat.lt_eq_cases in Hlen as [? | ?]; subst;
  do 2 simpl_array; simpl in *; inversion_access.
Qed.

(* ------------------------------------------------------------------------- *)
(* step-inherits-acc                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma step_write_inherits_acc : forall m t t' ad ad' v V,
  access m[ad' <- (v, V)] t' ad ->
  t --[EF_Write ad' v V]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; inversion_access; eauto using access;
  destruct (access_dec m v ad);
  eauto using mem_set_acc', access;
  assert (forall t t', t --[EF_Write ad' v V]--> t' -> access m t ad)
    by (intros; induction_step; eauto using access);
  eauto using access.
Qed.

Lemma step_spawn_inherits_acc : forall m t t' block ad,
  access m t' ad ->
  t --[EF_Spawn block]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; inversion_access; eauto using access.
Qed.














(* ------------------------------------------------------------------------- *)
(* Mem -- Add                                                                *)
(* ------------------------------------------------------------------------- *)

Local Lemma todo1 : forall m t ad v,
  ~ access (m +++ v) t (length m) ->
  access (m +++ v) t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. induction Hacc;
  inversion_not_access Hnacc; eauto using access.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst;
  do 3 simpl_array; eauto using access; try contradiction.
  auto_specialize. simpl in *. inversion_access.
Qed.

Lemma mem_add_nacc_length : forall m t v,
  ~ access m t (length m) ->
  ~ access (m +++ v) t (length m).
Proof.
  intros * Hnacc F. remember (length m) as ad.
  induction F; inversion Heqad; subst; inversion_not_access Hnacc.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; try lia;
  do 2 simpl_array; eauto.
  simpl_array. eauto.
Qed.

Lemma mem_add_nacc_lt : forall m t ad v,
  ~ access m t (length m) ->
  ~ access m t ad ->
  ~ access (m +++ v) t ad.
Proof.
  intros * Hnacc1 Hnacc2 F. induction F; inversion_not_access Hnacc2.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst;
  do 2 simpl_array;
  inversion_not_access Hnacc1.
  eapply IHF; eapply not_access_iff; eauto using not_access.
Qed.

Lemma mem_add_preserves_access : forall m t ad v,
  access m t ad ->
  access (m +++ v) t ad.
Proof.
  intros * Hacc. induction Hacc; eauto using access.
  destruct (Nat.eq_dec ad ad'); subst; eauto using access.
  eapply access_mem; trivial.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst;
  simpl_array; trivial; do 2 simpl_array; simpl in *; inversion_access.
Qed.

(* ------------------------------------------------------------------------- *)
(* Mem -- Set                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma mem_set_preserves_acc1 : forall m t ad ad' v,
  ~ access m t ad' ->
  access m t ad ->
  access m[ad' <- v] t ad.
Proof.
  intros * Hnacc Hacc. induction Hacc; inversion_not_access Hnacc.
  match goal with H : ~ access _ _ ?ad' |- _ => 
    destruct (Nat.eq_dec ad ad'); subst
  end.
  - contradiction.
  - eapply access_mem; trivial. simpl_array. eauto.
Qed.

Lemma mem_set_preserves_acc2 : forall m t ad ad' v,
  ~ access m m[ad'].tm ad ->
  access m t ad ->
  access m[ad' <- v] t ad.
Proof.
  intros * ? Hacc.
  destruct (access_dec m t ad'); eauto using mem_set_preserves_acc1.
  induction Hacc; inversion_access; eauto using mem_set_preserves_acc1, access;
  solve
    [ eapply access_mem; trivial; simpl_array; eauto
    | destruct (access_dec m t1 ad'); eauto using mem_set_preserves_acc1, access
    | destruct (access_dec m t2 ad'); eauto using mem_set_preserves_acc1, access
    ].
Qed.

Lemma mem_set_preserves_nacc2 : forall m t ad ad' v,
  ~ access m t ad' ->
  ~ access m t ad ->
  ~ access m[ad' <- v] t ad.
Proof.
  intros * Hnacc' Hnacc F. remember (m[ad' <- v]) as m'.
  induction F; inversion_not_access Hnacc'; inversion_not_access Hnacc.
  do 2 simpl_array. eauto.
Qed.

Lemma mem_set_preserves_nacc : forall m t ad ad' v V,
  ~ access m v ad ->
  ~ access m t ad ->
  ~ access m[ad' <- (v, V)] t ad.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m)
    by (intros; split; destruct n; eauto).
  assert (forall m ad ad' v,
    access m[ad' <- v] m[ad' <- v][ad'].tm ad ->
    ad' < length m). {
    intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
    rewrite (get_set_invalid memory_default) in H; trivial. inversion H.
  }

  intros * HnaccT HnaccV F. remember (m[ad' <- (v, V)]) as m'.
  induction F; inversion_subst_clear Heqm'; eauto using access.
  match goal with _ : ~ access _ <{ & ?ad :: _ }> _ |- _ => 
    destruct (Nat.eq_dec ad' ad) as [? | Hneq]; subst;
    try (assert (ad < length m) by eauto)
  end;
  do 2 simpl_array; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* Step                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma alloc_step_nacc_v : forall m t t' v V,
  valid_accesses m t ->
  t --[EF_Alloc (length m) v V]--> t' ->
  ~ access m v (length m).
Proof.
  intros * Hva ?. induction_step; inversion_va; eauto using access.
  intros F. specialize (Hva (length m) F). lia.
Qed.

Lemma alloc_step_access_t'_ad : forall m t t' ad v V,
  t --[EF_Alloc ad v V]--> t' ->
  access m t' ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma step_spawn_preserves_not_access : forall m t t' ad block,
  ~ access m t ad ->
  t --[EF_Spawn block]--> t' ->
  ~ access m t' ad.
Proof.
  intros * Hnacc ?. induction_step;
  eapply not_access_iff; eapply not_access_iff in Hnacc;
  inversion_clear Hnacc; eauto using not_access.
Qed.

(* ------------------------------------------------------------------------- *)
(* Step -- None                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma step_none_inherits_access : forall m t t' ad,
  access m t' ad ->
  t --[EF_None]--> t' ->
  access m t ad.
Proof.
  intros. induction_step;
  try inversion_access; eauto using access, access_subst.
Qed.

Lemma step_none_preserves_not_access : forall m t t' ad,
  ~ access m t ad ->
  t --[EF_None]--> t' ->
  ~ access m t' ad.
Proof.
  intros * Hnacc ?.
  induction_step; inversion_not_access Hnacc;
  eapply not_access_iff; eauto using not_access.
  eapply not_access_iff. eauto using not_access_subst_fun.
Qed.

(* ------------------------------------------------------------------------- *)
(* MStep -- None                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma mstep_none_inherits_access : forall m m' t t' ad,
  access m' t' ad ->
  m / t ==[EF_None]==> m' / t' ->
  access m t ad.
Proof.
  intros. inversion_mstep. induction_step;
  try inversion_access; eauto using access, access_subst.
Qed.

Lemma mstep_none_preserves_not_access : forall m m' t t' ad,
  ~ access m t ad ->
  m / t ==[EF_None]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc ?. inversion_mstep.
  induction_step; inversion_not_access Hnacc;
  eapply not_access_iff; eauto using not_access.
  eapply not_access_iff. eauto using not_access_subst_fun.
Qed.


(* ------------------------------------------------------------------------- *)
(* Read                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma step_read_inherits_acc : forall m t t' ad ad',
  access m t' ad ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  access m t ad.
Proof.
  intros * ? ?. induction_step;
  try inversion_access; eauto using access.
  destruct (Nat.eq_dec ad' ad); subst; eauto using access.
Qed.

Lemma step_read_preserves_not_access : forall m t t' ad ad',
  ~ access m t ad ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  ~ access m t' ad.
Proof.
  intros * Hnacc ?. induction_step; inversion_not_access Hnacc;
  solve
    [ eapply not_access_iff; eauto using not_access
    | match goal with | H : ~ access _ _ _ |- _ => inversion_not_access H end
    ].
Qed.

(* ------------------------------------------------------------------------- *)
(* MStep -- Read                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma mstep_read_address_access: forall m m' t t' ad v,
  m / t ==[EF_Read ad v]==> m' / t' ->
  access m t ad.
Proof.
  intros. inversion_mstep. induction_step; eauto using access.
Qed.

Lemma mstep_read_inherits_access : forall m m' t t' ad ad' v,
  access m' t' ad ->
  m / t ==[EF_Read ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros * ? ?. inversion_mstep. induction_step;
  try inversion_access; eauto using access.
  destruct (Nat.eq_dec ad' ad); subst; eauto using access.
Qed.

Lemma mstep_read_preserves_access : forall m m' t t' ad ad' v,
  ad <> ad' ->
  access m t ad ->
  m / t ==[EF_Read ad' v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros * Hneq Hacc Hmstep. inversion_mstep. induction_step;
  inversion_access; eauto using access.
  inversion_access; subst; trivial. exfalso. eauto.
Qed.

Corollary mstep_read_preserves_not_access : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Read ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros. inversion_mstep. eauto using step_read_preserves_not_access.
Qed.

(* ------------------------------------------------------------------------- *)
(* Auxiliary                                                                 *)
(* ------------------------------------------------------------------------- *)

Ltac solve_mstep_by H :=
  intros; inversion_mstep; eauto using H.

(* ------------------------------------------------------------------------- *)
(* Alloc                                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma step_alloc_preserves_acc : forall m t t' ad v V,
  access m t ad ->
  t --[EF_Alloc (length m) v V]--> t' ->
  access (m +++ (v, V)) t' ad.
Proof.
  intros. induction_step; inversion_access;
  eauto using access, mem_add_preserves_access.
  destruct (Nat.eq_dec ad (length m)); subst; eauto using access.
  eapply access_mem; trivial. simpl_array.
  eauto using mem_add_preserves_access.
Qed.

Lemma step_alloc_preserves_nacc : forall m t t' ad v V,
  valid_accesses m t ->
  ad <> length m ->
  ~ access m t ad ->
  t --[EF_Alloc (length m) v V]--> t' ->
  ~ access (m +++ (v, V)) t' ad.
Proof.
  intros * Hva ? Hnacc ?.
  induction_step; inversion_va; inversion_not_access Hnacc;
  intros F; inversion_access;
  try solve [unfold not in *; eauto]; try simpl_array;
  match goal with F : access (_ +++ _) _ _ |- _ => contradict F end;
  eauto using mem_add_nacc_lt, va_nacc_length.
Qed.

Lemma step_alloc_inherits_acc : forall m t t' ad v V,
  valid_accesses m t ->
  ad <> length m ->
  access (m +++ (v, V)) t' ad ->
  t --[EF_Alloc (length m) v V]--> t' ->
  access m t ad.
Proof.
  intros. induction_step;
  inversion_va; inversion_access; eauto using access;
  try lia; try simpl_array;
  eauto using mem_add_acc, va_nacc_length, access.
Qed.

Lemma step_alloc_creates_acc : forall ad v m t t' V,
  valid_accesses m t ->
  ~ access m t ad ->
  t --[EF_Alloc (length m) v V]--> t' ->
  access (m +++ (v, V)) t' ad ->
  ad = length m.
Proof.
  intros * ? Hnacc ? ?.
  induction_step; inversion_va; inversion_not_access Hnacc; inversion_access;
  eauto; try simpl_array;
  match goal with F : access (_ +++ _) _ _ |- _ => contradict F end;
  eauto using mem_add_nacc_lt, va_nacc_length.
Qed.

Local Lemma step_write_value_nacc : forall m t t' ad ad' v V,
  ~ access m t ad ->
  t --[EF_Write ad' v V]--> t' ->
  ~ access m v ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma step_write_requires_acc : forall m t t' ad v V,
  t --[EF_Write ad v V]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma step_write_preserves_nacc : forall m t t' ad ad' v V,
  ~ access m t ad ->
  t --[EF_Write ad' v V]--> t' ->
  ~ access m[ad' <- (v, V)] t' ad.
Proof.
  intros * Hnacc ?. induction_step; 
  inversion_not_access Hnacc; eapply not_access_iff; eauto using not_access;
  eauto using mem_set_preserves_nacc, step_write_value_nacc, not_access.
Qed.

