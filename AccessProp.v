From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.
From Elo Require Import Compat.

(* ------------------------------------------------------------------------- *)
(* Mem                                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma todo1 : forall m t ad v,
  ~ access (m +++ v) t (length m) ->
  access (m +++ v) t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. induction Hacc;
  inversion_not_access Hnacc; eauto using access.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst;
  do 3 (rewrite_array TM_Unit); eauto using access; try contradiction.
  auto_specialize. inversion_access.
Qed.

Lemma mem_add_nacc_length : forall m t v,
  ~ access m t (length m) ->
  ~ access (m +++ v) t (length m).
Proof.
  intros * Hnacc F. remember (length m) as ad.
  induction F; inversion Heqad; subst; inversion_not_access Hnacc.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; try lia;
  do 2 (rewrite_array TM_Unit); eauto. inversion_access.
Qed.

Lemma mem_add_nacc_lt : forall m t ad v,
  ~ access m t (length m) ->
  ~ access m t ad ->
  ~ access (m +++ v) t ad.
Proof.
  intros * Hnacc1 Hnacc2 F. induction F; inversion_not_access Hnacc2.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst;
  do 2 rewrite_term_array;
  inversion_not_access Hnacc1.
  eapply IHF; eapply not_access_iff; eauto using not_access.
Qed.

Lemma mem_add_inherits_access : forall m t ad v,
  ~ access m t (length m) ->
  access (m +++ v) t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (m +++ v) as m'.
  induction Hacc; inversion Heqm'; subst; inversion_not_access Hnacc.
  eapply access_mem; trivial.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst;
  do 2 (rewrite_array TM_Unit); eauto;
  rewrite (get_default TM_Unit) in *; eauto using access; lia.
Qed.

Lemma mem_add_preserves_access : forall m t ad v,
  access m t ad ->
  access (m +++ v) t ad.
Proof.
  intros * Hacc. induction Hacc; eauto using access.
  destruct (Nat.eq_dec ad ad'); subst; eauto using access.
  eapply access_mem; trivial.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst.
  - rewrite_array TM_Unit; trivial.
  - rewrite (get_default TM_Unit) in IHHacc; try lia. inversion_access.
  - rewrite (get_default TM_Unit) in IHHacc; try lia. inversion_access.
Qed.

Module Mem.
  Module Set_.
  End Set_.
End Mem.

(* ------------------------------------------------------------------------- *)
(* Step                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma alloc_step_nacc_v : forall m t t' v,
  valid_accesses m t ->
  t --[EF_Alloc (length m) v]--> t' ->
  ~ access m v (length m).
Proof.
  intros * Hva ?. induction_step; inversion_va; eauto using access.
  intros F. specialize (Hva (length m) F). lia.
Qed.

Lemma alloc_step_access_t'_ad : forall m t t' ad v,
  t --[EF_Alloc ad v]--> t' ->
  access m t' ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma step_spawn_inherits_access : forall m t t' ad block,
  access m t' ad ->
  t --[EF_Spawn block]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; try inversion_access; eauto using access.
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

Lemma step_read_preserves_not_access : forall m t t' ad ad',
  ~ access m t ad ->
  t --[EF_Read ad' m[ad']]--> t' ->
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

Lemma step_alloc_preserves_acc : forall m t t' ad v,
  access m t ad ->
  t --[EF_Alloc (length m) v]--> t' ->
  access (m +++ v) t' ad.
Proof.
  intros. induction_step; inversion_access;
  eauto using access, mem_add_preserves_access.
  destruct (Nat.eq_dec ad (length m)); subst; eauto using access.
  eapply access_mem; trivial. rewrite_term_array.
  eauto using mem_add_preserves_access.
Qed.

Lemma step_alloc_preserves_nacc : forall m t t' ad v,
  valid_accesses m t ->
  ad <> length m ->
  ~ access m t ad ->
  t --[EF_Alloc (length m) v]--> t' ->
  ~ access (m +++ v) t' ad.
Proof.
  intros * Hva ? Hnacc ?.
  induction_step; inversion_va; inversion_not_access Hnacc;
  intros F; inversion_access;
  try solve [unfold not in *; eauto]; try rewrite_term_array;
  match goal with F : access (_ +++ _) _ _ |- _ => contradict F end;
  eauto using mem_add_nacc_lt, va_nacc_length.
Qed.

Lemma step_alloc_inherits_acc : forall m t t' ad v,
  valid_accesses m t ->
  ad <> length m ->
  access (m +++ v) t' ad ->
  t --[EF_Alloc (length m) v]--> t' ->
  access m t ad.
Proof.
  intros. induction_step;
  inversion_va; inversion_access; eauto using access;
  try lia; try rewrite_term_array;
  eauto using mem_add_inherits_access, va_nacc_length, access.
Qed.

Lemma step_alloc_creates_acc : forall ad v m t t',
  valid_accesses m t ->
  ~ access m t ad ->
  t --[EF_Alloc (length m) v]--> t' ->
  access (m +++ v) t' ad ->
  ad = length m.
Proof.
  intros * ? Hnacc ? ?.
  induction_step; inversion_va; inversion_not_access Hnacc; inversion_access;
  eauto; try rewrite_term_array;
  match goal with F : access (_ +++ _) _ _ |- _ => contradict F end;
  eauto using mem_add_nacc_lt, va_nacc_length.
Qed.

(* corollaries *)

Corollary mstep_alloc_preserves_acc : forall m m' t t' ad ad' v,
  access m t ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  access m' t' ad.
Proof. solve_mstep_by step_alloc_preserves_acc. Qed.

Corollary mstep_alloc_preserves_nacc : forall m m' t t' ad ad' v,
  valid_accesses m t ->
  ad <> length m ->
  ~ access m t ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof. solve_mstep_by step_alloc_preserves_nacc. Qed.

Corollary mstep_alloc_inherits_acc : forall m m' t t' ad ad' v,
  valid_accesses m t ->
  ad <> ad' ->
  access m' t' ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  access m t ad.
Proof. solve_mstep_by step_alloc_inherits_acc. Qed.

Corollary mstep_alloc_creates_acc : forall m m' t t' ad ad' v,
  valid_accesses m t ->
  ~ access m t ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  access (m +++ v) t' ad ->
  ad = length m.
Proof. solve_mstep_by step_alloc_creates_acc. Qed.

(* ------------------------------------------------------------------------- *)
(* Write                                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma mem_set_preserves_acc : forall m t ad ad' v,
  ~ access m v ad ->
  access m[ad' <- v] t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (m[ad' <- v]) as m'.
  induction Hacc; try rename IHHacc into IH;
  inversion_subst_clear Heqm'; eauto using access.
  match goal with |- access _ <{ & ?ad :: _ }> _ => rename ad into ad'' end.
  destruct (Nat.eq_dec ad' ad''); subst;
  try solve [rewrite (get_set_neq TM_Unit) in IH; eauto using access];
  destruct (Nat.eq_dec ad'' ad); subst; eauto using access.
  auto_specialize. rewrite (get_set_eq TM_Unit) in IH. 1: contradiction.
  eapply not_le. intros ?. rewrite (get_default TM_Unit) in Hacc.
  - inversion_access.
  - rewrite set_preserves_length. trivial.
Qed.

Local Lemma mem_set_preserves_nacc : forall m t ad ad' v,
  ~ access m v ad ->
  ~ access m t ad ->
  ~ access m[ad' <- v] t ad.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m)
    by (intros; split; destruct n; eauto).
  assert (forall m ad ad' v,
    access m[ad' <- v] m[ad' <- v][ad'] ad ->
    ad' < length m). {
    intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
    rewrite (get_set_invalid TM_Unit) in H; trivial. inversion H.
  }

  intros * HnaccT HnaccV F. remember (m[ad' <- v]) as m'.
  induction F; inversion_subst_clear Heqm'; eauto using access.
  match goal with _ : ~ access _ <{ & ?ad :: _ }> _ |- _ => 
    destruct (Nat.eq_dec ad' ad) as [? | Hneq]; subst;
    try (assert (ad < length m) by eauto)
  end;
  do 2 rewrite_term_array; eauto using access.
Qed.

Local Lemma step_write_value_acc : forall m t t' ad ad' v,
  access m v ad ->
  t --[EF_Write ad' v]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Local Lemma step_write_value_nacc : forall m t t' ad ad' v,
  ~ access m t ad ->
  t --[EF_Write ad' v]--> t' ->
  ~ access m v ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma step_write_inherits_acc : forall m t t' ad ad' v,
  access m[ad' <- v] t' ad ->
  t --[EF_Write ad' v]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; inversion_access; eauto using access;
  destruct (access_dec m v ad);
  eauto using step_write_value_acc, mem_set_preserves_acc, access.
Qed.

Lemma step_write_preserves_nacc : forall m t t' ad ad' v,
  ~ access m t ad ->
  t --[EF_Write ad' v]--> t' ->
  ~ access m[ad' <- v] t' ad.
Proof.
  intros * Hnacc ?. induction_step; 
  inversion_not_access Hnacc; eapply not_access_iff; eauto using not_access;
  eauto using mem_set_preserves_nacc, step_write_value_nacc, not_access.
Qed.

(* corollaries *)

Corollary mstep_write_inherits_acc : forall m m' t t' ad ad' v,
  access m' t' ad ->
  m / t ==[EF_Write ad' v]==> m' / t' ->
  access m t ad.
Proof. solve_mstep_by step_write_inherits_acc. Qed.

Corollary mstep_write_preserves_nacc : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Write ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof. solve_mstep_by step_write_preserves_nacc. Qed.

