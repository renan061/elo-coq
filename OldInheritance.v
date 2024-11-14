
From Elo Require Import Core.
From Elo Require Import Properties.
From Elo Require Import Lemmas.

(* ------------------------------------------------------------------------- *)
(* access inheritance                                                        *)
(* ------------------------------------------------------------------------- *)

(* mem & subst ------------------------------------------------------------- *)

Local Lemma acc_subst_inheritance : forall m x Tx t t' ad,
  access ad m ([x := t'] t) ->
  access ad m <{call <{fn x Tx t}> t'}>.
Proof.
  intros. induction t; eauto using access; simpl in *;
  try (destruct string_eq_dec; eauto using access);
  invc_acc; auto_specialize; do 2 (invc_acc; eauto using access).
Qed.

Lemma acc_mem_add_inheritance : forall m t ad vT,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  access ad (m +++ vT) t ->
  access ad m t.
Proof.
  intros * Hmvad Hvad Hacc.
  assert (Hnacc : ~ access (#m) m t) by eauto using nacc_vad_length.
  clear Hvad. induction Hacc; inv_nacc; eauto using access.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; eauto;
  simpl_array; eauto using access. simpl in *. inv_acc.
Qed.

Lemma acc_mem_set_inheritance : forall m t ad ad' v T,
  ~ access ad m v ->
  (* --- *)
  access ad m[ad' <- (v, T)] t ->
  access ad m t.
Proof.
  intros * Hnacc Hacc. remember (m[ad' <- (v, T)]) as m'.
  induction Hacc; inv Heqm'; eauto using access.
  match goal with |- access _ _ <{& ?ad :: _}> => rename ad into ad'' end.
  destruct (nat_eq_dec ad' ad''); subst; try (simpl_array; eauto using access);
  destruct (nat_eq_dec ad'' ad); subst; eauto using access;
  rewrite (get_set_eq memory_default) in IHHacc. 1: contradiction.
  decompose sum (lt_eq_lt_dec ad'' (#m)); subst; trivial;
  simpl_array; simpl in *; inv_acc.
Qed.

Lemma alt_acc_mem_set_inheritance : forall m t ad ad' vT,
  ~ access ad' m t ->
  (* --- *)
  access ad m[ad' <- vT] t ->
  access ad m t.
Proof.
  intros * ? Hacc. induction Hacc; inv_nacc; eauto using access.
  simpl_array. eauto using access.
Qed.

(* tstep ------------------------------------------------------------------- *)

Lemma acc_tstep_none_inheritance  : forall m t t' ad,
  access ad m t' ->
  t --[EF_None]--> t' ->
  access ad m t.
Proof.
  intros.
  induction_tstep; try inv_acc; eauto using access, acc_subst_inheritance.
Qed.

Lemma acc_tstep_alloc_inheritance : forall m t t' ad v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  ad < #m ->
  access ad (m +++ (v, T)) t' ->
  t --[EF_Alloc (#m) v T]--> t' ->
  access ad m t.
Proof.
  intros. induction_tstep; inv_vad; inv_acc;
  eauto using access, acc_mem_add_inheritance.
  simpl_array. eauto using access, acc_mem_add_inheritance.
Qed.

Lemma acc_tstep_read_inheritance : forall m t t' ad ad',
  access ad m t' ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  access ad m t.
Proof.
  intros. induction_tstep; try inv_acc; eauto using access.
  destruct (nat_eq_dec ad' ad); subst; eauto using access.
Qed.

Lemma acc_tstep_write_inheritance : forall m t t' ad ad' v T,
  access ad m[ad' <- (v, T)] t' ->
  t --[EF_Write ad' v T]--> t' ->
  access ad m t.
Proof.
  intros. induction_tstep; inv_acc; eauto using access;
  destruct (acc_dec ad m v); eauto using access, acc_mem_set_inheritance;
  assert (forall t t', t --[EF_Write ad' v T]--> t' -> access ad m t)
    by (intros; induction_tstep; eauto using access);
  eauto using access.
Qed.

Lemma acc_tstep_spawn_inheritance : forall m t t' block ad,
  access ad m t' ->
  t --[EF_Spawn block]--> t' ->
  access ad m t.
Proof.
  intros. induction_tstep; inv_acc; eauto using access.
Qed.

(* mstep ------------------------------------------------------------------- *)

Corollary acc_mstep_inheritance : forall m m' t t' ad e,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  ad < #m ->
  access ad m' t' ->
  m / t ==[e]==> m' / t' ->
  access ad m t.
Proof.
  intros. inv_mstep;
  eauto using acc_tstep_none_inheritance,
              acc_tstep_alloc_inheritance,
              acc_tstep_read_inheritance,
              acc_tstep_write_inheritance.
Qed.

(* ------------------------------------------------------------------------- *)
(* unsafe-access inheritance                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma uacc_mem_add_inheritance : forall m t ad vT,
  ~ access (#m) m t ->
  (* --- *)
  unsafe_access ad (m +++ vT) t ->
  unsafe_access ad m t.
Proof.
  intros * ? Huacc.
  induction Huacc; inv_nacc; eauto using unsafe_access.
  eapply uacc_mem; trivial.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; eauto.
Qed.

Lemma uacc_mem_set_inheritance : forall m t ad ad' vT,
  ~ access ad' m t ->
  (* --- *)
  unsafe_access ad m[ad' <- vT] t ->
  unsafe_access ad m t.
Proof.
  intros * ? Huacc.
  induction Huacc; inv_nacc; eauto using unsafe_access.
  simpl_array. eauto using unsafe_access.
Qed.

Lemma uacc_tstep_spawn_inheritance : forall m t t' block ad,
  unsafe_access ad m t' ->
  t --[EF_Spawn block]--> t' ->
  unsafe_access ad m t.
Proof.
  intros. induction_tstep; inv_uacc; eauto using unsafe_access.
Qed.
