From Elo Require Export Core.
From Elo Require Export Definitions.
From Elo Require Export Inversions.
From Elo Require Export Constructors.

(* ------------------------------------------------------------------------- *)
(* misc. lemmas                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma vad_tstep_write_address_length : forall m t t' ad v T,
  valid_addresses m t ->
  t --[EF_Write ad v T]--> t' ->
  ad < #m.
Proof. 
  intros. induction_tstep; inv_vad; eauto. inv_vad. assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma wtt_tstep_alloc_value : forall t t' ad v T,
  well_typed_term t ->
  t --[EF_Alloc ad v T]--> t' ->
  well_typed_term v.
Proof.
  intros. induction_tstep; intros; inv_wtt; eauto.
Qed.

Lemma wtt_tstep_write_value : forall t t' ad v T,
  well_typed_term t ->
  t --[EF_Write ad v T]--> t' ->
  well_typed_term v.
Proof.
  intros. induction_tstep; intros; inv_wtt; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ctr_tstep_alloc_value : forall m t t' ad v T,
  consistently_typed_references m t ->
  t --[EF_Alloc ad v T]--> t' ->
  consistently_typed_references m v.
Proof.
  intros. induction_tstep; inv_ctr; eauto.
Qed.

Lemma ctr_tstep_write_value : forall m t t' ad v T,
  consistently_typed_references m t ->
  t --[EF_Write ad v T]--> t' ->
  consistently_typed_references m v.
Proof.
  intros. induction_tstep; inv_ctr; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Corollary acc_dec : forall ad m t,
  Decidable.decidable (access ad m t).
Proof. eauto using classic_decidable. Qed.

Theorem acc_mem_strong : forall m t ad ad',
  access ad' m t ->
  access ad  m (m[ad'].tm) ->
  access ad  m t.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access;
  match goal with
  |- access ?ad _ <{& ?ad' :: _}> => destruct (nat_eq_dec ad ad'); subst
  end;
  eauto using access.
Qed.

Lemma nacc_tstep_write_value : forall m t t' ad ad' v T,
  ~ access ad m t ->
  t --[EF_Write ad' v T]--> t' ->
  ~ access ad m v.
Proof.
  intros. induction_tstep; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma uacc_dec : forall m t ad,
  Decidable.decidable (unsafe_access ad m t).
Proof. eauto using classic_decidable. Qed.

Theorem uacc_soundness : forall m m' t t' ad e T,
  ad < #m ->
  empty |-- t is T ->
  ~ unsafe_access ad m t ->
  m / t ==[e]==> m' / t' ->
  m[ad].tm = m'[ad].tm.
Proof.
  intros. rename ad into ad'. invc_mstep; trivial.
  - decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; eauto.
  - decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array; trivial.
    generalize dependent T. induction_tstep; intros; inv_type; inv_nuacc; eauto.
    inv_type. exfalso. eauto using unsafe_access.
Qed.

Lemma nuacc_from_immutable_type : forall m ad ad' T,
  forall_memory m value ->
  empty |-- m[ad'].tm is <{{Immut T}}> ->
  ~ unsafe_access ad m m[ad'].tm.
Proof.
  intros * Hval **. intros ?.
  specialize (Hval ad'); simpl in *.
  destruct Hval; inv_type; inv_uacc; eauto.
Qed.

Lemma uacc_then_acc : forall m t ad,
  unsafe_access ad m t ->
  access ad m t.
Proof.
  intros * Huacc. induction Huacc; eauto using access.
Qed.

Corollary sacc_then_acc : forall m t ad,
  safe_access ad m t ->
  access ad m t.
Proof.
  intros * [? _]. assumption.
Qed.

Lemma nacc_then_nuacc : forall m t ad,
  ~ access ad m t ->
  ~ unsafe_access ad m t.
Proof.
  intros * ? Huacc. induction Huacc; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nomut_then_ss : forall t,
  no_mut t ->
  safe_spawns t.
Proof.
  intros * H. induction t; induction H; eauto using safe_spawns.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma hasvar_dec : forall x t,
  Decidable.decidable (has_var x t).
Proof.
  unfold Decidable.decidable. intros. induction t;
  try progress (repeat match goal with H : _ \/ _ |- _ => destruct H end);
  try match goal with x' : id |- _ => destruct (string_eq_dec x x'); subst end;
  solve [ left; eauto using has_var
        | right; intros ?; inv_hasvar; eauto
        ].
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ss_tstep_alloc_value : forall t t' ad v T,
  safe_spawns t ->
  t --[EF_Alloc ad v T]--> t' ->
  safe_spawns v.
Proof.
  intros. induction_tstep; inv_ss; eauto.
Qed.

Lemma ss_tstep_write_value : forall t t' ad v T,
  safe_spawns t ->
  t --[EF_Write ad v T]--> t' ->
  safe_spawns v.
Proof.
  intros. induction_tstep; inv_ss; eauto.
Qed.

