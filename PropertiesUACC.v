From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

From Elo Require Import PropertiesACC.

(* ------------------------------------------------------------------------- *)
(* misc. properties                                                          *)
(* ------------------------------------------------------------------------- *)

Corollary nuacc_vad_length : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ unsafe_access (#m) m t.
Proof.
  eauto using nacc_then_nuacc, nacc_vad_length.
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

(* ------------------------------------------------------------------------- *)
(* not-unsafe-access preservation                                            *)
(* ------------------------------------------------------------------------- *)

(* subst & mem ------------------------------------------------------------- *)

Lemma nuacc_subst_preservation : forall m t tx ad x,
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m tx ->
  ~ unsafe_access ad m ([x := tx] t).
Proof.
  intros ** ?. induction t; eauto; simpl in *;
  try (destruct string_eq_dec); eauto; inv_uacc; inv_nuacc; eauto.
Qed.

Lemma nuacc_mem_add_preservation  : forall m t ad vT,
  ~ unsafe_access (#m) m t ->
  (* --- *)
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad (m +++ vT) t.
Proof.
  intros ** Huacc. induction Huacc; inv_nuacc; eauto using unsafe_access.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array;
  simpl in *; eauto using unsafe_access; inv_nuacc; eauto. inv_uacc.
Qed.

Lemma nuacc_mem_set_preservation : forall m t ad ad' v T,
  ~ unsafe_access ad m v ->
  (* --- *)
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m[ad' <- (v, T)] t.
Proof.
  assert (H : forall m m' ad ad', unsafe_access ad m m'[ad'].tm -> ad' < #m'). {
    intros * H. decompose sum (lt_eq_lt_dec ad' (#m')); subst; trivial;
    simpl_array; simpl in *; inv_uacc.
  }
  (* main proof *)
  intros ** Huacc. induction Huacc; eauto using unsafe_access.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  eapply H in Huacc. rewrite set_preserves_length in Huacc.
  destruct (nat_eq_dec ad' ad''); subst; simpl_array; eauto using unsafe_access.
Qed.

Lemma alt_nuacc_mem_set_preservation : forall m t ad ad' vT,
  ~ unsafe_access ad' m t ->
  (* --- *)
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m[ad' <- vT] t.
Proof.
  intros ** Huacc. induction Huacc; inv_nuacc; inv_nuacc; eauto.
  match goal with _ : _ <> ?ad |- _ => destruct (nat_eq_dec ad' ad); subst end;
  simpl_array; eauto.
Qed.

(* tstep ------------------------------------------------------------------- *)

Lemma nuacc_tstep_none_preservation : forall m t t' ad,
  ~ unsafe_access ad m t ->
  t --[EF_None]--> t' ->
  ~ unsafe_access ad m t'.
Proof.
  intros ** Huacc. induction_tstep; inv_nuacc;
  try inv_uacc; eauto. inv_nuacc.
  contradict Huacc. eauto using nuacc_subst_preservation.
Qed.

Lemma nuacc_tstep_alloc_preservation : forall m t t' ad v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  ad < #m ->
  ~ unsafe_access ad m t ->
  t --[EF_Alloc (#m) v T]--> t' ->
  ~ unsafe_access ad (m +++ (v, T)) t'.
Proof.
  intros ** ?. induction_tstep; inv_vad; inv_nuacc; invc_uacc; eauto;
  match goal with F : unsafe_access _ (_ +++ _) _ |- _ => contradict F end;
  try simpl_array;
  eauto using nacc_vad_length, nacc_then_nuacc, nuacc_mem_add_preservation.
Qed.

Lemma nuacc_tstep_read_preservation : forall m t t' ad ad',
  forall_memory m value ->
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  ~ unsafe_access ad m t ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  ~ unsafe_access ad m t'.
Proof.
  intros ** ?. induction_tstep; intros;
  inv_wtt; inv_ctr; inv_nuacc; try invc_uacc; eauto;
  inv_wtt; destruct (nat_eq_dec ad' ad); subst; eauto using unsafe_access;
  inv_ctr;
  match goal with F : unsafe_access _ _ _[_].tm |- _ => contradict F end;
  eauto using nuacc_from_immutable_type.
Qed.

Lemma nuacc_tstep_write_preservation : forall m t t' ad ad' v T,
  ~ unsafe_access ad m t ->
  t --[EF_Write ad' v T]--> t' ->
  ~ unsafe_access ad m[ad' <- (v, T)] t'.
Proof.
  assert (forall m t t' ad ad' v T,
    ~ unsafe_access ad m t ->
    t --[EF_Write ad' v T]--> t' ->
    ~ unsafe_access ad m v)
    by (intros; induction_tstep; eauto using unsafe_access).
  (* main proof *)
  intros ** ?. induction_tstep; inv_nuacc; invc_uacc; eauto;
  match goal with _ : unsafe_access _ _ ?t |- _ => rename t into tx end;
  eapply (nuacc_mem_set_preservation _ tx _ _ v); eauto.
Qed.

Lemma nuacc_tstep_spawn_preservation : forall m t t' ad block,
  ~ unsafe_access ad m t ->
  t --[EF_Spawn block]--> t' ->
  ~ unsafe_access ad m t'.
Proof.
  intros ** ?. induction_tstep; inv_uacc; eauto; inv_nuacc; eauto.
Qed.

(* mstep ------------------------------------------------------------------- *)

Corollary nuacc_mstep_preservation : forall m m' t t' e ad,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  ad < #m ->
  ~ unsafe_access ad m t ->
  m / t ==[e]==> m' / t' ->
  ~ unsafe_access ad m' t'.
Proof.
  intros. inv_mstep;
  eauto using nuacc_tstep_none_preservation,
              nuacc_tstep_alloc_preservation,
              nuacc_tstep_read_preservation,
              nuacc_tstep_write_preservation.
Qed.

(* cstep ------------------------------------------------------------------- *)

(* TODO *)
Local Lemma uacc_tstep_write_requirement : forall m t t' ad v T,
  well_typed_term t ->
  t --[EF_Write ad v T]--> t' ->
  unsafe_access ad m t.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  induction_tstep; intros; inv_type; eauto using unsafe_access.
  inv_type. eauto using unsafe_access.
Qed.

(* TODO *)
Lemma nuacc_untouched_threads_preservation : forall m m' ths tid tid' t' ad e,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths well_typed_term ->
  safe_memory_sharing m ths ->
  (* --- *)
  tid <> tid' ->
  tid' < #ths ->
  ~ unsafe_access ad m ths[tid'] ->
  m / ths[tid] ==[e]==> m' / t' ->
  ~ unsafe_access ad m' ths[tid'].
Proof.
  intros * ? ? ? Hsms **. rename ad into ad'. invc_mstep;
  eauto using nuacc_mem_add_preservation, nuacc_vad_length.
  eapply alt_nuacc_mem_set_preservation; eauto.
  assert (unsafe_access ad m ths[tid])
    by eauto using uacc_tstep_write_requirement.
  intros ?. eapply (Hsms tid tid'); eauto using uacc_then_acc.
Qed.

Corollary nuacc_cstep_preservation : forall m m' ths ths' tid tid' ad e,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  safe_memory_sharing m ths ->
  (* --- *)
  ad < #m ->
  tid < #ths ->
  ~ unsafe_access ad m ths[tid] ->
  m / ths ~~[tid', e]~~> m' / ths' ->
  ~ unsafe_access ad m' ths'[tid].
Proof.
  intros. invc_cstep; destruct (nat_eq_dec tid tid'); subst; simpl_array;
  eauto using nuacc_tstep_spawn_preservation,
              nuacc_mstep_preservation,
              nuacc_untouched_threads_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* misc. properties                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma memtyp_mstep_nuacc_then_immut : forall m m' t t' e,
  well_typed_term t ->
  (* --- *)
  m / t ==[e]==> m' / t' ->
  #m' > #m ->
  ~ unsafe_access (#m) m' t' ->
  exists Tm, m'[#m].typ = <{{i&Tm}}>.
Proof.
  intros * [T' ?] ? Hlen **. intros. invc_mstep;
  try rewrite set_preserves_length in Hlen; eauto.
  simpl_array. simpl. generalize dependent T'.
  induction_tstep; intros; inv_type; try inv_nuacc; eauto;
  try match goal with
  | _ : ?t --[_]--> _ , H : _ |-- ?t is _ |- _ =>
    specialize (IHtstep _ H) as [? ?]; eauto
  end.
Qed.

Lemma memtyp_mstep_uacc_then_mut : forall m m' t t' e,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  well_typed_term t ->
  (* --- *)
  m / t ==[e]==> m' / t' ->
  #m' > #m ->
  unsafe_access (#m) m' t' ->
  exists T, m'[#m].typ = <{{&T}}>.
Proof.
  intros * ? ? [T' ?] ? Hlen **. invc_mstep;
  try rewrite set_preserves_length in Hlen; eauto.
  simpl_array. simpl. generalize dependent T'.
  induction_tstep; intros; inv_vad; inv_type; try invc_uacc; eauto; exfalso;
  match goal with
  | _ : unsafe_access _ _ ?t |- _ =>
    assert (~ access (#m) m t) by eauto using nacc_vad_length
  end;
  eauto using uacc_then_acc, uacc_mem_add_inheritance.
Qed.

(* If there is access: *)
(* The access is unsafe if and only if the memtyp is mutable. *)
Lemma uacc_iff_memtyp_mut : forall m t ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  access ad m t ->
  (* --- *)
  unsafe_access ad m t <-> (exists T, m[ad].typ = <{{&T}}>).
Proof.
  intros * ? ? ? Hacc. split.
  - intros Huacc. clear Hacc. induction Huacc; inv_ctr; eauto.
  - intros [? Heq]. induction Hacc; inv_ctr; eauto using unsafe_access.
    + exfalso. eauto using nuacc_from_immutable_type.
    + rewrite Heq in *. discriminate.
Qed.

(* If one access is unsafe, then all accesses are unsafe. *)
Corollary uacc_from_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  consistently_typed_references m t' ->
  (* --- *)
  access ad m t ->
  unsafe_access ad m t' ->
  unsafe_access ad m t.
Proof.
  intros.
  eapply uacc_iff_memtyp_mut; eauto.
  eapply uacc_iff_memtyp_mut; eauto using uacc_then_acc.
Qed.

(* If there is access: *)
(* The access is not unsafe if and only if the memtyp is immutable. *)
Lemma nuacc_iff_memtyp_immut : forall m t ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  access ad m t ->
  (* --- *)
  ~ unsafe_access ad m t <-> (exists T, m[ad].typ = <{{i&T}}>).
Proof.
  intros * Hval ? ? Hacc. split.
  - intros ?. induction Hacc; invc_ctr; eauto; try inv_nuacc; eauto.
    eapply IHHacc; eauto. intros ?. destruct (Hval ad'); inv_type; inv_uacc.
  - intros [? Heq]. induction Hacc; intros ?; invc_ctr; inv_uacc; eauto;
    try (eapply IHHacc; eauto using uacc_from_association).
    rewrite Heq in *. discriminate.
Qed.

(* If one access is not unsafe, then all accesses are not unsafe. *)
Corollary nuacc_from_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  consistently_typed_references m t' ->
  (* --- *)
  access ad m t ->
  access ad m t' ->
  ~ unsafe_access ad m t' ->
  ~ unsafe_access ad m t.
Proof.
  intros.
  eapply nuacc_iff_memtyp_immut; eauto.
  eapply nuacc_iff_memtyp_immut; eauto.
Qed.

