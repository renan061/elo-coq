From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Meta.

From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* safe-spawns preservation                                                  *)
(* ------------------------------------------------------------------------- *)

(* subst ------------------------------------------------------------------- *)

Lemma nomut_subst : forall x t t',
  no_mut t ->
  no_mut t' ->
  no_mut ([x := t'] t).
Proof.
  intros. induction t; eauto; simpl;
  try destruct string_eq_dec; subst; try assumption;
  inv_nomut; eauto using no_mut.
Qed.

Lemma hasvar_subst : forall x t tx,
  ~ (has_var x t) -> ([x := tx] t) = t.
Proof.
  intros * Hnhv **. induction t; simpl; trivial;
  try (destruct string_eq_dec; subst; trivial);
  solve
    [ progress (repeat match goal with H : _ -> _ = _ |- _ => rewrite H end);
      trivial; intros ?; eauto using has_var
    | exfalso; eauto using has_var
    ].
Qed.

Lemma hasvar_typing : forall Gamma x t T,
  has_var x t ->
  Gamma x = None ->
  ~ (Gamma |-- t is T).
Proof.
  intros * ? Heq Htype.
  induction_type; inv_hasvar; eauto using ctx_eqv_safe_lookup.
  - rewrite Heq in *. discriminate.
  - rewrite lookup_update_neq in IHHtype; eauto.
Qed.

Lemma ss_subst : forall Gamma x t v T Tx,
  value v ->
  empty |-- v is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  (* --- *)
  safe_spawns v ->
  safe_spawns t ->
  safe_spawns ([x := v] t).
Proof.
  intros * Hval ? ? ? Hss.
  generalize dependent Gamma. generalize dependent T. generalize dependent Tx.
  induction Hss; intros; invc_type; try (simpl; destruct string_eq_dec);
  eauto using safe_spawns, ctx_eqv_typing, MapEquivalence.update_permutation.
  eapply ss_spawn. destruct (hasvar_dec x t).
  - eapply nomut_subst; trivial.
    inv Hval; inv_type; eauto using no_mut;
    exfalso; eapply hasvar_typing; eauto;
    unfold safe; rewrite lookup_update_eq; reflexivity.
  - erewrite hasvar_subst; eauto.
Qed.

(* tstep ------------------------------------------------------------------- *)

Lemma ss_tstep_spawn_preservation : forall t t' block,
  safe_spawns t ->
  t --[EF_Spawn block]--> t' ->
  safe_spawns t'.
Proof.
  intros. induction_tstep; inv_ss; eauto using safe_spawns.
Qed.

(* mstep ------------------------------------------------------------------- *)

Lemma ss_mstep_preservation : forall m m' t t' e,
  forall_memory m safe_spawns ->
  well_typed_term t ->
  (* --- *)
  safe_spawns t ->
  m / t ==[e]==> m' / t' ->
  safe_spawns t'.
Proof.
  intros * ? [T ?] **. generalize dependent T.
  invc_mstep; induction_tstep; intros;
  inv_type; inv_ss; eauto using safe_spawns;
  inv_type; inv_ss; eauto using ss_subst.
Qed.

(* cstep ------------------------------------------------------------------- *)

Lemma ss_thread_default :
  safe_spawns thread_default.
Proof.
  eauto using safe_spawns.
Qed.

Lemma ss_spawn_block : forall t t' block,
  safe_spawns t ->
  t --[EF_Spawn block]--> t' ->
  safe_spawns block.
Proof.
  intros. induction_tstep; inv_ss; eauto using nomut_then_ss.
Qed.

Corollary ss_cstep_preservation : forall m m' ths ths' tid e,
  forall_threads ths well_typed_term ->
  (* --- *)
  forall_memory m safe_spawns ->
  forall_threads ths safe_spawns ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_threads ths' safe_spawns.
Proof.
  eauto using simple_cstep_preservation,
    ss_tstep_spawn_preservation,
    ss_mstep_preservation,
    ss_thread_default,
    ss_spawn_block.
Qed.

(* tstep mem --------------------------------------------------------------- *)

Lemma ss_tstep_alloc_mem_preservation : forall m t t' v T,
  forall_memory m safe_spawns ->
  safe_spawns t ->
  t --[EF_Alloc (#m) v T]--> t' ->
  forall_memory (m +++ (v, T)) safe_spawns.
Proof.
  intros. unfold forall_memory.
  eauto using forall_array_add, ss_tstep_alloc_value, safe_spawns.
Qed.

Lemma ss_tstep_write_mem_preservation : forall m t t' ad v T,
  forall_memory m safe_spawns ->
  safe_spawns t ->
  t --[EF_Write ad v T]--> t' ->
  forall_memory m[ad <- (v, T)] safe_spawns.
Proof.
  intros. unfold forall_memory.
  eauto using forall_array_set, ss_tstep_write_value, safe_spawns.
Qed.

(* mstep mem --------------------------------------------------------------- *)

Corollary ss_mstep_mem_preservation : forall m m' t t' e,
  forall_memory m safe_spawns ->
  safe_spawns t ->
  m / t ==[e]==> m' / t' ->
  forall_memory m' safe_spawns.
Proof.
  intros. inv_mstep;
  eauto using ss_tstep_alloc_mem_preservation, ss_tstep_write_mem_preservation.
Qed.

(* safe-spawns preservation ------------------------------------------------ *)

Theorem safe_spawns_preservation : forall m m' ths ths' tid e,
  forall_program m ths well_typed_term ->
  (* --- *)
  forall_program m ths safe_spawns ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_program m' ths' safe_spawns.
Proof.
  intros * [? ?] [? ?] **. split; inv_cstep;
  eauto using ss_cstep_preservation, ss_mstep_mem_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* misc. properties                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma nomut_block : forall t t' block,
  safe_spawns t ->
  t --[EF_Spawn block]--> t' ->
  no_mut block.
Proof.
  intros. induction_tstep; inv_ss; eauto.
Qed.

Lemma nomut_then_nuacc: forall m t ad,
  no_mut t ->
  unsafe_access ad m t ->
  False.
Proof.
  intros * Hnm Huacc. induction Hnm; inv_uacc; eauto.
Qed.

Theorem nuacc_spawn_block : forall m t t' block ad,
  safe_spawns t ->
  t --[EF_Spawn block]--> t' ->
  ~ unsafe_access ad m block.
Proof.
  eauto using nomut_block, nomut_then_nuacc.
Qed.

