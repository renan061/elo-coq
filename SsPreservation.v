
(* ------------------------------------------------------------------------- *)
(* SafeSpawns mstep term preservation                                        *)
(* ------------------------------------------------------------------------- *)

Local Lemma safe_spawns_subst : forall Gamma x t v T Tx,
  value v ->
  empty |-- v is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  SafeSpawns v ->
  SafeSpawns t ->
  SafeSpawns ([x := v] t).
Proof.
  assert (H1 : forall Gamma x T,
    (safe Gamma[x <== <{{ &T }}>]) x = None);
  assert (H2 : forall Gamma x T T',
    (safe Gamma[x <== <{{ T --> T' }}>]) x = None);
  try solve [unfold safe; intros; rewrite lookup_update_eq; reflexivity].
  (* main proof *)
  intros * Hvalue HtypeV HtypeT Hssv Hsst.
  generalize dependent Gamma. generalize dependent T. generalize dependent Tx.
  induction Hsst; intros; inversion_type;
  simpl; try (destruct string_eq_dec);
  eauto using SafeSpawns, equivalence_typing, MapEquivalence.update_permutation.
  eapply safe_spawns_spawn. destruct (hasvar_dec x t).
  - eapply nomut_subst; trivial.
    inversion Hvalue; subst; eauto using NoMut.
    + inversion HtypeV; subst; eauto using NoMut.
      exfalso. eapply hasvar_typing; eauto using H1.
    + inversion_clear Hvalue. inversion HtypeV; subst.
      exfalso. eapply hasvar_typing; eauto using H2. 
  - erewrite hasvar_subst; eauto.
Qed.

Local Lemma mstep_tm_safe_spawns_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  forall_memory m SafeSpawns ->
  SafeSpawns t ->
  m / t ==[eff]==> m' / t' ->
  SafeSpawns t'.
Proof.
  intros. generalize dependent T.
  inversion_clear_mstep; induction_step; intros;
  try solve [inversion_type; inversion_ss; eauto using SafeSpawns].
  do 2 (inversion_ss; inversion_type).
  eauto using safe_spawns_subst.
Qed.

(* ------------------------------------------------------------------------- *)
(* SafeSpawns mstep memory preservation                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma mem_safe_spawns_alloc : forall m t t' v V,
  forall_memory m SafeSpawns ->
  SafeSpawns t ->
  t --[EF_Alloc (length m) v V]--> t' ->
  forall_memory (m +++ (v, V)) SafeSpawns.
Proof.
  intros. assert (SafeSpawns v) by (induction_step; inversion_ss; eauto).
  unfold forall_memory. eauto using forall_array_add, SafeSpawns.
Qed.

Local Lemma mem_safe_spawns_store : forall m t t' ad v V,
  forall_memory m SafeSpawns ->
  SafeSpawns t ->
  t --[EF_Write ad v V]--> t' ->
  forall_memory m[ad <- (v, V)] SafeSpawns.
Proof.
  intros. assert (SafeSpawns v) by (induction_step; inversion_ss; eauto).
  unfold forall_memory. eauto using forall_array_set, SafeSpawns.
Qed.

Local Lemma mstep_mem_safe_spawns_preservation : forall m m' t t' eff,
  forall_memory m SafeSpawns ->
  SafeSpawns t ->
  m / t ==[eff]==> m' / t' ->
  forall_memory m' SafeSpawns.
Proof.
  intros. inversion_mstep;
  eauto using mem_safe_spawns_alloc, mem_safe_spawns_store.
Qed.

(* ------------------------------------------------------------------------- *)
(* SafeSpawns cstep preservation                                             *)
(* ------------------------------------------------------------------------- *)

Local Lemma nomut_then_safe_spawns : forall t,
  NoMut t ->
  SafeSpawns t.
Proof.
  intros * H. induction t; induction H; eauto using SafeSpawns.
Qed.

Local Lemma safe_spawns_for_block : forall t t' block,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  SafeSpawns block.
Proof.
  intros. induction_step; inversion_ss;
  eauto using SafeSpawns, nomut_then_safe_spawns.
Qed.

Local Lemma step_safe_spawns_preservation : forall t t' block,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  SafeSpawns t'.
Proof.
  intros. induction_step; inversion_ss;
  eauto using SafeSpawns, nomut_then_safe_spawns.
Qed.

Theorem safe_spawns_preservation : forall m m' ths ths' tid eff,
  forall_program m ths well_typed_term ->
  (* --- *)
  forall_program m ths SafeSpawns ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_program m' ths' SafeSpawns.
Proof.
  intros * [_ Htype] [? ?]. split; inversion_cstep;
  eauto using mstep_mem_safe_spawns_preservation.
  - eapply forall_array_add; eauto using SafeSpawns, safe_spawns_for_block.
    eapply forall_array_set;
    eauto using SafeSpawns, step_safe_spawns_preservation.
  - eapply forall_array_set;
    eauto using SafeSpawns. specialize (Htype tid) as [? ?].
    eauto using mstep_tm_safe_spawns_preservation. (* performance *)
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Local Lemma nomut_block : forall t t' block,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  NoMut block.
Proof.
  intros. induction_step; inversion_ss; eauto.
Qed.

Local Lemma nomut_then_nuacc: forall m t ad,
  NoMut t ->
  unsafe_access ad m t ->
  False.
Proof.
  intros * Hnm Huacc. induction Hnm; inv_uacc; eauto.
Qed.

Theorem nuacc_spawn_block : forall m t t' block ad,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  ~ unsafe_access ad m block.
Proof.
  eauto using nomut_block, nomut_then_nuacc.
Qed.

