From Elo Require Import Core.
From Elo Require Import Properties.

From Elo Require Import SimpleLemmas.

(* simpl forall-threads *)
Ltac simplfths := 
  match goal with
  | |- forall_threads _[_ <- _] _          => intros tid'; Array.sgs
  | |- forall_threads (_[_ <- _] +++ _) _  => intros tid'; Array.sgas
  end.

Ltac destruct_forall_program :=
  progress (repeat (
    match goal with H : forall_program _ _ _ |- _ => destruct H end
  )).

Ltac split_preservation := 
  intros;
  match goal with
  (* vad | ctr | ss *)
  | H : forall_program ?m1 ?ths1 (?P ?m1),
    _ : ?m1 / ?ths1 ~~[_, _]~~> ?m2 / ?ths2
     |- forall_program ?m2 ?ths2 (?P ?m2) =>
    destruct_forall_program;
    invc_cstep; try invc_mstep; trivial; split; try simplfths; trivial
  (* ss *)
  | H : forall_program ?m1 ?ths1 ?P,
    _ : ?m1 / ?ths1 ~~[_, _]~~> ?m2 / ?ths2
     |- forall_program ?m2 ?ths2 ?P =>
    destruct_forall_program;
    invc_cstep; try invc_mstep; split; try simplfths; trivial
  (* nacc | nuacc *)
  | _ : ?ad  < #?m1,
    _ : ?tid < #?ths1,
    H : ~ ?P ?ad ?m1 ?ths1[?tid],
    _ : ?m1 / ?ths1 ~~[?tid', _]~~> ?m2 / ?ths2
     |- ~ ?P ?ad ?m2 ?ths2[?tid]  =>
    invc_cstep; try invc_mstep; try simpl_array; Array.sgs; trivial
  (* sms *)
  | _ : ?P ?m1 ?ths1,
    _ : ?m1 / ?ths1 ~~[_, _]~~> ?m2 / ?ths2
     |- ?P ?m2 ?ths2 =>
    invc_cstep; try invc_mstep
  end.

(* ------------------------------------------------------------------------- *)
(* value                                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem value_preservation : forall m m' ths ths' tid e,
  forall_memory m value ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_memory m' value.
Proof.
  assert (forall t t' ad te T, t --[e_alloc ad te T]--> t' -> value te)
    by (intros; ind_tstep; eauto using value). 
  assert (forall t t' ad te T, t --[e_write ad te T]--> t' -> value te)
    by (intros; ind_tstep; eauto). 
  intros. inv_cstep; trivial. inv_mstep; trivial;
  (eapply forall_array_add || eapply forall_array_set); eauto using value.
Qed.

(* ------------------------------------------------------------------------- *)
(* safe-spawns                                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma hasvar_subst : forall x t tx,
  ~ (has_var x t) ->
  ([x := tx] t) = t.
Proof.
  intros * Hnhv **. induction t; simpl; trivial;
  try (destruct string_eq_dec; subst; trivial);
  solve
    [ progress (repeat match goal with H : _ -> _ = _ |- _ => rewrite H end);
      trivial; intros ?; eauto using has_var
    | exfalso; eauto using has_var
    ].
Qed.

Local Lemma hasvar_typing : forall Gamma x t T,
  has_var x t ->
  Gamma x = None ->
  ~ (Gamma |-- t is T).
Proof.
  intros * ? Heq Htype.
  induction_type; inv_hasvar; eauto using ctx_eqv_safe_lookup.
  - rewrite Heq in *. discriminate.
  - rewrite lookup_update_neq in IHHtype; eauto.
Qed.

Local Lemma nomut_safe_value : forall Gamma x t tx T Tx,
  value tx ->
  empty |-- tx is Tx ->
  safe Gamma[x <== Tx] |-- t is T ->
  has_var x t ->
  no_mut v.
Proof.
  intros * Hval **.
  inv Hval; inv_type; eauto using no_mut;
  exfalso; eapply hasvar_typing; eauto;
  unfold safe; rewrite lookup_update_eq; reflexivity.
Qed.

Local Lemma ss_subst : forall Gamma x t v T Tx,
  value v ->
  empty |-- v is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  (* --- *)
  safe_spawns v ->
  safe_spawns t ->
  safe_spawns ([x := v] t).
Proof.
  intros * ? ? ? ? Hss.
  generalize dependent Gamma. generalize dependent T. generalize dependent Tx.
  induction Hss; intros; invc_type;
  simpl; eauto using safe_spawns;
  try solve [destruct string_eq_dec;
             eauto using safe_spawns,
                         ctx_eqv_typing,
                         MapEquivalence.update_permutation].
  eapply ss_spawn. destruct (hasvar_dec x t).
  - eauto using nomut_safe_value, (must_subst (fun _ t => no_mut t) nil).
  - erewrite hasvar_subst; assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ss_preservation_mem_alloc : forall m t t' v T,
  forall_memory m safe_spawns ->
  safe_spawns t ->
  t --[e_Alloc (#m) v T]--> t' ->
  forall_memory (m +++ (v, T)) safe_spawns.
Proof.
  intros. unfold forall_memory.
  eauto using forall_array_add, ss_tstep_alloc_value, safe_spawns.
Qed.

Lemma ss_preservation_mem_write : forall m t t' ad v T,
  forall_memory m safe_spawns ->
  safe_spawns t ->
  t --[e_Write ad v T]--> t' ->
  forall_memory m[ad <- (v, T)] safe_spawns.
Proof.
  intros. unfold forall_memory.
  eauto using forall_array_set, ss_tstep_write_value, safe_spawns.
Qed.

Lemma ss_preservation_spawned : forall t1 t2 t,
  safe_spawns t1 ->
  t1 --[e_Spawn t]--> t2 ->
  safe_spawns t.
Proof.
  intros. induction_tstep; inv_ss; eauto using nomut_then_ss.
Qed.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_ss_preservation :=
  match goal with
  | H1 : forall_threads ?ths well_typed_term,
    H2 : forall_threads ?ths safe_spawns,
    _  : ?ths[?tid] --[_]--> _ 
      |- _ =>
    destruct (H1 tid) as [T' ?]; specialize (H2 tid); generalize dependent T';
    induction_tstep; intros; inv_type; inv_ss; eauto using safe_spawns
  end.

Theorem ss_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  (* --- *)
  forall_program m1 ths1 safe_spawns ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 safe_spawns.
Proof.
  split_preservation.
  - (* spawn     *) solve_ss_preservation.
  - (* spawned   *) eauto using ss_preservation_spawned.
  - (* unit      *) eauto using safe_spawns.
  - (* mem_alloc *) eauto using ss_preservation_mem_alloc.
  - (* alloc     *) solve_ss_preservation.
  - (* read      *) solve_ss_preservation.
  - (* mem_write *) eauto using ss_preservation_mem_write.
  - (* write     *) solve_ss_preservation.
  - (* none      *) solve_ss_preservation.
                    invc_type. invc_ss. eauto using ss_subst.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma nacc_mem_add : forall m t ad tT,
  ~ access (#m) m t ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad (m +++ tT) t.
Proof.
  intros ** Hacc.
  induction Hacc; do 2 inv_nacc; eauto.
  Array.sga; eauto.
Qed.

Lemma nacc_mem_set1 : forall m t ad ad' v T,
  ~ access ad m v ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad m[ad' <- (v, T)] t.
Proof.
  assert (forall m ad ad' v,
    access ad m[ad' <- v] m[ad' <- v][ad'].tm -> ad' < #m). {
      intros * H. decompose sum (lt_eq_lt_dec ad' (#m)); subst; trivial;
      simpl_array; simpl in *; inv_acc.
  }
  (* main proof *)
  intros ** Hacc. 
  induction Hacc; eauto using access.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  destruct (nat_eq_dec ad' ad''); subst;
  try (assert (ad'' < #m) by eauto);
  simpl_array; eauto using access.
Qed.

Lemma nacc_mem_set2 : forall m t ad ad' v T,
  ~ access ad' m t ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad m[ad' <- (v, T)] t.
Proof.
  intros ** Hacc.
  induction Hacc; do 2 inv_nacc; eauto using access.
  simpl_array. eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_none : forall m t1 t2 ad,
  ~ access ad m t1 ->
  t1 --[e_None]--> t2 ->
  ~ access ad m t2.
Proof.
  intros.
  induction_tstep; inv_nacc; eauto with acc.
  inv_nacc. eauto using (may_subst (access ad)).
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_alloc : forall m t1 t2 ad v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t1 ->
  (* --- *)
  ad < #m ->
  ~ access ad m t1 ->
  t1 --[e_Alloc (#m) v T]--> t2 ->
  ~ access ad (m +++ (v, T)) t2.
Proof.
  intros.
  induction_tstep; inv_vad; inv_nacc;
  eauto using nacc_mem_add, nacc_vad_length with acc.
  eapply nacc_ref; try lia. simpl_array.
  eauto using nacc_mem_add, nacc_vad_length.
Qed.

Lemma nacc_preservation_unt_alloc : forall m t1 t2 t ad ad' v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  ~ access ad m t ->
  t1 --[e_Alloc ad' v T]--> t2 ->
  ~ access ad (m +++ (v, T)) t.
Proof.
  eauto using nacc_mem_add, nacc_vad_length.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_read : forall m t1 t2 ad ad',
  ~ access ad m t1 ->
  t1 --[e_Read ad' m[ad'].tm]--> t2 ->
  ~ access ad m t2.
Proof.
  intros. induction_tstep; inv_nacc; eauto with acc. inv_nacc. assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_write : forall m t1 t2 ad ad' v T,
  ~ access ad m t1 ->
  t1 --[e_Write ad' v T]--> t2 ->
  ~ access ad (m[ad' <- (v, T)]) t2.
Proof.
  intros.
  assert (~ access ad m v) by eauto using nacc_tstep_write_value;
  induction_tstep; inv_nacc; eauto using nacc_mem_set1 with acc.
Qed.

Lemma nacc_preservation_unt_write : forall m t1 t2 t ad ad' v T,
  well_typed_term t1 ->
  (access ad' m t -> ~ unsafe_access ad' m t1) ->
  (* --- *)
  ~ access ad m t ->
  t1 --[e_Write ad' v T]--> t2 ->
  ~ access ad m[ad' <- (v, T)] t.
Proof.
  intros * ? Hsms **.
  eapply nacc_mem_set2; eauto.
  assert (unsafe_access ad' m t1) by eauto using tstep_write_requires_uacc.
  intros ?. eapply Hsms; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_spawn : forall m t1 t2 t ad,
  ~ access ad m t1 ->
  t1 --[e_Spawn t]--> t2 ->
  ~ access ad m t2.
Proof.
  intros ** ?. induction_tstep; try inv_nacc; inv_acc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem nacc_preservation : forall m1 m2 ths1 ths2 ad tid tid' e,
  forall_memory m1 (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 well_typed_term ->
  safe_memory_sharing m1 ths1 ->
  (* --- *)
  ad < #m1 ->
  tid < #ths1 ->
  ~ access ad m1 ths1[tid] ->
  m1 / ths1 ~~[tid', e]~~> m2 / ths2 ->
  ~ access ad m2 ths2[tid].
Proof.
  split_preservation.
  - eauto using nacc_preservation_spawn.
  - eauto using nacc_preservation_alloc.
  - eauto using nacc_preservation_unt_alloc.
  - eauto using nacc_preservation_read.
  - eauto using nacc_preservation_write.
  - eauto using nacc_preservation_unt_write.
  - eauto using nacc_preservation_none.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-unsafe-access                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma nuacc_mem_add : forall m t ad tT,
  ~ unsafe_access (#m) m t ->
  (* --- *)
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad (m +++ tT) t.
Proof.
  intros ** Huacc.
  induction Huacc; inv_nuacc; eauto using unsafe_access.
  Array.sga; eauto using unsafe_access; inv_nuacc; eauto.
  simpl in *. inv_uacc.
Qed.

Lemma nuacc_mem_set1 : forall m t ad ad' v T,
  ~ unsafe_access ad m v ->
  (* --- *)
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m[ad' <- (v, T)] t.
Proof.
  assert (H : forall m m' ad ad',
    unsafe_access ad m m'[ad'].tm -> ad' < #m'). {
      intros * H. decompose sum (lt_eq_lt_dec ad' (#m')); subst; trivial;
      simpl_array; simpl in *; inv_uacc.
  }
  (* main proof *)
  intros ** Huacc.
  induction Huacc; eauto using unsafe_access.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  eapply H in Huacc. rewrite set_preserves_length in Huacc.
  Array.sgs; eauto using unsafe_access.
Qed.

Lemma nuacc_mem_set2 : forall m t ad ad' tT,
  ~ unsafe_access ad' m t ->
  (* --- *)
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m[ad' <- tT] t.
Proof.
  intros ** Huacc.
  induction Huacc; inv_nuacc; inv_nuacc; eauto.
  match goal with _ : _ <> ?ad |- _ => destruct (nat_eq_dec ad' ad); subst end;
  simpl_array; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_none : forall m t1 t2 ad,
  ~ unsafe_access ad m t1 ->
  t1 --[e_None]--> t2 ->
  ~ unsafe_access ad m t2.
Proof.
  intros ** Huacc.
  induction_tstep; inv_nuacc; try inv_uacc; eauto.
  inv_nuacc. contradict Huacc. eauto using (may_subst (unsafe_access ad)).
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_alloc : forall m t1 t2 ad v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t1 ->
  (* --- *)
  ad < #m ->
  ~ unsafe_access ad m t1 ->
  t1 --[e_Alloc (#m) v T]--> t2 ->
  ~ unsafe_access ad (m +++ (v, T)) t2.
Proof.
  intros ** ?.
  induction_tstep; inv_vad; inv_nuacc; invc_uacc; eauto;
  match goal with F : unsafe_access _ (_ +++ _) _ |- _ => contradict F end;
  try simpl_array; eauto using nacc_vad_length, nacc_then_nuacc, nuacc_mem_add.
Qed.

Lemma nuacc_preservation_unt_alloc : forall m t1 t2 t ad ad' v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  ~ unsafe_access ad m t ->
  t1 --[e_Alloc ad' v T]--> t2 ->
  ~ unsafe_access ad (m +++ (v, T)) t.
Proof.
  eauto using nuacc_mem_add, nuacc_vad_length.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_read : forall m t1 t2 ad ad',
  forall_memory m value ->
  well_typed_term t1 ->
  consistently_typed_references m t1 ->
  (* --- *)
  ~ unsafe_access ad m t1 ->
  t1 --[e_Read ad' m[ad'].tm]--> t2 ->
  ~ unsafe_access ad m t2.
Proof.
  intros ** ?.
  induction_tstep; intros;
  inv_wtt; inv_ctr; inv_nuacc; try invc_uacc; eauto;
  inv_wtt; destruct (nat_eq_dec ad' ad); subst; eauto using unsafe_access;
  inv_ctr;
  match goal with F : unsafe_access _ _ _[_].tm |- _ => contradict F end;
  eauto using nuacc_from_immutable_type.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_write : forall m t1 t2 ad ad' v T,
  ~ unsafe_access ad m t1 ->
  t1 --[e_Write ad' v T]--> t2 ->
  ~ unsafe_access ad m[ad' <- (v, T)] t2.
Proof.
  assert (forall m t t' ad ad' v T,
    ~ unsafe_access ad m t ->
    t --[e_Write ad' v T]--> t' ->
    ~ unsafe_access ad m v)
    by (intros; induction_tstep; eauto using unsafe_access).
  (* main proof *)
  intros ** ?. induction_tstep; inv_nuacc; invc_uacc; eauto;
  match goal with _ : unsafe_access _ _ ?t |- _ => rename t into tx end;
  eapply (nuacc_mem_set1 _ tx _ _ v); eauto.
Qed.

Lemma nuacc_preservation_unt_write : forall m t1 t2 t ad ad' v T,
  well_typed_term t1 ->
  (access ad' m t -> ~ unsafe_access ad' m t1) ->
  (* --- *)
  ~ unsafe_access ad m t ->
  t1 --[e_Write ad' v T]--> t2 ->
  ~ unsafe_access ad m[ad' <- (v, T)] t.
Proof.
  intros * ? Hsms **.
  eapply nuacc_mem_set2; eauto.
  assert (unsafe_access ad' m t1) by eauto using tstep_write_requires_uacc.
  intros ?. eapply Hsms; eauto using uacc_then_acc.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_spawn : forall m t1 t2 t ad,
  ~ unsafe_access ad m t1 ->
  t1 --[e_Spawn t]--> t2 ->
  ~ unsafe_access ad m t2.
Proof.
  intros ** ?. induction_tstep; inv_uacc; eauto; inv_nuacc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem nuacc_preservation : forall m1 m2 ths1 ths2 tid tid' ad e,
  forall_memory m1 value ->
  forall_memory m1 (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistently_typed_references m1) ->
  safe_memory_sharing m1 ths1 ->
  (* --- *)
  ad < #m1 ->
  tid < #ths1 ->
  ~ unsafe_access ad m1 ths1[tid] ->
  m1 / ths1 ~~[tid', e]~~> m2 / ths2 ->
  ~ unsafe_access ad m2 ths2[tid].
Proof.
  split_preservation.
  - eauto using nuacc_preservation_spawn. 
  - eauto using nuacc_preservation_alloc. 
  - eauto using nuacc_preservation_unt_alloc. 
  - eauto using nuacc_preservation_read. 
  - eauto using nuacc_preservation_write. 
  - eauto using nuacc_preservation_unt_write. 
  - eauto using nuacc_preservation_none. 
Qed.

(* unused *)
Local Corollary nuacc_preservation_corollary_from_nacc_preservation :
  forall m1 m2 ths1 ths2 ad tid tid' e,
    forall_memory m1 value ->
    forall_memory m1 (valid_addresses m1) ->
    forall_memory m1 well_typed_term ->
    forall_memory m1 (consistently_typed_references m1) ->
    forall_threads ths1 (valid_addresses m1) ->
    forall_threads ths1 well_typed_term ->
    forall_threads ths1 (consistently_typed_references m1) ->
    safe_memory_sharing m1 ths1 ->
    (* --- *)
    ad < #m1 ->
    tid < #ths1 ->
    ~ unsafe_access ad m1 ths1[tid] ->
    m1 / ths1 ~~[tid', e]~~> m2 / ths2 ->
    ~ unsafe_access ad m2 ths2[tid].
Proof.
  intros.
  assert (forall_program m2 ths2 (consistently_typed_references m2))
    as [? ?] by (eapply ctr_preservation; eauto).
  destruct (acc_dec ad m1 ths1[tid]).
  - intros ?.
    assert (safe_access ad m1 ths1[tid]) by (split; eauto).
    eapply (ptyp_sacc_uacc_contradiction m1 m2 ths1[tid] ths2[tid]);
    eauto using value_preservation, ptyp_cstep_preservation.
  - eauto using nacc_then_nuacc, nacc_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* safe-memory-sharing                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_write_sms_helper : forall m t ad v ths tid tid' T,
  tid <> tid' ->
  forall_threads ths well_typed_term ->
  safe_memory_sharing m ths ->
  ths[tid] --[e_Write ad v T]--> t ->
  ~ access ad m ths[tid'].
Proof.
  assert (forall m t t' ad v T Te,
    empty |-- t is T ->
    t --[e_Write ad v Te]--> t' ->
    unsafe_access ad m t
  ). {
    intros. generalize dependent T.
    induction_tstep; intros; inv_type; eauto using unsafe_access.
    inv_type. eauto using unsafe_access.
  }
  (* main proof *)
  intros * Hneq Htype Hsms ? Hacc.
  destruct (Htype tid). specialize (Hsms _ _ _ Hneq Hacc); eauto.
Qed.

(* tstep ----------------------------------------------------------------- *)

(* Three cases:
   - needs nuacc-tstep-preservation;
   - needs acc-tstep-inheritance;
   - just safe-memory-sharing.
*)

Local Ltac destruct_sms ths tid tid1 tid2 :=
  assert (Hlt : tid < #ths) by eauto using tstep_length_tid;
  destruct (nat_eq_dec tid tid1), (nat_eq_dec tid tid2); subst;
  try contradiction.

Local Lemma sms_tstep_none_preservation : forall m t ths tid,
  safe_memory_sharing m ths ->
  ths[tid] --[e_None]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros ** tid1 tid2 **. destruct_sms ths tid tid1 tid2; simpl_array;
  eauto using nuacc_preservation_none, acc_tstep_none_inheritance.
Qed.

Local Lemma sms_tstep_alloc_preservation : forall m t v ths tid T,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[e_Alloc (#m) v T]--> t ->
  safe_memory_sharing (m +++ (v, T)) ths[tid <- t].
Proof.
  intros * ? Hvad ** tid1 tid2 ** Huacc.
  assert (forall tid, ~ unsafe_access (#m) m ths[tid])
    by eauto using nuacc_vad_length.
  eapply uacc_then_acc in Huacc as ?. contradict Huacc.
  destruct_sms ths tid tid1 tid2; simpl_array;
  eauto 6 using acc_mem_add_inheritance,
                acc_tstep_alloc_inheritance,
                nuacc_mem_add,
                nuacc_preservation_alloc,
                vad_acc.
Qed.

Local Lemma sms_tstep_read_preservation : forall m t ad ths tid,
  forall_memory m value ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[e_Read ad m[ad].tm]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros * ? Hwtt ** tid1 tid2 **. destruct (Hwtt tid1).
  destruct_sms ths tid tid1 tid2; simpl_array;
  eauto using acc_tstep_read_inheritance, nuacc_preservation_read.
Qed.

Local Lemma sms_tstep_write_preservation : forall m ths t tid ad v T,
  forall_threads ths well_typed_term ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[e_Write ad v T]--> t ->
  safe_memory_sharing m[ad <- (v, T)] ths[tid <- t].
Proof.
  intros ** tid1 tid2 ** Huacc.
  eapply uacc_then_acc in Huacc as ?. contradict Huacc.
  destruct_sms ths tid tid1 tid2; simpl_array;
  try assert (~ access ad m ths[tid1]) by eauto using step_write_sms_helper;
  try assert (~ access ad m ths[tid2]) by eauto using step_write_sms_helper;
  eauto 7 using uacc_then_acc,
    nuacc_preservation_write,
    acc_tstep_write_inheritance,
    nuacc_mem_set2,
    alt_acc_mem_set_inheritance.
Qed.

Local Lemma sms_tstep_spawn_preservation : forall m ths t block tid,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  forall_memory m (consistently_typed_references m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (consistently_typed_references m) ->
  forall_threads ths safe_spawns ->
  (* --- *)
  tid < #ths ->
  safe_memory_sharing m ths ->
  ths[tid] --[e_Spawn block]--> t ->
  safe_memory_sharing m (ths[tid <- t] +++ block).
Proof.
  intros ** tid1 tid2 **.
  destruct_sms ths tid tid1 tid2;
  decompose sum (lt_eq_lt_dec tid1 (#ths)); subst;
  decompose sum (lt_eq_lt_dec tid2 (#ths)); subst;
  simpl_array;
  try solve [lia | inv_acc | intros ?; inv_uacc];
  eauto using nuacc_preservation_spawn, acc_tstep_spawn_inheritance;
  assert (~ unsafe_access ad m block) by eauto using spawn_nuacc; eauto;
  assert (consistently_typed_references m block)
    by eauto using (tstep_spawn_block consistently_typed_references);
  eauto using uacc_by_association, ctr_preservation_spawn.
Qed.

Local Corollary sms_mstep_preservation : forall m m' t e ths tid,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  (* --- *)
  safe_memory_sharing m ths ->
  m / ths[tid] ==[e]==> m' / t ->
  safe_memory_sharing m' ths[tid <- t].
Proof.
  intros. inv_mstep;
  eauto using sms_tstep_none_preservation,
              sms_tstep_alloc_preservation,
              sms_tstep_read_preservation,
              sms_tstep_write_preservation.
Qed.

(* safe-memory-sharing preservation -------------------------------------- *)

Theorem sms_preservation : forall m m' ths ths' tid e,
  forall_memory m value ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  forall_program m ths safe_spawns ->
  (* --- *)
  safe_memory_sharing m ths ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  safe_memory_sharing m' ths'.
Proof.
  intros * ? [? ?] [_ ?] [? ?] [_ ?] **. split_preservation;
  eauto using sms_tstep_none_preservation,
              sms_tstep_alloc_preservation,
              sms_tstep_read_preservation,
              sms_tstep_write_preservation,
              sms_tstep_spawn_preservation.
Qed.

