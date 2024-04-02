From Coq Require Import Lia.

From Elo Require Import Core.
From Elo Require Import Properties.
From Elo Require Import PtrTyp.
From Elo Require Import Lemmas.
From Elo Require Import Generic.
From Elo Require Import Inheritance.

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
    invc_cstep; try invc_mstep; split; trivial; try simplfths; trivial
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
(* valid-addresses                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma vad_mem_add : forall m t vT,
  valid_addresses m t ->
  valid_addresses (m +++ vT) t.
Proof.
  intros.
  induction t; try inv_vad; eauto using valid_addresses.
  eapply vad_ref. rewrite add_increments_length. eauto.
Qed.

Lemma vad_mem_set : forall m t ad vT,
  valid_addresses m t ->
  valid_addresses m[ad <- vT] t.
Proof.
  intros.
  induction t; try inv_vad; eauto using valid_addresses.
  eapply vad_ref. rewrite set_preserves_length. assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma vad_preservation_none : forall m t1 t2,
  valid_addresses m t1 ->
  t1 --[EF_None]--> t2 ->
  valid_addresses m t2.
Proof.
  intros.
  induction_tstep; inv_vad; eauto using valid_addresses.
  inv_vad. eauto using (must_subst valid_addresses).
Qed.

(* ------------------------------------------------------------------------- *)

Lemma vad_preservation_mem_alloc : forall m t1 t2 v T,
  valid_addresses m t1 ->
  (* --- *)
  forall_memory m (valid_addresses m) ->
  t1 --[EF_Alloc (#m) v T]--> t2 ->
  forall_memory (m +++ (v, T)) (valid_addresses (m +++ (v, T))).
Proof.
  intros.
  induction_tstep; inv_vad; eauto. 
  intros ad'. Array.sga; eauto using vad_mem_add, valid_addresses.
Qed.

Lemma vad_preservation_alloc : forall m t1 t2 v T,
  valid_addresses m t1 ->
  t1 --[EF_Alloc (#m) v T]--> t2 ->
  valid_addresses (m +++ (v, T)) t2.
Proof.
  intros.
  induction_tstep; inv_vad; eauto using vad_mem_add, valid_addresses.
  eapply vad_ref. rewrite add_increments_length. eauto.
Qed.

Lemma vad_preservation_unt_alloc : forall m t1 t2 t ad v T,
  valid_addresses m t ->
  t1 --[EF_Alloc ad v T]--> t2 ->
  valid_addresses (m +++ (v, T)) t.
Proof.
  intros. induction_tstep; eauto using vad_mem_add.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma vad_preservation_read : forall m t1 t2 ad,
  forall_memory m (valid_addresses m) ->
  (* --- *)
  valid_addresses m t1 ->
  t1 --[EF_Read ad m[ad].tm]--> t2 ->
  valid_addresses m t2.
Proof.
  intros.
  induction_tstep; inv_vad; eauto using valid_addresses.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma vad_preservation_mem_write : forall m t1 t2 ad v T,
  valid_addresses m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (valid_addresses m) ->
  t1 --[EF_Write ad v T]--> t2 ->
  forall_memory m[ad <- (v, T)] (valid_addresses m[ad <- (v, T)]).
Proof.
  intros.
  induction_tstep; inv_vad; eauto. 
  intros ad'. Array.sgs; eauto using vad_mem_set.
Qed.

Lemma vad_preservation_write : forall m t1 t2 ad v T,
  valid_addresses m t1 ->
  t1 --[EF_Write ad v T]--> t2 ->
  valid_addresses (m[ad <- (v, T)]) t2.
Proof.
  intros.
  induction_tstep; inv_vad; eauto using vad_mem_set, valid_addresses.
Qed.

Lemma vad_preservation_unt_write : forall m t1 t2 t ad v T,
  valid_addresses m t ->
  t1 --[EF_Write ad v T]--> t2 ->
  valid_addresses m[ad <- (v, T)] t.
Proof.
  intros. induction_tstep; eauto using vad_mem_set.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma vad_preservation_spawn : forall m t1 t2 t,
  valid_addresses m t1 ->
  t1 --[EF_Spawn t]--> t2 ->
  valid_addresses m t2.
Proof.
  intros. induction_tstep; inv_vad; eauto using valid_addresses.
Qed.

Lemma vad_preservation_spawned : forall m t1 t2 t,
  valid_addresses m t1 ->
  t1 --[EF_Spawn t]--> t2 ->
  valid_addresses m t.
Proof.
  intros. induction_tstep; inv_vad; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem vad_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_addresses m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (valid_addresses m2).
Proof.
  split_preservation.
  - eauto using vad_preservation_spawn.
  - eauto using vad_preservation_spawned.
  - eauto using valid_addresses.
  - eauto using vad_preservation_mem_alloc.
  - eauto using vad_preservation_alloc.
  - eauto using vad_preservation_unt_alloc.
  - eauto using vad_preservation_read.
  - eauto using vad_preservation_mem_write.
  - eauto using vad_preservation_write.
  - eauto using vad_preservation_unt_write.
  - eauto using vad_preservation_none.
Qed.

(* ------------------------------------------------------------------------- *)

Corollary vad_cstep_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (valid_addresses m2).
Proof.
  intros.
  assert (forall_program m2 ths2 (valid_addresses m2))
    by eauto using vad_preservation.
  destruct_forall_program. assumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* consistently-typed-references                                             *)
(* ------------------------------------------------------------------------- *)

Lemma ctr_mem_add : forall m t vT,
  valid_addresses m t ->
  (* --- *)
  consistently_typed_references m t ->
  consistently_typed_references (m +++ vT) t.
Proof.
  intros.
  induction t; eauto using consistently_typed_references;
  inv_vad; inv_ctr; eauto using consistently_typed_references;
  (eapply ctr_refM || eapply ctr_refI); simpl_array; assumption.
Qed.

Lemma ctr_mem_set : forall m t ad v T Tv,
  ad < #m ->
  empty |-- v is Tv ->
  m[ad].typ = T ->
  m[ad].typ = <{{&Tv}}> ->
  (* --- *)
  consistently_typed_references m t ->
  consistently_typed_references m[ad <- (v, T)] t.
Proof.
  intros.
  induction t; eauto using consistently_typed_references;
  inv_ctr; eauto using consistently_typed_references;
  (eapply ctr_refM || eapply ctr_refI);
  match goal with H1 : _[?ad1].typ = _, H2 : _[?ad2].typ = _ |- _ =>
    destruct (nat_eq_dec ad1 ad2); subst;
    try (rewrite H1 in H2; inv H2)
  end;
  simpl_array; trivial.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ctr_preservation_none : forall m t1 t2,
  consistently_typed_references m t1 ->
  t1 --[EF_None]--> t2 ->
  consistently_typed_references m t2.
Proof.
  intros.
  induction_tstep; inv_ctr; eauto using consistently_typed_references.
  inv_ctr. eauto using (must_subst consistently_typed_references).
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ctr_preservation_mem_alloc : forall m t1 t2 v T,
  well_typed_term t1 ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t1 ->
  consistently_typed_references m t1 ->
  (* --- *)
  forall_memory m (consistently_typed_references m) ->
  t1 --[EF_Alloc (#m) v T]--> t2 ->
  forall_memory (m +++ (v, T)) (consistently_typed_references (m +++ (v, T))).
Proof.
  intros ** ad.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
  eauto using ctr_mem_add, consistently_typed_references; (* optimization *)
  eauto using ctr_mem_add, (tstep_alloc_value consistently_typed_references).
Qed.

Lemma ctr_preservation_alloc : forall m t1 t2 v T,
  well_typed_term t1 ->
  valid_addresses m t1 ->
  (* --- *)
  consistently_typed_references m t1 ->
  t1 --[EF_Alloc (#m) v T]--> t2 ->
  consistently_typed_references (m +++ (v, T)) t2.
Proof.
  intros * [T ?] **. generalize dependent T.
  induction_tstep; intros; inv_ctr; inv_type; inv_vad;
  eauto using ctr_mem_add, consistently_typed_references;
  (eapply ctr_refM || eapply ctr_refI); simpl_array; trivial.
Qed.

Lemma ctr_preservation_unt_alloc : forall m t1 t2 t ad v T,
  valid_addresses m t ->
  (* --- *)
  consistently_typed_references m t ->
  t1 --[EF_Alloc ad v T]--> t2 ->
  consistently_typed_references (m +++ (v, T)) t.
Proof.
  intros.
  induction_tstep; eauto using ctr_mem_add, consistently_typed_references.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ctr_preservation_read : forall m t1 t2 ad,
  consistently_typed_references m m[ad].tm ->
  (* --- *)
  consistently_typed_references m t1 ->
  t1 --[EF_Read ad m[ad].tm]--> t2 ->
  consistently_typed_references m t2.
Proof.
  intros.
  induction_tstep; inv_ctr; eauto using consistently_typed_references.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ctr_preservation_mem_write : forall m t1 t2 ad v T,
  well_typed_term t1 ->
  consistently_typed_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (consistently_typed_references m) ->
  t1 --[EF_Write ad v T]--> t2 ->
  forall_memory m[ad <- (v, T)] (consistently_typed_references m[ad <- (v, T)]).
Proof.
  intros ** ad'.
  assert (exists Tv, T = <{{&Tv}}>
                  /\ empty |-- v is Tv
                  /\ empty |-- m[ad].tm is Tv
                  /\ m[ad].typ = <{{&Tv}}>)
    as [? [? [? [? ?]]]] by eauto using consistently_typed_write_effect.
  subst. Array.sgs;
  eauto using ctr_mem_set, (tstep_write_value consistently_typed_references).
Qed.

Lemma ctr_preservation_write : forall m t1 t2 ad v T,
  well_typed_term t1 ->
  (* --- *)
  ad < #m ->
  consistently_typed_references m t1 ->
  t1 --[EF_Write ad v T]--> t2 ->
  consistently_typed_references (m[ad <- (v, T)]) t2.
Proof.
  intros.
  assert (exists Tv, T = <{{&Tv}}>
                  /\ empty |-- v is Tv
                  /\ empty |-- m[ad].tm is Tv
                  /\ m[ad].typ = <{{&Tv}}>)
    as [? [? [? [? ?]]]] by eauto using consistently_typed_write_effect.
  induction_tstep; intros; inv_wtt; inv_ctr;
  eauto using ctr_mem_set, consistently_typed_references.
Qed.

Lemma ctr_preservation_unt_write : forall m t1 t2 t ad v T,
  well_typed_term t1 ->
  consistently_typed_references m t1 ->
  (* --- *)
  ad < #m ->
  consistently_typed_references m t ->
  t1 --[EF_Write ad v T]--> t2 ->
  consistently_typed_references m[ad <- (v, T)] t.
Proof.
  intros.
  assert (exists Tv, T = <{{&Tv}}>
                  /\ empty |-- v is Tv
                  /\ empty |-- m[ad].tm is Tv
                  /\ m[ad].typ = <{{&Tv}}>)
  as [? [? [? [? ?]]]] by eauto using consistently_typed_write_effect.
  subst. eauto using ctr_mem_set.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ctr_preservation_spawn : forall m t1 t2 t,
  consistently_typed_references m t1 ->
  t1 --[EF_Spawn t]--> t2 ->
  consistently_typed_references m t2.
Proof.
  intros.
  induction_tstep; inv_ctr; eauto using consistently_typed_references.
Qed.

Lemma ctr_preservation_spawned : forall m t1 t2 t,
  consistently_typed_references m t1 ->
  t1 --[EF_Spawn t]--> t2 ->
  consistently_typed_references m t.
Proof.
  intros. induction_tstep; inv_ctr; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem ctr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  forall_program m1 ths1 (valid_addresses m1) ->
  (* --- *)
  forall_program m1 ths1 (consistently_typed_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (consistently_typed_references m2).
Proof.
  split_preservation.
  - eauto using ctr_preservation_spawn.
  - eauto using ctr_preservation_spawned.
  - eauto using consistently_typed_references.
  - eauto using ctr_preservation_mem_alloc.
  - eauto using ctr_preservation_alloc.
  - eauto using ctr_preservation_unt_alloc.
  - eauto using ctr_preservation_read.
  - eauto using ctr_preservation_mem_write.
  - eauto using ctr_preservation_write.
  - eauto using ctr_preservation_unt_write.
  - eauto using ctr_preservation_none.
Qed.

(* ------------------------------------------------------------------------- *)

Corollary ctr_cstep_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   well_typed_term ->
  forall_threads ths1 well_typed_term ->
  forall_memory  m1   (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  (* --- *)
  forall_memory m1 (consistently_typed_references m1) ->
  forall_threads ths1 (consistently_typed_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (consistently_typed_references m2).
Proof.
  intros.
  assert (forall_program m2 ths2 (consistently_typed_references m2))
    by (eapply ctr_preservation; eauto).
  destruct_forall_program. assumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma nacc_mem_add : forall m t ad vT,
  ~ access (#m) m t ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad (m +++ vT) t.
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
  t1 --[EF_None]--> t2 ->
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
  t1 --[EF_Alloc (#m) v T]--> t2 ->
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
  t1 --[EF_Alloc ad' v T]--> t2 ->
  ~ access ad (m +++ (v, T)) t.
Proof.
  eauto using nacc_mem_add, nacc_vad_length.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_read : forall m t1 t2 ad ad',
  ~ access ad m t1 ->
  t1 --[EF_Read ad' m[ad'].tm]--> t2 ->
  ~ access ad m t2.
Proof.
  intros. induction_tstep; inv_nacc; eauto with acc. inv_nacc. assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_write : forall m t1 t2 ad ad' v T,
  ~ access ad m t1 ->
  t1 --[EF_Write ad' v T]--> t2 ->
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
  t1 --[EF_Write ad' v T]--> t2 ->
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
  t1 --[EF_Spawn t]--> t2 ->
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

Module nuacc_preservation.
  Lemma nuacc_mem_add : forall m t ad vT,
    ~ unsafe_access (#m) m t ->
    (* --- *)
    ~ unsafe_access ad m t ->
    ~ unsafe_access ad (m +++ vT) t.
  Proof.
    intros ** Huacc. induction Huacc; inv_nuacc; eauto using unsafe_access.
    decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array;
    simpl in *; eauto using unsafe_access; inv_nuacc; eauto. inv_uacc.
  Qed.

  Local Lemma nuacc_mem_set : forall m t ad ad' v T,
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
    intros ** Huacc. induction Huacc; eauto using unsafe_access.
    match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
    eapply H in Huacc. rewrite set_preserves_length in Huacc.
    destruct (nat_eq_dec ad' ad''); subst; simpl_array;
    eauto using unsafe_access.
  Qed.

  Lemma alt_nuacc_mem_set_preservation : forall m t ad ad' vT,
    ~ unsafe_access ad' m t ->
    (* --- *)
    ~ unsafe_access ad m t ->
    ~ unsafe_access ad m[ad' <- vT] t.
  Proof.
    intros ** Huacc. induction Huacc; inv_nuacc; inv_nuacc; eauto.
    match goal with _ : _ <> ?ad |- _ =>
      destruct (nat_eq_dec ad' ad); subst
    end;
    simpl_array; eauto.
  Qed.

  (* tstep ----------------------------------------------------------------- *)

  Lemma nuacc_tstep_none_preservation : forall m t t' ad,
    ~ unsafe_access ad m t ->
    t --[EF_None]--> t' ->
    ~ unsafe_access ad m t'.
  Proof.
    intros ** Huacc. induction_tstep; inv_nuacc;
    try inv_uacc; eauto. inv_nuacc.
    contradict Huacc. eauto using (may_subst (unsafe_access ad)).
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
    eauto using nacc_vad_length, nacc_then_nuacc, nuacc_mem_add.
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
    eapply (nuacc_mem_set _ tx _ _ v); eauto.
  Qed.

  Lemma nuacc_tstep_spawn_preservation : forall m t t' ad block,
    ~ unsafe_access ad m t ->
    t --[EF_Spawn block]--> t' ->
    ~ unsafe_access ad m t'.
  Proof.
    intros ** ?. induction_tstep; inv_uacc; eauto; inv_nuacc; eauto.
  Qed.

  (* mstep ----------------------------------------------------------------- *)

  Local Corollary nuacc_mstep_preservation : forall m m' t t' e ad,
    forall_memory m value ->
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    well_typed_term t ->
    consistently_typed_references m t ->
    ad < #m ->
    (* --- *)
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

  (* cstep ----------------------------------------------------------------- *)

  (* TODO *)
  Lemma nuacc_untouched_preservation : forall m m' ths tid tid' t' ad e,
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
    eauto using nuacc_mem_add, nuacc_vad_length.
    eapply alt_nuacc_mem_set_preservation; eauto.
    assert (unsafe_access ad m ths[tid])
      by eauto using tstep_write_requires_uacc.
    intros ?. eapply (Hsms tid tid'); eauto using uacc_then_acc.
  Qed.

  (* not-unsafe-access preservation ---------------------------------------- *)

  Theorem nuacc_preservation : forall m m' ths ths' tid tid' ad e,
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
    (* split for performance *)
    eauto using nuacc_tstep_spawn_preservation.
    eauto using nuacc_mstep_preservation.
    eauto using nuacc_untouched_preservation.
  Qed.
End nuacc_preservation.
Import nuacc_preservation.

(* ------------------------------------------------------------------------- *)
(* safe-spawns                                                               *)
(* ------------------------------------------------------------------------- *)

Module ss_preservation.
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

  Local Lemma nomut_safe_value : forall Gamma x t v T Tx,
    value v ->
    empty |-- v is Tx ->
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
    intros.
    generalize dependent Gamma. generalize dependent T. generalize dependent Tx.
    induction t; simpl; intros; invc_type; try inv_ss;
    try (destruct string_eq_dec);
    eauto using safe_spawns, ctx_eqv_typing, MapEquivalence.update_permutation.
    eapply ss_spawn. destruct (hasvar_dec x t).
    - eauto using nomut_safe_value, (must_subst (fun _ t => no_mut t) nil).
    - erewrite hasvar_subst; assumption.
  Qed.

  (* tstep ----------------------------------------------------------------- *)

  Local Lemma ss_tstep_spawn_preservation : forall t t' block,
    safe_spawns t ->
    t --[EF_Spawn block]--> t' ->
    safe_spawns t'.
  Proof.
    intros. induction_tstep; inv_ss; eauto using safe_spawns.
  Qed.

  (* mstep ----------------------------------------------------------------- *)

  Local Lemma ss_mstep_preservation : forall m m' t t' e,
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

  (* cstep ----------------------------------------------------------------- *)

  Local Lemma ss_thread_default :
    safe_spawns thread_default.
  Proof.
    eauto using safe_spawns.
  Qed.

  Local Lemma ss_spawn_block : forall t t' block,
    safe_spawns t ->
    t --[EF_Spawn block]--> t' ->
    safe_spawns block.
  Proof.
    intros. induction_tstep; inv_ss; eauto using nomut_then_ss.
  Qed.

  Local Corollary ss_cstep_preservation : forall m m' ths ths' tid e,
    forall_threads ths well_typed_term ->
    (* --- *)
    forall_memory m safe_spawns ->
    forall_threads ths safe_spawns ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' safe_spawns.
  Proof.
    eauto using memoryless_cstep_preservation,
      ss_tstep_spawn_preservation,
      ss_mstep_preservation,
      ss_thread_default,
      ss_spawn_block.
  Qed.

  (* tstep mem ------------------------------------------------------------- *)

  Local Lemma ss_tstep_alloc_mem_preservation : forall m t t' v T,
    forall_memory m safe_spawns ->
    safe_spawns t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    forall_memory (m +++ (v, T)) safe_spawns.
  Proof.
    intros. unfold forall_memory.
    eauto using forall_array_add, ss_tstep_alloc_value, safe_spawns.
  Qed.

  Local Lemma ss_tstep_write_mem_preservation : forall m t t' ad v T,
    forall_memory m safe_spawns ->
    safe_spawns t ->
    t --[EF_Write ad v T]--> t' ->
    forall_memory m[ad <- (v, T)] safe_spawns.
  Proof.
    intros. unfold forall_memory.
    eauto using forall_array_set, ss_tstep_write_value, safe_spawns.
  Qed.

  (* mstep mem ------------------------------------------------------------- *)

  Local Corollary ss_mstep_mem_preservation : forall m m' t t' e,
    forall_memory m safe_spawns ->
    safe_spawns t ->
    m / t ==[e]==> m' / t' ->
    forall_memory m' safe_spawns.
  Proof.
    intros. inv_mstep;
    eauto using ss_tstep_alloc_mem_preservation, ss_tstep_write_mem_preservation.
  Qed.

  (* safe-spawns preservation ---------------------------------------------- *)

  Theorem ss_preservation : forall m m' ths ths' tid e,
    forall_program m ths well_typed_term ->
    (* --- *)
    forall_program m ths safe_spawns ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_program m' ths' safe_spawns.
  Proof.
    intros * [? ?] [? ?] **. split; inv_cstep;
    eauto using ss_cstep_preservation, ss_mstep_mem_preservation.
  Qed.
End ss_preservation.

(* ------------------------------------------------------------------------- *)
(* safe-memory-sharing                                                       *)
(* ------------------------------------------------------------------------- *)

Module sms_preservation.
  Local Lemma step_write_sms_helper : forall m t ad v ths tid tid' T,
    tid <> tid' ->
    forall_threads ths well_typed_term ->
    safe_memory_sharing m ths ->
    ths[tid] --[EF_Write ad v T]--> t ->
    ~ access ad m ths[tid'].
  Proof.
    assert (forall m t t' ad v T Te,
      empty |-- t is T ->
      t --[EF_Write ad v Te]--> t' ->
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
    ths[tid] --[EF_None]--> t ->
    safe_memory_sharing m ths[tid <- t].
  Proof.
    intros ** tid1 tid2 **. destruct_sms ths tid tid1 tid2; simpl_array.
    - eauto using nuacc_tstep_none_preservation.
    - eauto using acc_tstep_none_inheritance.
    - eauto.
  Qed.

  Local Lemma sms_tstep_alloc_preservation : forall m t v ths tid T,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    (* --- *)
    safe_memory_sharing m ths ->
    ths[tid] --[EF_Alloc (#m) v T]--> t ->
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
                  nuacc_tstep_alloc_preservation,
                  vad_acc.
  Qed.

  Local Lemma sms_tstep_read_preservation : forall m t ad ths tid,
    forall_memory m value ->
    forall_threads ths well_typed_term ->
    forall_threads ths (consistently_typed_references m) ->
    (* --- *)
    safe_memory_sharing m ths ->
    ths[tid] --[EF_Read ad m[ad].tm]--> t ->
    safe_memory_sharing m ths[tid <- t].
  Proof.
    intros * ? Hwtt ** tid1 tid2 **. destruct (Hwtt tid1).
    destruct_sms ths tid tid1 tid2; simpl_array;
    eauto using acc_tstep_read_inheritance, nuacc_tstep_read_preservation.
  Qed.

  Local Lemma sms_tstep_write_preservation : forall m ths t tid ad v T,
    forall_threads ths well_typed_term ->
    (* --- *)
    safe_memory_sharing m ths ->
    ths[tid] --[EF_Write ad v T]--> t ->
    safe_memory_sharing m[ad <- (v, T)] ths[tid <- t].
  Proof.
    intros ** tid1 tid2 ** Huacc.
    eapply uacc_then_acc in Huacc as ?. contradict Huacc.
    destruct_sms ths tid tid1 tid2; simpl_array;
    try assert (~ access ad m ths[tid1]) by eauto using step_write_sms_helper;
    try assert (~ access ad m ths[tid2]) by eauto using step_write_sms_helper;
    eauto 7 using uacc_then_acc,
      nuacc_tstep_write_preservation,
      acc_tstep_write_inheritance,
      alt_nuacc_mem_set_preservation,
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
    ths[tid] --[EF_Spawn block]--> t ->
    safe_memory_sharing m (ths[tid <- t] +++ block).
  Proof.
    intros ** tid1 tid2 **.
    destruct_sms ths tid tid1 tid2;
    decompose sum (lt_eq_lt_dec tid1 (#ths)); subst;
    decompose sum (lt_eq_lt_dec tid2 (#ths)); subst;
    simpl_array;
    try solve [inv_tstep | inv_acc | intros ?; inv_uacc | lia];
    eauto using nuacc_tstep_spawn_preservation, acc_tstep_spawn_inheritance;
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
End sms_preservation.

