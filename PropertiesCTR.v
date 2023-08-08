From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Module Preservation.

  (* auxiliary. *)
  Local Lemma step_write_wtt : forall m t t' ad v Tr T,
    empty |-- t is T ->
    t --[EF_Write ad v Tr]--> t' ->
    consistently_typed_references m t ->
    (Tr = m[ad].typ /\ exists V, empty |-- v is V /\ empty |-- m[ad].tm is V).
  Proof.
    intros * ? ?.
    assert (exists V, empty |-- v is V) as [? ?].
    { generalize dependent T. induction_tstep; intros; inv_type; eauto. }
    intros. generalize dependent T.
    induction_tstep; intros; inv_type; inv_ctr; eauto.
    inv_type. inv_ctr. apply_deterministic_typing. eauto.
  Qed.

  (* subst & mem ----------------------------------------------------------- *)

  Lemma ctr_subst_preservation : forall m t tx x,
    consistently_typed_references m t ->
    consistently_typed_references m tx ->
    consistently_typed_references m ([x := tx] t).
  Proof.
    intros. induction t; trivial;
    try solve [inv_ctr; eauto using consistently_typed_references];
    simpl; destruct string_eq_dec; subst; trivial.
    inv_ctr. eauto using consistently_typed_references.
  Qed.

  Lemma ctr_mem_add_preservation : forall m t vT,
    valid_addresses m t ->
    consistently_typed_references m t ->
    consistently_typed_references (m +++ vT) t.
  Proof.
    intros. induction t; eauto using consistently_typed_references;
    inv_vad; inv_ctr; eauto using consistently_typed_references;
    (eapply ctr_refM || eapply ctr_refI); simpl_array; assumption.
  Qed.

  Lemma ctr_mem_set_preservation : forall m t ad v T,
    ad < #m ->
    empty |-- v is T ->
    empty |-- m[ad].tm is T ->
    (* --- *)
    consistently_typed_references m t ->
    consistently_typed_references m[ad <- (v, m[ad].typ)] t.
  Proof.
    intros. induction t;
    eauto using consistently_typed_references;
    inv_ctr; eauto using consistently_typed_references;
    match goal with _ : _[?ad].typ = _ |- _ => rename ad into ad' end;
    (eapply ctr_refM || eapply ctr_refI);
    decompose sum (lt_eq_lt_dec ad' ad); subst;
    simpl_array; trivial; apply_deterministic_typing; trivial.
  Qed.

  (* tstep ----------------------------------------------------------------- *)

  Lemma ctr_tstep_none_preservation : forall m t t',
    consistently_typed_references m t ->
    t --[EF_None]--> t' ->
    consistently_typed_references m t'.
  Proof.
    intros. induction_tstep; inv_ctr; eauto using consistently_typed_references.
    inv_ctr. eauto using ctr_subst_preservation.
  Qed.

  Local Lemma ctr_tstep_alloc_preservation : forall m t t' v T,
    valid_addresses m t ->
    well_typed_term t ->
    (* --- *)
    consistently_typed_references m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    consistently_typed_references (m +++ (v, T)) t'.
  Proof.
    intros * ? [T' ?] **. generalize dependent T'.
    induction_tstep; intros; inv_vad; inv_type; inv_ctr;
    eauto using consistently_typed_references, ctr_mem_add_preservation;
    (eapply ctr_refM || eapply ctr_refI); simpl_array; trivial.
  Qed.

  Local Lemma ctr_tstep_read_preservation : forall m t t' ad v,
    consistently_typed_references m v ->
    consistently_typed_references m t ->
    t --[EF_Read ad v]--> t' ->
    consistently_typed_references m t'.
  Proof.
    intros. induction_tstep; inv_ctr;
    eauto using consistently_typed_references.
  Qed.

  Local Lemma ctr_tstep_write_preservation : forall m t t' ad v T,
    well_typed_term t ->
    valid_addresses m t ->
    consistently_typed_references m t ->
    t --[EF_Write ad v T]--> t' ->
    consistently_typed_references m[ad <- (v, T)] t'.
  Proof.
    intros * [T' ?]. intros. assert (
      T = m[ad].typ /\
      exists Tv, empty |-- v is Tv /\ empty |-- m[ad].tm is Tv)
      as [? [? [? ?]]] by eauto using step_write_wtt.
    generalize dependent T'.
    induction_tstep; intros; inv_type; inv_vad; inv_ctr;
    eauto using valid_address_write,
      consistently_typed_references,
      ctr_mem_set_preservation.
  Qed.

  Lemma ctr_tstep_spawn_preservation : forall m t t' block,
    consistently_typed_references m t ->
    t --[EF_Spawn block]--> t' ->
    consistently_typed_references m t'.
  Proof.
    intros. induction_tstep; inv_ctr;
    eauto using consistently_typed_references.
  Qed.

  Local Corollary ctr_mstep_preservation : forall m m' t t' e,
    well_typed_term t ->
    valid_addresses m t ->
    forall_memory m (consistently_typed_references m) ->
    consistently_typed_references m t ->
    m / t ==[e]==> m' / t' ->
    consistently_typed_references m' t'.
  Proof.
    solve_mstep_preservation_using
      ctr_tstep_none_preservation
      ctr_tstep_alloc_preservation
      ctr_tstep_read_preservation
      ctr_tstep_write_preservation.
  Qed.

  (* ------------------------------------------------------------------------- *)

  Local Lemma ctr_thread_default_preservation : forall m,
    consistently_typed_references m thread_default.
  Proof.
    eauto using consistently_typed_references.
  Qed.

  Lemma ctr_spawn_block : forall m t t' block,
    consistently_typed_references m t ->
    t --[EF_Spawn block]--> t' ->
    consistently_typed_references m block.
  Proof.
    intros. induction_tstep; inv_ctr; eauto.
  Qed.

  Local Lemma ctr_untouched_threads_preservation : forall m m' ths tid tid' e t',
    forall_threads ths well_typed_term ->
    forall_threads ths (valid_addresses m) ->
    forall_threads ths (consistently_typed_references m) ->
    tid <> tid' ->
    tid' < #ths ->
    m / ths[tid] ==[e]==> m' / t' ->
    consistently_typed_references m' ths[tid'].
  Proof.
    intros *. intros Htype. intros. destruct (Htype tid).
    inv_mstep; eauto using ctr_mem_add_preservation.
    match goal with
    | _ : _ --[EF_Write _ _ ?T]--> _ |- _ =>
      assert (
        T = m[ad].typ /\
        exists V, empty |-- v is V /\ empty |-- m[ad].tm is V)
        as [Heq [? [? ?]]] by eauto using step_write_wtt
    end.
    rewrite Heq in *. eauto using ctr_mem_set_preservation.
  Qed.

  Corollary ctr_cstep_preservation : forall m m' ths ths' tid e,
    forall_threads ths well_typed_term ->
    forall_threads ths (valid_addresses m) ->
    forall_memory m (consistently_typed_references m) ->
    forall_threads ths (consistently_typed_references m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' (consistently_typed_references m').
  Proof.
    intros * Htype ?. destruct (Htype tid).
    eauto 6 using cstep_preservation,
      ctr_tstep_spawn_preservation,
      ctr_mstep_preservation,
      ctr_thread_default_preservation,
      ctr_spawn_block,
      ctr_untouched_threads_preservation.
  Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma wtt_alloc_value_generalization : forall t t' ad v T,
  well_typed_term t ->
  t --[EF_Alloc ad v T]--> t' ->
  well_typed_term v.
Proof.
  unfold well_typed_term. intros * [T' ?]. intros. generalize dependent T'.
  induction_tstep; intros; inv_type; eauto.
Qed.

Local Lemma ctr_alloc_value_generalization : forall m t t' ad v T,
  consistently_typed_references m t ->
  t --[EF_Alloc ad v T]--> t' ->
  consistently_typed_references m v.
Proof.
  intros. induction_tstep; intros; inv_ctr; eauto.
Qed.

Local Lemma ctr_write_value_generalization : forall m t t' ad v T,
  consistently_typed_references m t ->
  t --[EF_Write ad v T]--> t' ->
  consistently_typed_references m v.
Proof.
  intros. induction_tstep; intros; inv_ctr; eauto.
Qed.

Local Lemma ctr_tstep_alloc_mem_preservation : forall m t t' v T,
  well_typed_term t ->
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  (* --- *)
  consistently_typed_references m t ->
  forall_memory m (consistently_typed_references m) ->
  t --[EF_Alloc (#m) v T]--> t' ->
  forall_memory (m +++ (v, T)) (consistently_typed_references (m +++ (v, T))).
Proof.
  intros. intros ad.
  assert (well_typed_term v) as [? ?]
    by eauto using wtt_alloc_value_generalization.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
  eauto using consistently_typed_references; (* optimization *)
  eauto using ctr_mem_add_preservation, ctr_alloc_value_generalization.
Qed.

Local Lemma ctr_tstep_write_mem_preservation : forall m t t' ad v T,
  ad < # m ->
  well_typed_term t ->
  (* --- *)
  consistently_typed_references m t ->
  forall_memory m (consistently_typed_references m) ->
  t --[EF_Write ad v T]--> t' ->
  forall_memory m[ad <- (v, T)] (consistently_typed_references m[ad <- (v, T)]).
Proof.
  intros * ? [? ?]. intros. intros ad'.
  match goal with
  | _ : _ --[EF_Write _ _ ?T]--> _ |- _ =>
    assert (
      T = m[ad].typ /\
      exists V, empty |-- v is V /\ empty |-- m[ad].tm is V)
      as [? [? [? ?]]] by eauto using step_write_wtt
  end.
  decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array;
  eauto using ctr_write_value_generalization, ctr_mem_set_preservation.
Qed.

Local Corollary ctr_mstep_mem_preservation : forall m m' t t' e,
  well_typed_term t ->
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  (* --- *)
  consistently_typed_references m t ->
  forall_memory m (consistently_typed_references m) ->
  m / t ==[e]==> m' / t' ->
  forall_memory m' (consistently_typed_references m').
Proof.
  solve_mstep_mem_preservation_using 
    ctr_tstep_alloc_mem_preservation 
    ctr_tstep_write_mem_preservation.
Qed.

Local Corollary ctr_cstep_mem_preservation : forall m m' ths ths' tid e,
  forall_threads ths well_typed_term ->
  forall_threads ths (valid_addresses m) ->
  forall_memory m (valid_addresses m) ->
  (* --- *)
  forall_threads ths (consistently_typed_references m) ->
  forall_memory m (consistently_typed_references m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_memory m' (consistently_typed_references m').
Proof.
  solve_cstep_mem_preservation_using ctr_mstep_mem_preservation.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem consistently_typed_references_preservation : forall m m' ths ths' tid e,
  forall_program m ths well_typed_term ->
  forall_program m ths (valid_addresses m) ->
  (* --- *)
  forall_program m ths (consistently_typed_references m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_program m' ths' (consistently_typed_references m').
Proof.
  intros * [_ ?] [? ?] [? ?]. intros.
  eauto using ctr_cstep_preservation, ctr_cstep_mem_preservation.
Qed.

