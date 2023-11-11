From Elo Require Import Core.
From Elo Require Import Meta.
From Elo Require Import Properties.
From Elo Require Import Lemmas.
From Elo Require Import Inheritance.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma preservation_subst P :
  forall m t tx x
    `{ConsMust (P m), InvMust P m},
    P m t ->
    P m tx ->
    P m ([x := tx] t).
Proof.
  intros. induction t; trivial; simpl; try solve [inv_must (P m); eauto_cons];
  destruct string_eq_dec; subst; trivial. inv_must (P m). eauto_cons.
Qed.

Local Lemma preservation_mem_add P :
  forall m t vT
    `{ConsUnit (P (m +++ vT)),
      ConsNum  (P (m +++ vT)),
      ConsVar  (P (m +++ vT)),
      ConsMust (P (m +++ vT)),
      InvMust P m},
    (forall ad T, P (m +++ vT) <{&ad :: T}>) ->
    P m t ->
    P (m +++ vT) t.
Proof.
  intros. induction t; trivial; try solve [inv_must (P m); eauto_cons];
  eauto using cons_unit, cons_num, cons_var.
Qed.

(* ------------------------------------------------------------------------- *)
(* valid-addresses                                                           *)
(* ------------------------------------------------------------------------- *)

Module vad_preservation.
  Local Lemma vad_mem_add : forall m t vT,
    valid_addresses m t ->
    valid_addresses (m +++ vT) t.
  Proof.
    intros. 
    eapply preservation_mem_add;
    eauto using ConsVAD, ConsVADUnit, ConsVADNum, ConsVADVar, InvVAD.
    intros. 
    -
  Qed.

  Local Lemma vad_mem_set : forall m t ad vT,
    valid_addresses m t ->
    valid_addresses m[ad <- vT] t.
  Proof.
    intros. induction t; eauto with vad; inv_vad; eauto with vad.
    intros ? ?. inv_hasad. rewrite set_preserves_length. assumption.
  Qed.

  (* tstep ----------------------------------------------------------------- *)

  Local Lemma vad_tstep_none_preservation : forall m t t',
    valid_addresses m t ->
    t --[EF_None]--> t' ->
    valid_addresses m t'.
  Proof.
    intros. induction_tstep; inv_vad; eauto with vad. 
    inv_vad. eauto using (preservation_subst valid_addresses), ConsVAD, InvVAD.
  Qed.

  Local Lemma vad_tstep_alloc_preservation : forall m t t' v T,
    valid_addresses m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    valid_addresses (m +++ (v, T)) t'.
  Proof.
    intros. induction_tstep; inv_vad;
    eauto using vad_mem_add with vad.
    intros ? ?. inv_hasad. rewrite add_increments_length. eauto.
  Qed.

  Local Lemma vad_tstep_read_preservation : forall m t t' ad v,
    valid_addresses m v ->
    valid_addresses m t ->
    t --[EF_Read ad v]--> t' ->
    valid_addresses m t'.
  Proof.
    intros. induction_tstep; inv_vad; eauto with vad.
  Qed.

  Local Lemma vad_tstep_write_preservation : forall m t t' ad v T,
    valid_addresses m t ->
    t --[EF_Write ad v T]--> t' ->
    valid_addresses m[ad <- (v, T)] t'.
  Proof.
    intros. induction_tstep; inv_vad; eauto using vad_mem_set with vad.
  Qed.

  Local Lemma vad_tstep_spawn_preservation : forall m t t' block,
    valid_addresses m t ->
    t --[EF_Spawn block]--> t' ->
    valid_addresses m t'.
  Proof.
    intros. induction_tstep; inv_vad; eauto with vad.
  Qed.

  (* mstep ----------------------------------------------------------------- *)

  Local Corollary vad_mstep_preservation : forall m m' t t' e,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    m / t ==[e]==> m' / t' ->
    valid_addresses m' t'.
  Proof.
    intros. inv_mstep;
    eauto using vad_tstep_none_preservation,
                vad_tstep_alloc_preservation,
                vad_tstep_read_preservation,
                vad_tstep_write_preservation.
  Qed.

  (* cstep ----------------------------------------------------------------- *)

  Local Lemma vad_thread_default : forall m,
    valid_addresses m thread_default.
  Proof.
    intros. eauto with vad.
  Qed.

  Local Lemma vad_spawn_block : forall m t t' block,
    valid_addresses m t ->
    t --[EF_Spawn block]--> t' ->
    valid_addresses m block.
  Proof.
    intros. induction_tstep; inv_vad; eauto.
  Qed.

  Local Lemma vad_untouched_preservation : forall m m' ths tid tid' t' e,
    forall_threads ths (valid_addresses m) ->
    tid <> tid' ->
    tid' < #ths ->
    m / ths[tid] ==[e]==> m' / t' ->
    valid_addresses m' ths[tid'].
  Proof.
    intros. inv_mstep; eauto using vad_mem_add, vad_mem_set.
  Qed.

  Local Corollary vad_cstep_preservation : forall m m' ths ths' tid e,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' (valid_addresses m').
  Proof.
    intros. eauto 6 using cstep_preservation,
      vad_tstep_spawn_preservation,
      vad_mstep_preservation,
      vad_thread_default,
      vad_spawn_block,
      vad_untouched_preservation.
  Qed.

  (* tstep mem ------------------------------------------------------------- *)

  Local Lemma vad_tstep_alloc_mem_preservation : forall m t t' v T,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    forall_memory  (m +++ (v, T)) (valid_addresses (m +++ (v, T))).
  Proof.
    assert (forall m t t' ad v T,
      valid_addresses m t ->
      t --[EF_Alloc ad v T]--> t' ->
      valid_addresses m v)
        by (intros; induction_tstep; inv_vad; eauto).
    (* main proof *)
    intros ** ad.
    decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
    eauto using vad_mem_add with vad.
  Qed.

  Local Lemma vad_tstep_write_mem_preservation : forall m t t' ad v T,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    t --[EF_Write ad v T]--> t' ->
    forall_memory m[ad <- (v, T)] (valid_addresses m[ad <- (v, T)]).
  Proof.
    assert (forall m t t' ad v T,
      valid_addresses m t ->
      t --[EF_Write ad v T]--> t' ->
      valid_addresses m v)
        by (intros; induction_tstep; inv_vad; eauto).
    (* main proof *)
    intros ** ad'.
    assert (ad < #m) by eauto using vad_tstep_write_address_length.
    destruct (nat_eq_dec ad ad'); subst; simpl_array;
    eauto using vad_mem_set.
  Qed.

  (* mstep mem ------------------------------------------------------------- *)

  Corollary vad_mstep_mem_preservation : forall m m' t t' e,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    m / t ==[e]==> m' / t' ->
    forall_memory m' (valid_addresses m').
  Proof.
    intros. inv_mstep;
    eauto using vad_tstep_alloc_mem_preservation,
                vad_tstep_write_mem_preservation.
  Qed.

  (* cstep mem ------------------------------------------------------------- *)

  Local Corollary vad_cstep_mem_preservation : forall m m' ths ths' tid e,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_memory m' (valid_addresses m').
  Proof.
    intros. inv_cstep; eauto using vad_mstep_mem_preservation.
  Qed.

  (* valid-addresses preservation ------------------------------------------ *)

  Theorem vad_preservation : forall m m' ths ths' tid e,
    forall_program m ths (valid_addresses m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_program m' ths' (valid_addresses m').
  Proof.
    intros * [? ?] **.
    eauto using vad_cstep_preservation, vad_cstep_mem_preservation.
  Qed.
End vad_preservation.

(* ------------------------------------------------------------------------- *)
(* consistently-typed-references                                             *)
(* ------------------------------------------------------------------------- *)

Module ctr_preservation.
  Local Lemma ctr_subst : forall m t tx x,
    consistently_typed_references m t ->
    consistently_typed_references m tx ->
    consistently_typed_references m ([x := tx] t).
  Proof.
    intros. induction t; trivial;
    try solve [inv_ctr; eauto using consistently_typed_references];
    simpl; destruct string_eq_dec; subst; trivial.
    inv_ctr. eauto using consistently_typed_references.
  Qed.

  Local Lemma ctr_mem_add : forall m t vT,
    valid_addresses m t ->
    (* --- *)
    consistently_typed_references m t ->
    consistently_typed_references (m +++ vT) t.
  Proof.
    intros. induction t; eauto using consistently_typed_references;
    inv_vad; inv_ctr; eauto using consistently_typed_references.
    - clear H4.
    clear H4.
    (eapply ctr_refM || eapply ctr_refI); simpl_array; assumption.
  Qed.

  Local Lemma ctr_mem_set : forall m t ad v T Tv,
    ad < #m ->
    empty |-- v is Tv ->
    m[ad].typ = T ->
    m[ad].typ = <{{&Tv}}> ->
    (* --- *)
    consistently_typed_references m t ->
    consistently_typed_references m[ad <- (v, T)] t.
  Proof.
    intros. induction t; eauto using consistently_typed_references;
    inv_ctr; eauto using consistently_typed_references;
    (eapply ctr_refM || eapply ctr_refI);
    match goal with H1 : _[?ad1].typ = _, H2 : _[?ad2].typ = _ |- _ =>
      destruct (nat_eq_dec ad1 ad2); subst;
      try (rewrite H1 in H2; inv H2)
    end;
    simpl_array; trivial.
  Qed.

  (* tstep ----------------------------------------------------------------- *)

  Local Lemma ctr_tstep_none_preservation : forall m t t',
    consistently_typed_references m t ->
    t --[EF_None]--> t' ->
    consistently_typed_references m t'.
  Proof.
    intros. induction_tstep; inv_ctr; eauto using consistently_typed_references.
    inv_ctr. eauto using ctr_subst.
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
    eauto using consistently_typed_references, ctr_mem_add;
    (eapply ctr_refM || eapply ctr_refI); simpl_array; trivial.
  Qed.

  Local Lemma ctr_tstep_read_preservation : forall m t t' ad v,
    consistently_typed_references m v ->
    (* --- *)
    consistently_typed_references m t ->
    t --[EF_Read ad v]--> t' ->
    consistently_typed_references m t'.
  Proof.
    intros. induction_tstep; inv_ctr; eauto using consistently_typed_references.
  Qed.

  Local Lemma ctr_tstep_write_preservation : forall m t t' ad v T,
    valid_addresses m t ->
    well_typed_term t ->
    (* --- *)
    consistently_typed_references m t ->
    t --[EF_Write ad v T]--> t' ->
    consistently_typed_references m[ad <- (v, T)] t'.
  Proof.
    intros.
    assert (ad < #m) by eauto using vad_tstep_write_address_length.
    assert (exists Tv, T = <{{&Tv}}>
                    /\ empty |-- v is Tv
                    /\ empty |-- m[ad].tm is Tv
                    /\ m[ad].typ = <{{&Tv}}>)
      as [? [? [? [? ?]]]] by eauto using consistently_typed_write_effect.
    induction_tstep; intros; inv_vad; inv_wtt; inv_ctr;
    eauto using ctr_mem_set, consistently_typed_references.
  Qed.

  Local Lemma ctr_tstep_spawn_preservation : forall m t t' block,
    consistently_typed_references m t ->
    t --[EF_Spawn block]--> t' ->
    consistently_typed_references m t'.
  Proof.
    intros. induction_tstep; inv_ctr;
    eauto using consistently_typed_references.
  Qed.

  (* mstep ----------------------------------------------------------------- *)

  Local Corollary ctr_mstep_preservation : forall m m' t t' e,
    forall_memory m (consistently_typed_references m) ->
    valid_addresses m t ->
    well_typed_term t ->
    (* --- *)
    consistently_typed_references m t ->
    m / t ==[e]==> m' / t' ->
    consistently_typed_references m' t'.
  Proof.
    intros. inv_mstep;
    eauto using ctr_tstep_none_preservation,
                ctr_tstep_alloc_preservation,
                ctr_tstep_read_preservation,
                ctr_tstep_write_preservation.
  Qed.

  (* cstep ----------------------------------------------------------------- *)

  Local Lemma ctr_thread_default : forall m,
    consistently_typed_references m thread_default.
  Proof.
    eauto using consistently_typed_references.
  Qed.

  Local Lemma ctr_spawn_block : forall m t t' block,
    consistently_typed_references m t ->
    t --[EF_Spawn block]--> t' ->
    consistently_typed_references m block.
  Proof.
    intros. induction_tstep; inv_ctr; eauto.
  Qed.

  Local Lemma ctr_untouched_preservation : forall m m' ths tid tid' t' e,
    forall_threads ths (valid_addresses m) ->
    forall_threads ths well_typed_term ->
    forall_threads ths (consistently_typed_references m) ->
    (* --- *)
    tid <> tid' ->
    tid' < #ths ->
    m / ths[tid] ==[e]==> m' / t' ->
    consistently_typed_references m' ths[tid'].
  Proof.
    intros. inv_mstep; eauto using ctr_mem_add.
    assert (exists Tv, T = <{{&Tv}}>
                    /\ empty |-- v is Tv
                    /\ empty |-- m[ad].tm is Tv
                    /\ m[ad].typ = <{{&Tv}}>)
      as [? [? [? [? ?]]]] by eauto using consistently_typed_write_effect.
    subst. eauto using ctr_mem_set.
  Qed.

  Local Corollary ctr_cstep_preservation : forall m m' ths ths' tid e,
    forall_threads ths (valid_addresses m) ->
    forall_threads ths well_typed_term ->
    (* --- *)
    forall_memory m (consistently_typed_references m) ->
    forall_threads ths (consistently_typed_references m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' (consistently_typed_references m').
  Proof.
    intros. eapply cstep_preservation.
    (* split for performance *)
    eauto using ctr_tstep_spawn_preservation.
    eauto using ctr_mstep_preservation.
    eauto using ctr_thread_default.
    eauto using ctr_spawn_block.
    eauto using ctr_untouched_preservation.
    assumption.
    assumption.
    eauto.
  Qed.

  (* tstep mem ------------------------------------------------------------- *)

  Local Lemma ctr_tstep_alloc_mem_preservation : forall m t t' v T,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    well_typed_term t ->
    (* --- *)
    forall_memory m (consistently_typed_references m) ->
    consistently_typed_references m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    forall_memory (m +++ (v, T)) (consistently_typed_references (m +++ (v, T))).
  Proof.
    intros ** ad.
    decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
    eauto using consistently_typed_references; (* optimization *)
    eauto using ctr_mem_add, ctr_tstep_alloc_value.
  Qed.

  Local Lemma ctr_tstep_write_mem_preservation : forall m t t' ad v T,
   valid_addresses m t ->
   well_typed_term t ->
   (* --- *)
   forall_memory m (consistently_typed_references m) ->
   consistently_typed_references m t ->
   t --[EF_Write ad v T]--> t' ->
   forall_memory m[ad <- (v, T)] (consistently_typed_references m[ad <- (v, T)])
   .
  Proof.
    intros ** ad'.
    assert (ad < #m) by eauto using vad_tstep_write_address_length.
    assert (exists Tv, T = <{{&Tv}}>
                    /\ empty |-- v is Tv
                    /\ empty |-- m[ad].tm is Tv
                    /\ m[ad].typ = <{{&Tv}}>)
      as [? [? [? [? ?]]]] by eauto using consistently_typed_write_effect.
    subst. destruct (nat_eq_dec ad ad'); subst; simpl_array;
    eauto using ctr_mem_set, ctr_tstep_write_value.
  Qed.

  (* mstep mem ------------------------------------------------------------- *)

  Local Corollary ctr_mstep_mem_preservation : forall m m' t t' e,
    well_typed_term t ->
    valid_addresses m t ->
    forall_memory m (valid_addresses m) ->
    (* --- *)
    forall_memory m (consistently_typed_references m) ->
    consistently_typed_references m t ->
    m / t ==[e]==> m' / t' ->
    forall_memory m' (consistently_typed_references m').
  Proof.
    intros. inv_mstep;
    eauto using ctr_tstep_alloc_mem_preservation,
                ctr_tstep_write_mem_preservation.
  Qed.

  (* cstep mem ------------------------------------------------------------- *)

  Local Corollary ctr_cstep_mem_preservation : forall m m' ths ths' tid e,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    forall_threads ths well_typed_term ->
    (* --- *)
    forall_memory m (consistently_typed_references m) ->
    forall_threads ths (consistently_typed_references m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_memory m' (consistently_typed_references m').
  Proof.
    intros. inv_cstep; eauto using ctr_mstep_mem_preservation.
  Qed.

  (* consistently-typed-references preservation ---------------------------- *)

  Theorem ctr_preservation : forall m m' ths ths' tid e,
    forall_program m ths (valid_addresses m) ->
    forall_program m ths well_typed_term ->
    (* --- *)
    forall_program m ths (consistently_typed_references m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_program m' ths' (consistently_typed_references m').
  Proof.
    intros * [? ?] [_ ?] [? ?]. intros.
    eauto using ctr_cstep_preservation, ctr_cstep_mem_preservation.
  Qed.
End ctr_preservation.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Module nacc_preservation.
  Local Lemma nacc_subst : forall m t tx ad x,
    ~ access ad m t ->
    ~ access ad m tx ->
    ~ access ad m ([x := tx] t).
  Proof.
    intros. induction t; simpl; eauto using access;
    try inv_nacc; eauto with acc;
    destruct string_eq_dec; subst; eauto with acc.
  Qed.

  Local Lemma nacc_mem_add : forall m t ad vT,
    ~ access (#m) m t ->
    (* --- *)
    ~ access ad m t ->
    ~ access ad (m +++ vT) t.
  Proof.
    intros ** Hacc. induction Hacc; inv_nacc; inv_nacc; eauto.
    decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; eauto.
  Qed.

  Local Lemma nacc_mem_set : forall m t ad ad' v T,
    ~ access ad m v ->
    ~ access ad m t ->
    ~ access ad m[ad' <- (v, T)] t.
  Proof.
    assert (forall m ad ad' v,
      access ad m[ad' <- v] m[ad' <- v][ad'].tm -> ad' < #m). {
        intros * H. decompose sum (lt_eq_lt_dec ad' (#m)); subst; trivial;
        simpl_array; simpl in *; inv_acc.
    }
    (* main proof *)
    intros ** Hacc. induction Hacc; eauto using access.
    match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
    destruct (nat_eq_dec ad' ad''); subst;
    try (assert (ad'' < #m) by eauto);
    simpl_array; eauto using access.
  Qed.

  Local Lemma alt_nacc_mem_set : forall m t ad ad' vT,
    ~ access ad' m t ->
    (* --- *)
    ~ access ad m t ->
    ~ access ad m[ad' <- vT] t.
  Proof.
    intros ** Hacc.
    induction Hacc; inv_nacc; inv_nacc; eauto using access.
    simpl_array. eauto.
  Qed.

  (* tstep ----------------------------------------------------------------- *)

  Local Lemma nacc_tstep_none_preservation : forall m t t' ad,
    ~ access ad m t ->
    t --[EF_None]--> t' ->
    ~ access ad m t'.
  Proof.
    intros. induction_tstep; inv_nacc; eauto with acc.
    inv_nacc. eauto using nacc_subst.
  Qed.

  Local Lemma nacc_tstep_alloc_preservation : forall m t t' ad v T,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    (* --- *)
    ad < #m ->
    ~ access ad m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    ~ access ad (m +++ (v, T)) t'.
  Proof.
    intros. induction_tstep; inv_vad; inv_nacc;
    eauto using nacc_mem_add, nacc_vad_length with acc.
    eapply nacc_ref.
    - intros ?. subst. eauto.
    - simpl_array. eauto using nacc_mem_add, nacc_vad_length.
  Qed.

  Local Lemma nacc_tstep_read_preservation : forall m t t' ad ad',
    ~ access ad m t ->
    t --[EF_Read ad' m[ad'].tm]--> t' ->
    ~ access ad m t'.
  Proof.
    intros. induction_tstep; inv_nacc; eauto with acc. inv_nacc. assumption.
  Qed.

  Local Lemma nacc_tstep_write_preservation : forall m t t' ad ad' v T,
    ~ access ad m t ->
    t --[EF_Write ad' v T]--> t' ->
    ~ access ad m[ad' <- (v, T)] t'.
  Proof.
    intros.
    assert (~ access ad m v) by eauto using nacc_tstep_write_value.
    induction_tstep; inv_nacc; eauto using nacc_mem_set with acc.
  Qed.

  Local Lemma nacc_tstep_spawn_preservation : forall m t t' block ad,
    ~ access ad m t ->
    t --[EF_Spawn block]--> t' ->
    ~ access ad m t'.
  Proof.
    intros. induction_tstep; eauto with acc; inv_nacc; eauto with acc.
  Qed.

  (* mstep ----------------------------------------------------------------- *)

  Local Corollary nacc_mstep_preservation : forall m m' t t' ad e,
    forall_memory m (valid_addresses m) ->
    valid_addresses m t ->
    (* --- *)
    ad < #m ->
    ~ access ad m t ->
    m / t ==[e]==> m' / t' ->
    ~ access ad m' t'.
  Proof.
    intros. inv_mstep;
    eauto using nacc_tstep_none_preservation,
                nacc_tstep_alloc_preservation,
                nacc_tstep_read_preservation,
                nacc_tstep_write_preservation.
  Qed.

  (* cstep ----------------------------------------------------------------- *)

  Local Lemma uacc_tstep_write_requirement : forall m t t' ad v T,
    well_typed_term t ->
    t --[EF_Write ad v T]--> t' ->
    unsafe_access ad m t.
  Proof.
    intros * [T' ?] **. generalize dependent T'.
    induction_tstep; intros; inv_type; eauto using unsafe_access.
    inv_type. eauto using unsafe_access.
  Qed.

  Local Lemma nacc_untouched_preservation : forall m m' ths tid tid' t' ad e,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    forall_threads ths well_typed_term ->
    safe_memory_sharing m ths ->
    (* --- *)
    tid <> tid' ->
    tid' < #ths ->
    ~ access ad m ths[tid'] ->
    m / ths[tid] ==[e]==> m' / t' ->
    ~ access ad m' ths[tid'].
  Proof.
    intros * ? ? ? Hsms **. rename ad into ad'. invc_mstep;
    eauto using nacc_mem_add, nacc_vad_length.
    eapply alt_nacc_mem_set; eauto.
    assert (unsafe_access ad m ths[tid])
      by eauto using uacc_tstep_write_requirement.
    intros ?. eapply (Hsms tid tid'); eauto.
  Qed.

  (* not-access preservation ----------------------------------------------- *)

  Theorem nacc_preservation : forall m m' ths ths' tid tid' ad e,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    forall_threads ths well_typed_term ->
    safe_memory_sharing m ths ->
    (* --- *)
    ad < #m ->
    tid < #ths ->
    ~ access ad m ths[tid] ->
    m / ths ~~[tid', e]~~> m' / ths' ->
    ~ access ad m' ths'[tid].
  Proof.
    intros. invc_cstep; destruct (nat_eq_dec tid tid'); subst; simpl_array;
    (* split for performance *)
    eauto using nacc_tstep_spawn_preservation.
    eauto using nacc_mstep_preservation.
    eauto using nacc_untouched_preservation.
  Qed.
End nacc_preservation.

(* ------------------------------------------------------------------------- *)
(* not-unsafe-access                                                         *)
(* ------------------------------------------------------------------------- *)

Module nuacc_preservation.
  Local Lemma nuacc_subst : forall m t tx ad x,
    ~ unsafe_access ad m t ->
    ~ unsafe_access ad m tx ->
    ~ unsafe_access ad m ([x := tx] t).
  Proof.
    intros ** ?. induction t; eauto; simpl in *;
    try (destruct string_eq_dec); eauto; inv_uacc; inv_nuacc; eauto.
  Qed.

  Local Lemma nuacc_mem_add : forall m t ad vT,
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

  Local Lemma alt_nuacc_mem_set_preservation : forall m t ad ad' vT,
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
    contradict Huacc. eauto using nuacc_subst.
  Qed.

  Local Lemma nuacc_tstep_alloc_preservation : forall m t t' ad v T,
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

  Local Lemma nuacc_tstep_read_preservation : forall m t t' ad ad',
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

  Local Lemma nuacc_tstep_write_preservation : forall m t t' ad ad' v T,
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

  Local Lemma nuacc_tstep_spawn_preservation : forall m t t' ad block,
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

  (* cstep ----------------------------------------------------------------- *)

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
      by eauto using uacc_tstep_write_requirement.
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

(* ------------------------------------------------------------------------- *)
(* safe-spawns                                                               *)
(* ------------------------------------------------------------------------- *)

Module ss_preservation.
  Local Lemma nomut_subst : forall x t t',
    no_mut t ->
    no_mut t' ->
    no_mut ([x := t'] t).
  Proof.
    intros. induction t; eauto; simpl;
    try destruct string_eq_dec; subst; try assumption;
    inv_nomut; eauto using no_mut.
  Qed.

  Local Lemma hasvar_subst : forall x t tx,
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

  Local Lemma ss_subst : forall Gamma x t v T Tx,
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
    eauto using simple_cstep_preservation,
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
    intros ** tid1 tid2 **. destruct_sms ths tid tid1 tid2; simpl_array;
    eauto using acc_tstep_none_inheritance,
                nuacc_preservation.nuacc_tstep_none_preservation.
  Qed.

  Local Lemma sms_tstep_alloc_preservation : forall m t v ths tid T,
    forall_memory m (valid_addresses m) ->
    forall_threads ths (valid_addresses m) ->
    (* --- *)
    safe_memory_sharing m ths ->
    ths[tid] --[EF_Alloc (#m) v T]--> t ->
    safe_memory_sharing (m +++ (v, T)) ths[tid <- t].
  Proof.
    intros ** tid1 tid2 ** Huacc.
    assert (Hvac : forall_threads ths (valid_accesses m))
      by (intros ?; eauto using vad_then_vac).
    assert (forall tid, ~ unsafe_access (#m) m ths[tid])
      by eauto using nuacc_vad_length.
    autounfold with vac in Hvac.
    eapply uacc_then_acc in Huacc as ?. contradict Huacc.
    destruct_sms ths tid tid1 tid2; simpl_array;
    eauto 6 using nuacc_tstep_alloc_preservation,
                  acc_tstep_alloc_inheritance,
                  nuacc_mem_add_preservation,
                  acc_mem_add_inheritance.
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
    safe_memory_sharing m ths ->
    ths[tid] --[EF_Spawn block]--> t ->
    safe_memory_sharing m (ths[tid <- t] +++ block).
  Proof.
    intros ** tid1 tid2 **.
    assert (~ unsafe_access ad m block) by eauto using nuacc_spawn_block.
    assert (consistently_typed_references m block) by eauto using ctr_spawn_block.
    destruct_sms ths tid tid1 tid2;
    decompose sum (lt_eq_lt_dec tid1 (#ths)); subst; simpl_array;
    decompose sum (lt_eq_lt_dec tid2 (#ths)); subst; simpl_array;
    try solve [inv_step | inv_acc | intros ?; inv_uacc];
    eauto using uacc_by_association,
      nuacc_tstep_spawn_preservation,
      acc_tstep_spawn_inheritance.
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
    intros * ? [? ?] [_ ?] [? ?] [_ ?] **.
    invc_cstep; eauto using sms_tstep_spawn_preservation, sms_mstep_preservation.
  Qed.
End sms_preservation.
