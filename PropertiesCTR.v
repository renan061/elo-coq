From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Meta.

From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* misc. properties                                                          *)
(* ------------------------------------------------------------------------- *)

Inductive consistently_typed_effect (m : mem) : effect -> Prop :=
  | cte_none :
    consistently_typed_effect m EF_None

  | cte_alloc : forall ad v T,
    consistently_typed_effect m (EF_Alloc ad v T)

  | cte_read : forall ad v,
    consistently_typed_effect m (EF_Read ad v)

  | cte_write : forall ad v T,
    ad < #m ->
    empty |-- v is T ->
    empty |-- m[ad].tm is T ->
    m[ad].typ = <{{&T}}> ->
    consistently_typed_effect m (EF_Write ad v <{{&T}}>)

  | cte_spawn : forall t,
    consistently_typed_effect m (EF_Spawn t)
  .

Lemma cte_tstep_write_T : forall m t t' ad v T Tv,
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  empty |-- v is Tv ->
  t --[EF_Write ad v T]--> t' ->
  T = <{{&Tv}}>.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  induction_tstep; intros; inv_type; inv_ctr; eauto.
  inv_type. inv_ctr. apply_deterministic_typing. eauto.
Qed.

Lemma cte_tstep_preservation : forall m t t' e,
  valid_addresses m t ->
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  t --[e]--> t' ->
  exists m', consistently_typed_effect m' e.
Proof.
  intros. destruct e;
  try solve [exists m; eauto using consistently_typed_effect].
  assert (ad < #m) by eauto using vad_tstep_write_address_length.
  assert (well_typed_term v) as [Tv ?] by eauto using wtt_tstep_write_value.
  assert (T = <{{&Tv}}>) by eauto using cte_tstep_write_T. subst.
  exists (m[ad <- (v, <{{&Tv}}>)]).
  eapply cte_write; eauto; try solve [simpl_array; trivial].
  rewrite set_preserves_length. assumption.
Qed.

Lemma cte_tstep_write : forall m t t' ad v T,
  valid_addresses m t ->
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  t --[EF_Write ad v T]--> t' ->
  consistently_typed_effect m[ad <- (v, T)] (EF_Write ad v T).
Proof.
  intros.
  assert (ad < #m) by eauto using vad_tstep_write_address_length.
  assert (well_typed_term v) as [Tv ?] by eauto using wtt_tstep_write_value.
  assert (T = <{{&Tv}}>) by eauto using cte_tstep_write_T. subst.
  eapply cte_write; eauto; try solve [simpl_array; trivial].
  rewrite set_preserves_length. assumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

(*
Lemma ctr_tstep_write_consistent_memval : forall m t t' ad v T Tv,
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  empty |-- v is Tv ->
  t --[EF_Write ad v T]--> t' ->
  empty |-- m[ad].tm is Tv.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  induction_tstep; intros; inv_type; inv_ctr; eauto.
  inv_type. inv_ctr. apply_deterministic_typing. assumption.
Qed.

Lemma ctr_tstep_write_consistent_memtyp_v : forall m t t' ad v T Tv,
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  empty |-- v is Tv ->
  t --[EF_Write ad v T]--> t' ->
  m[ad].typ = <{{&Tv}}>.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  induction_tstep; intros; inv_type; inv_ctr; eauto.
  inv_type. inv_ctr. apply_deterministic_typing. assumption.
Qed.

Lemma ctr_tstep_write_consistent_memtyp_T : forall m t t' ad v T,
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  t --[EF_Write ad v T]--> t' ->
  m[ad].typ = T.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  induction_tstep; intros; inv_type; inv_ctr; eauto.
  inv_type. inv_ctr. assumption.
Qed.

Corollary ctr_tstep_write_consistently_typed_effect : forall m t t' ad v T Tv,
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  empty |-- v is Tv ->
  t --[EF_Write ad v T]--> t' ->
  T = <{{&Tv}}>.
Proof.
  intros. symmetry.
  erewrite <- ctr_tstep_write_consistent_memtyp_T; eauto.
  erewrite ctr_tstep_write_consistent_memtyp_v; eauto.
Qed.
*)

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Module Preservation.

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
    (eapply ctr_adM || eapply ctr_adI); simpl_array; assumption.
  Qed.

  Lemma ctr_mem_set_preservation : forall m t ad v T,
    ad < #m ->
    empty |-- v is T ->
    empty |-- m[ad].tm is T ->
    (* --- *)
    consistently_typed_references m t ->
    consistently_typed_references m[ad <- (v, m[ad].typ)] t.
  Proof.
    intros. induction t; eauto using consistently_typed_references;
    inv_ctr; eauto using consistently_typed_references;
    match goal with _ : _[?ad].typ = _ |- _ => rename ad into ad' end;
    (eapply ctr_adM || eapply ctr_adI);
    decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array;
    trivial; apply_deterministic_typing; trivial.
  Qed.

  Lemma ctr_mem_set_preservation2 : forall m t ad v T Tv,
    ad < #m ->
    empty |-- v is Tv ->
    empty |-- m[ad].tm is Tv ->
    T = m[ad].typ ->
    (* --- *)
    consistently_typed_references m t ->
    consistently_typed_references m[ad <- (v, T)] t.
  Proof.
    intros. induction t; eauto using consistently_typed_references;
    inv_ctr; eauto using consistently_typed_references;
    (eapply ctr_adM || eapply ctr_adI);
    destruct (nat_eq_dec ad n); subst; simpl_array; trivial;
    apply_deterministic_typing; trivial.
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

  Lemma ctr_tstep_alloc_preservation : forall m t t' v T,
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
    (eapply ctr_adM || eapply ctr_adI); simpl_array; trivial.
  Qed.

  Lemma ctr_tstep_read_preservation : forall m t t' ad v,
    consistently_typed_references m v ->
    (* --- *)
    consistently_typed_references m t ->
    t --[EF_Read ad v]--> t' ->
    consistently_typed_references m t'.
  Proof.
    intros. induction_tstep; inv_ctr;
    eauto using consistently_typed_references.
  Qed.

  Lemma ctr_tstep_write_preservation : forall m t t' ad v T,
    valid_addresses m t ->
    well_typed_term t ->
    (* --- *)
    consistently_typed_references m t ->
    t --[EF_Write ad v T]--> t' ->
    consistently_typed_references m[ad <- (v, T)] t'.
  Proof.
    intros * ? Hwtt **. inversion Hwtt as [T' ?]. generalize dependent T'.
    induction_tstep; intros; inv_vad; inv_wtt; inv_ctr;
    eauto using consistently_typed_references.
    - eapply 

      assert (exists m', consistently_typed_effect m' (EF_Write ad v T))
        as [? ?] by eauto using cte_tstep_preservation.





    (*
    assert (
      T = m[ad].typ /\ exists Tv, empty |-- v is Tv /\ empty |-- m[ad].tm is Tv)
      as [? [? [? ?]]] by admit.
    *)
    generalize dependent T'.
    induction_tstep; intros; inv_vad; inv_type; inv_ctr;
    eauto using ctr_mem_set_preservation,
      vad_tstep_write_address_length,
      consistently_typed_references.
    - eapply ctr_asg.
      + eapply IHtstep; eauto.
      + eapply ctr_mem_set_preservation2; eauto;
        eauto using vad_tstep_write_address_length.
        eauto uding
  Qed.

  Lemma ctr_tstep_spawn_preservation : forall m t t' block,
    consistently_typed_references m t ->
    t --[EF_Spawn block]--> t' ->
    consistently_typed_references m t'.
  Proof.
    intros. induction_tstep; inv_ctr;
    eauto using consistently_typed_references.
  Qed.

  (* mstep ----------------------------------------------------------------- *)

  Corollary ctr_mstep_preservation : forall m m' t t' e,
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

  Lemma ctr_thread_default : forall m,
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

  Lemma ctr_untouched_threads_preservation : forall m m' ths tid tid' t' e,
    forall_threads ths (valid_addresses m) ->
    forall_threads ths well_typed_term ->
    forall_threads ths (consistently_typed_references m) ->
    (* --- *)
    tid <> tid' ->
    tid' < #ths ->
    m / ths[tid] ==[e]==> m' / t' ->
    consistently_typed_references m' ths[tid'].
  Proof.
    intros * ? Htype **. destruct (Htype tid).
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
    forall_threads ths (valid_addresses m) ->
    forall_threads ths well_typed_term ->
    (* --- *)
    forall_memory m (consistently_typed_references m) ->
    forall_threads ths (consistently_typed_references m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' (consistently_typed_references m').
  Proof.
    intros * ? Htype **. destruct (Htype tid).
    eapply cstep_preservation;
    eauto using ctr_tstep_spawn_preservation,
                ctr_mstep_preservation,
                ctr_thread_default,
                ctr_spawn_block,
                ctr_untouched_threads_preservation.
  Qed.

  (* tstep mem ------------------------------------------------------------- *)

  Lemma ctr_tstep_alloc_mem_preservation : forall m t t' v T,
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
    assert (well_typed_term v) as [? ?] by eauto using wtt_tstep_alloc_value.
    decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
    eauto using consistently_typed_references; (* optimization *)
    eauto using ctr_mem_add_preservation, ctr_tstep_alloc_value.
  Qed.

  Lemma ctr_tstep_write_mem_preservation : forall m t t' ad v T,
   valid_addresses m t ->
   well_typed_term t ->
   (* --- *)
   forall_memory m (consistently_typed_references m) ->
   consistently_typed_references m t ->
   t --[EF_Write ad v T]--> t' ->
   forall_memory m[ad <- (v, T)] (consistently_typed_references m[ad <- (v, T)])
   .
  Proof.
    intros * ? [? ?] **. intros ad'.
    assert (ad < #m) by eauto using vad_tstep_write_address_length.
    match goal with
    | _ : _ --[EF_Write _ _ ?T]--> _ |- _ =>
      assert (
        T = m[ad].typ /\
        exists V, empty |-- v is V /\ empty |-- m[ad].tm is V)
        as [? [? [? ?]]] by eauto using step_write_wtt
    end.
    decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array;
    eauto using ctr_mem_set_preservation, ctr_tstep_write_value.
  Qed.

  (* mstep mem ------------------------------------------------------------- *)

  Corollary ctr_mstep_mem_preservation : forall m m' t t' e,
    well_typed_term t ->
    valid_addresses m t ->
    forall_memory m (valid_addresses m) ->
    (* --- *)
    forall_memory m (consistently_typed_references m) ->
    consistently_typed_references m t ->
    m / t ==[e]==> m' / t' ->
    forall_memory m' (consistently_typed_references m').
  Proof.
    intros. inv_mstep; eauto using ctr_tstep_alloc_mem_preservation,
                                   ctr_tstep_write_mem_preservation.
  Qed.

  (* cstep mem ------------------------------------------------------------- *)

  Corollary ctr_cstep_mem_preservation : forall m m' ths ths' tid e,
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

  Theorem consistently_typed_references_preservation :
    forall m m' ths ths' tid e,
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

End Preservation.

