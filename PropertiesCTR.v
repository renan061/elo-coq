From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Meta.

From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* consistently-typed-effects                                                *)
(* ------------------------------------------------------------------------- *)

Lemma consistently_typed_write_effect : forall m t t' ad v T,
  valid_addresses m t ->
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  t --[EF_Write ad v T]--> t' ->
  exists Tv, T = <{{&Tv}}>
          /\ empty |-- v is Tv
          /\ empty |-- m[ad].tm is Tv
          /\ m[ad].typ = <{{&Tv}}>.
Proof.
  intros * ? Hwtt **. inversion Hwtt as [T' ?].
  clear Hwtt. generalize dependent T'.
  induction_tstep; intros; inv_vad; inv_type; inv_ctr; eauto.
  inv_type. inv_ctr. eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

(* subst & mem ------------------------------------------------------------- *)

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
  (* --- *)
  consistently_typed_references m t ->
  consistently_typed_references (m +++ vT) t.
Proof.
  intros. induction t; eauto using consistently_typed_references;
  inv_vad; inv_ctr; eauto using consistently_typed_references;
  (eapply ctr_adM || eapply ctr_adI); simpl_array; assumption.
Qed.

Lemma ctr_mem_set_preservation : forall m t ad v T Tv,
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
  (eapply ctr_adM || eapply ctr_adI);
  match goal with H1 : _[?ad1].typ = _, H2 : _[?ad2].typ = _ |- _ =>
    destruct (nat_eq_dec ad1 ad2); subst;
    try (rewrite H1 in H2; inv H2)
  end;
  simpl_array; trivial.
Qed.

(* tstep ------------------------------------------------------------------- *)

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
  intros.
  assert (ad < #m) by eauto using vad_tstep_write_address_length.
  assert (exists Tv, T = <{{&Tv}}>
                  /\ empty |-- v is Tv
                  /\ empty |-- m[ad].tm is Tv
                  /\ m[ad].typ = <{{&Tv}}>)
    as [? [? [? [? ?]]]] by eauto using consistently_typed_write_effect.
  induction_tstep; intros; inv_vad; inv_wtt; inv_ctr;
  eauto using ctr_mem_set_preservation, consistently_typed_references.
Qed.

Lemma ctr_tstep_spawn_preservation : forall m t t' block,
  consistently_typed_references m t ->
  t --[EF_Spawn block]--> t' ->
  consistently_typed_references m t'.
Proof.
  intros. induction_tstep; inv_ctr;
  eauto using consistently_typed_references.
Qed.

(* mstep ------------------------------------------------------------------- *)

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

(* cstep ------------------------------------------------------------------- *)

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
  intros. inv_mstep; eauto using ctr_mem_add_preservation.
  assert (exists Tv, T = <{{&Tv}}>
                  /\ empty |-- v is Tv
                  /\ empty |-- m[ad].tm is Tv
                  /\ m[ad].typ = <{{&Tv}}>)
    as [? [? [? [? ?]]]] by eauto using consistently_typed_write_effect.
  subst. eauto using ctr_mem_set_preservation.
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
  intros. eapply cstep_preservation;
  eauto using ctr_tstep_spawn_preservation,
              ctr_mstep_preservation,
              ctr_thread_default,
              ctr_spawn_block,
              ctr_untouched_threads_preservation.
Qed.

(* tstep mem --------------------------------------------------------------- *)

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
  intros ** ad'.
  assert (ad < #m) by eauto using vad_tstep_write_address_length.
  assert (exists Tv, T = <{{&Tv}}>
                  /\ empty |-- v is Tv
                  /\ empty |-- m[ad].tm is Tv
                  /\ m[ad].typ = <{{&Tv}}>)
    as [? [? [? [? ?]]]] by eauto using consistently_typed_write_effect.
  subst. destruct (nat_eq_dec ad ad'); subst; simpl_array;
  eauto using ctr_mem_set_preservation, ctr_tstep_write_value.
Qed.

(* mstep mem --------------------------------------------------------------- *)

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

(* cstep mem --------------------------------------------------------------- *)

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

(* consistently-typed-references preservation ------------------------------ *)

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

