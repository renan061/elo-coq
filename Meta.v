From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.

(* ------------------------------------------------------------------------- *)

Definition subst_preservation (P : mem -> tm -> Prop) :=
  forall m t tx x,
    P m t ->
    P m tx ->
    P m ([x := tx] t).

Definition mem_add_preservation (P : mem -> tm -> Prop) :=
  forall m t vT,
    P m t ->
    P (m +++ vT) t.

Definition mem_set_preservation (P : mem -> tm -> Prop) :=
  forall m t ad v T,
    P m v ->
    P m t ->
    P m[ad <- (v, T)] t.

(* ------------------------------------------------------------------------- *)

Definition thread_default_preservation (P : mem -> tm -> Prop) :=
  forall m,
    P m thread_default.

Definition spawn_block_preservation (P : mem -> tm -> Prop) :=
  forall m t t' block,
    P m t ->
    t --[EF_Spawn block]--> t' ->
    P m block.

(* The untouched threads with the new memory still preserve the property. *)
Definition untouched_threads_preservation (P : mem -> tm -> Prop) :=
  forall m m' ths tid tid' e t',
    forall_threads ths (P m) ->
    tid <> tid' ->
    tid' < #ths ->
    m / ths[tid] ==[e]==> m' / t' ->
    P m' ths[tid'].

(* ------------------------------------------------------------------------- *)

Definition tstep_none_preservation (P : mem -> tm -> Prop) :=
  forall m t t',
    P m t ->
    t --[EF_None]--> t' ->
    P m t'.

Definition tstep_alloc_preservation (P : mem -> tm -> Prop) :=
  forall m t t' v T,
    P m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    P (m +++ (v, T)) t'.

Definition tstep_read_preservation (P : mem -> tm -> Prop) :=
  forall m t t' ad v,
    P m v ->
    P m t ->
    t --[EF_Read ad v]--> t' ->
    P m t'.

Definition tstep_write_preservation (P : mem -> tm -> Prop) :=
  forall m t t' ad v T,
    P m t ->
    t --[EF_Write ad v T]--> t' ->
    P m[ad <- (v, T)] t'.

Definition tstep_spawn_preservation (P : mem -> tm -> Prop) :=
  forall m t t' block,
    P m t ->
    t --[EF_Spawn block]--> t' ->
    P m t'.

Definition mstep_preservation (P : mem -> tm -> Prop) :=
  forall m m' t t' e,
    forall_memory m (P m) ->
    P m t ->
    m / t ==[e]==> m' / t' ->
    P m' t'.

Definition cstep_preservation (P : mem -> tm -> Prop) :=
  forall m m' ths ths' tid e,
    forall_memory m (P m) ->
    forall_threads ths (P m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' (P m').

Definition property_preservation (P : mem -> tm -> Prop) :=
  forall m m' ths ths' tid e,
    forall_program m ths (P m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_program m' ths' (P m').

(* ------------------------------------------------------------------------- *)

Corollary mstep_preserves (P : mem -> tm -> Prop) :
  tstep_none_preservation P ->
  tstep_alloc_preservation P ->
  tstep_read_preservation P ->
  tstep_write_preservation P ->
  mstep_preservation P.
Proof. unfold mstep_preservation. intros. inversion_mstep; eauto. Qed.

Lemma cstep_preserves (P : mem -> tm -> Prop) :
    thread_default_preservation P ->
    spawn_block_preservation P ->
    untouched_threads_preservation P ->
    mstep_preservation P ->
    tstep_spawn_preservation P ->
    cstep_preservation P.
Proof.
  unfold cstep_preservation. intros. inversion_cstep; intros tid'.
  - destruct (nat_eq_dec tid' (#ths)); subst.
    + rewrite <- (set_preserves_length _ tid t'). simpl_array. eauto.
    + destruct (lt_eq_lt_dec tid' (length ths)) as [[Ha | ?] | Hb]; subst;
      try lia.
      * rewrite <- (set_preserves_length _ tid t') in Ha. simpl_array.
        destruct (nat_eq_dec tid tid'); subst; simpl_array; eauto.
      * rewrite <- (set_preserves_length _ tid t') in Hb. simpl_array. eauto.
  - destruct (nat_eq_dec tid tid'); subst; simpl_array;
    eauto using (mstep_preserves P).
    decompose sum (lt_eq_lt_dec tid' (#ths)); subst; eauto;
    simpl_array; eauto.
Qed.

#[export] Hint Resolve mstep_preserves cstep_preserves : preservation.

