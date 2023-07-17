From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.

(* ----------------------------------------------------------------------------

(* Used by tstep_none_preservation *)
subst_preservation:
  forall m t tx x,
    P m t ->
    P m tx ->
    P m ([x := tx] t).

(* Used by tstep_alloc_preservation *)
mem_add_preservation:
  forall m t vT,
    P m t ->
    P (m +++ vT) t.

(* Used by tstep_write_preservation *)
mem_set_preservation:
  forall m t ad vT,
    P m t ->
    P m[ad <- vT] t.

-------------------------------------------------------------------------------

tstep_none_preservation:
  forall m t t',
    P m t ->
    t --[EF_None]--> t' ->
    P m t'.

tstep_alloc_preservation:
  forall m t t' v T,
    P m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    P (m +++ (v, T)) t'.

tstep_read_preservation:
  forall m t t' ad v,
    P m v ->
    P m t ->
    t --[EF_Read ad v]--> t' ->
    P m t'.

tstep_write_preservation:
  forall m t t' ad v T,
    P m t ->
    t --[EF_Write ad v T]--> t' ->
    P m[ad <- (v, T)] t'.

tstep_spawn_preservation:
  forall m t t' block,
    P m t ->
    t --[EF_Spawn block]--> t' ->
    P m t'.

mstep_preservation:
  forall_memory m (P m) ->
    P m t ->
    m / t ==[e]==> m' / t' ->
    P m' t'.

-------------------------------------------------------------------------------

thread_default_preservation:
  forall m,
    P m thread_default.

spawn_block_preservation:
  forall m t t' block,
    P m t ->
    t --[EF_Spawn block]--> t' ->
    P m block.

(* The untouched threads with the new memory still preserve the property. *)
untouched_threads_preservation:
  forall m m' ths tid tid' e t',
    forall_threads ths (P m) ->
    tid <> tid' ->
    tid' < #ths ->
    m / ths[tid] ==[e]==> m' / t' ->
    P m' ths[tid'].

cstep_preservation:
  forall m m' ths ths' tid e,
    forall_memory m (P m) ->
    forall_threads ths (P m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' (P m').

-------------------------------------------------------------------------------

tstep_alloc_mem_preservation:
  forall m t t' v T,
    P m t ->
    forall_memory m (P m) ->
    t --[EF_Alloc (#m) v T]--> t' ->
    forall_memory  (m +++ (v, T)) (P (m +++ (v, T))).

tstep_write_mem_preservation:
  forall m t t' ad v T,
    P m t ->
    forall_memory m (P m) ->
    t --[EF_Write ad v T]--> t' ->
    forall_memory m[ad <- (v, T)] (P m[ad <- (v, T)]).

mstep_mem_preservation:
  forall m m' t t' e,
    P m t ->
    forall_memory m (P m) ->
    m / t ==[e]==> m' / t' ->
    forall_memory m' (P m').

cstep_mem_preservation:
  forall m m' ths ths' tid e,
    forall_threads ths (P m) ->
    forall_memory m (P m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_memory m' (P m').

-------------------------------------------------------------------------------

preservation:
  forall m m' ths ths' tid e,
    forall_program m ths (P m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_program m' ths' (P m').

---------------------------------------------------------------------------- *)

Corollary mstep_preservation (P : mem -> tm -> Prop) : forall m m' t t',
  (* tstep_none_preservation *)
  (P m t ->
   t --[EF_None]--> t' ->
   P m t') ->
  (* tstep_alloc_preservation *)
  (forall v T,
    P m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    P (m +++ (v, T)) t') ->
  (* tstep_read_preservation *)
  (forall ad v,
    P m v ->
    P m t ->
    t --[EF_Read ad v]--> t' ->
    P m t') ->
  (* tstep_write_preservation: *)
  (forall ad v T,
    P m t ->
    t --[EF_Write ad v T]--> t' ->
    P m[ad <- (v, T)] t') ->
  (* What we want to prove: *)
  forall e,
    forall_memory m (P m) ->
    P m t ->
    m / t ==[e]==> m' / t' ->
    P m' t'.
Proof. intros. inversion_mstep; eauto. Qed.

Lemma cstep_preservation (P : mem -> tm -> Prop) : forall m m' ths ths' tid e,
    (* tstep_spawn_preservation *)
    (forall t t' block,
      P m t ->
      t --[EF_Spawn block]--> t' ->
      P m t') ->
    (* mstep_preservation *)
    (forall t',
      forall_memory m (P m) ->
      P m ths[tid] ->
      m / ths[tid] ==[e]==> m' / t' ->
      P m' t') ->
    (* thread_default_preservation *)
    (forall m,
      P m thread_default) ->
    (* spawn_block_preservation *)
    (forall t t' block,
      P m t ->
      t --[EF_Spawn block]--> t' ->
      P m block) ->
    (* untouched_threads_preservation *)
    (forall tid' t',
      forall_threads ths (P m) ->
      tid <> tid' ->
      tid' < #ths ->
      m / ths[tid] ==[e]==> m' / t' ->
      P m' ths[tid']) ->
    (* What we want to prove: *)
    forall_memory m (P m) ->
    forall_threads ths (P m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' (P m').
Proof.
  intros. inversion_cstep; intros tid'.
  - destruct (nat_eq_dec tid' (#ths)); subst.
    + rewrite <- (set_preserves_length _ tid t'). simpl_array. eauto.
    + destruct (lt_eq_lt_dec tid' (length ths)) as [[Ha | ?] | Hb]; subst;
      try lia.
      * rewrite <- (set_preserves_length _ tid t') in Ha. simpl_array.
        destruct (nat_eq_dec tid tid'); subst; simpl_array; eauto.
      * rewrite <- (set_preserves_length _ tid t') in Hb. simpl_array. eauto.
  - destruct (nat_eq_dec tid tid'); subst; simpl_array; eauto.
    decompose sum (lt_eq_lt_dec tid' (#ths)); subst; eauto;
    simpl_array; eauto.
Qed.

Corollary mstep_mem_preservation (P : mem -> tm -> Prop) : forall m t t',
  (* tstep_alloc_mem_preservation *)
  (forall v T,
    P m t ->
    forall_memory m (P m) ->
    t --[EF_Alloc (#m) v T]--> t' ->
    forall_memory (m +++ (v, T)) (P (m +++ (v, T)))) ->
  (* tstep_write_mem_preservation *)
  (forall ad v T,
    P m t ->
    forall_memory m (P m) ->
    t --[EF_Write ad v T]--> t' ->
    forall_memory m[ad <- (v, T)] (P m[ad <- (v, T)])) ->
  (* What we want to prove: *)
  forall m' e,
    P m t ->
    forall_memory m (P m) ->
    m / t ==[e]==> m' / t' ->
    forall_memory m' (P m').
Proof. intros. inversion_mstep; eauto. Qed.

Corollary cstep_mem_preservation (P : mem -> tm -> Prop) :
  (* mstep_mem_preservation *)
  (forall m m' t t' e,
    P m t ->
    forall_memory m (P m) ->
    m / t ==[e]==> m' / t' ->
    forall_memory m' (P m')) ->
  (* What we want to prove: *)
  forall m m' ths ths' tid e,
    forall_threads ths (P m) ->
    forall_memory m (P m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_memory m' (P m').
Proof. intros. inversion_cstep; eauto. Qed.

Corollary preservation (P : mem -> tm -> Prop) : forall m m' ths ths' tid e,
  (* cstep_preservation *)
  (forall_memory m (P m) ->
   forall_threads ths (P m) ->
   m / ths ~~[tid, e]~~> m' / ths' ->
   forall_threads ths' (P m')) ->
  (* cstep_mem_preservation *)
  (forall_threads ths (P m) ->
   forall_memory m (P m) ->
   m / ths ~~[tid, e]~~> m' / ths' ->
   forall_memory m' (P m')) ->
  (* What we want to prove: *)
  forall_program m ths (P m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_program m' ths' (P m').
Proof. intros * ? ? [? ?]. intros. eauto. Qed.

