From Elo Require Import Core.
From Elo Require Import Properties1.

From Elo Require Import UniqueInits.
From Elo Require Import ConsistentInits.

(* ------------------------------------------------------------------------- *)
(* init-cr-exclusivity                                                       *)
(* ------------------------------------------------------------------------- *)

Definition init_cr_exclusivity (m : mem) (ths : threads) := forall ad tid1 tid2,
  (one_init ad ths[tid1] -> no_cr   ad ths[tid2]) /\
  (one_cr   ad ths[tid1] -> no_init ad ths[tid2]).

(* preservation ------------------------------------------------------------ *)

Lemma ice_preservation_none : forall m ths tid t,
  forall_threads ths valid_blocks ->
  (* --- *)
  init_cr_exclusivity m ths ->
  ths[tid] --[e_none]--> t ->
  init_cr_exclusivity m ths[tid <- t].
Proof.
  intros * ? Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto;
  eauto using nocr_preservation_none, oneinit_inheritance_none;
  eauto using noinit_preservation_none, onecr_inheritance_none.
Qed.

Lemma ice_preservation_alloc : forall m ths tid t T,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  (* --- *)
  init_cr_exclusivity m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  init_cr_exclusivity (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros * Hvad ? Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  assert (forall tid, no_cr (#m) ths[tid]) by eauto using nocr_from_vad.
  split; intros; repeat omicron; auto; destruct (nat_eq_dec ad (#m)); subst;
  eauto using nocr_preservation_alloc, oneinit_inheritance_alloc;
  eauto using noinit_preservation_alloc, onecr_inheritance_alloc;
  exfalso; eauto using onecr_inheritance_alloc, nocr_onecr_contradiction.
Qed.

Theorem insert_then_noinit : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (consistent_inits m) ->
  unique_initializers m ths ->
  (* --- *)
  ths[tid] --[e_insert ad te]--> t ->
  one_init ad ths[tid].
Proof.
  intros * ? ? Hui **.
  assert (Had   : ad < #m) by eauto using vad_insert_addr.
  assert (Hnone : m[ad].t = None) by eauto using insert_then_uninitialized.
  specialize (Hui ad Had) as [_ Hui]. specialize (Hui Hnone) as [tid' [? ?]].
  destruct (nat_eq_dec tid' tid); subst; trivial.
  exfalso. eauto using noinit_insert_contradiction.
Qed.

Lemma ice_preservation_insert : forall m ths tid t ad te,
  forall_threads ths valid_blocks ->
  (* --- *)
  init_cr_exclusivity m ths ->
  ths[tid] --[e_insert ad te]--> t ->
  init_cr_exclusivity m ths[tid <- t].
Proof.
  intros until 1. rename ad into ad'.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; destruct (nat_eq_dec ad' ad); subst;
  eauto using nocr_preservation_insert, oneinit_inheritance_insert;
  eauto using noinit_preservation_insert, onecr_inheritance_insert.
  -
Qed.
