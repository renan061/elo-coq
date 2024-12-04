From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import ValidAddresses.
From Elo Require Import NoRef.
From Elo Require Import NoInit.
From Elo Require Import ValidBlocks.
From Elo Require Import OneInit.
From Elo Require Import NoUninitRefs.

(* ------------------------------------------------------------------------- *)
(* unique-initializers                                                       *)
(* ------------------------------------------------------------------------- *)

Definition unique_initializers (m : mem) (ths : threads) := forall ad,
  ad < #m ->
  (m[ad].t <> None -> forall_threads ths (no_init ad)) /\
  (m[ad].t =  None -> forone_thread  ths (one_init ad) (no_init ad)).

(* lemmas ------------------------------------------------------------------ *)

Corollary noinit_or_oneinit_from_ui : forall ad m ths tid,
  ad < #m ->
  unique_initializers m ths ->
  no_init ad ths[tid] \/ one_init ad ths[tid].
Proof.
  intros * Had Hui. specialize (Hui ad Had) as [? Hnone].
  opt_dec (m[ad].t); spec; auto.
  specialize Hnone as [tid' [? ?]]. nat_eq_dec tid' tid; auto.
Qed.

Corollary ui_oneinit_contradiction : forall ad m ths tid1 tid2,
  unique_initializers m ths ->
  (* --- *)
  ad < #m ->
  tid1 <> tid2 ->
  one_init ad ths[tid1] ->
  one_init ad ths[tid2] ->
  False.
Proof.
  intros * Hui Had **. specialize (Hui ad Had) as [? Hnone].
  opt_dec (m[ad].t); spec;
  eauto using noinit_oneinit_contradiction.
  specialize Hnone as [tid [? ?]].
  nat_eq_dec tid1 tid; nat_eq_dec tid2 tid;
  eauto using noinit_oneinit_contradiction.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma ui_preservation_none : forall m ths tid t,
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_none]--> t ->
  unique_initializers m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hui ? ad Had. specialize (Hui ad Had) as [Hfall Hfone].
  split; intros; spec.
  - intros ?. omicron; eauto using noinit_preservation_none.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split; intros; omicron;
    eauto using noinit_preservation_none, oneinit_preservation_none.
Qed.

Local Lemma ui_preservation_alloc : forall m ths tid t T,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  unique_initializers (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hui ? ad Had. omicron.
  - specialize (Hui ad) as [Hfall Hfone]; trivial.
    split; intros; upsilon; spec.
    + intros ?. omicron; eauto using noinit_preservation_alloc.
    + specialize Hfone as [tid' [? ?]]. exists tid'.
      assert (ad < #m) by eauto using oneinit_ad_bound.
      split; intros; omicron;
      eauto using noinit_preservation_alloc, oneinit_preservation_alloc.
  - split; intros; upsilon; auto. exists tid. split; intros; sigma;
    eauto using noinit_from_vad1, noinit_to_oneinit.
  - lia.
Qed.

Local Lemma ui_preservation_insert : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_insert ad te]--> t ->
  unique_initializers m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 2.
  intros ? Hui ? ad' Had'. sigma. specialize (Hui ad' Had') as [Hfall Hfone].
  assert (ad < #m) by eauto using vad_insert_address.
  opt_dec (m[ad'].t); spec; split; intros.
  - specialize Hfone as [tid'' [? ?]].
    intros tid'. repeat omicron; nat_eq_dec tid'' tid';
    eauto using oneinit_to_noinit;
    exfalso; eauto using noinit_insert_contradiction.
  - specialize Hfone as [tid'' [? ?]].
    repeat omicron; try discriminate.
    exists tid''. split; intros; omicron;
    eauto using noinit_preservation_insert, oneinit_preservation_insert.
  - intros tid'. repeat omicron; eauto using noinit_preservation_insert.
    exfalso. eauto using noinit_insert_contradiction.
  - omicron; eauto. discriminate.
Qed.

Local Lemma ui_preservation_read : forall m ths tid t ad te,
  no_inits te ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_read ad te]--> t ->
  unique_initializers m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hui ? ad' Had'. specialize (Hui ad' Had') as [Hfall Hfone].
  split; intros; upsilon; spec.
  - intros ?. omicron; eauto using noinit_preservation_read.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using noinit_preservation_read, oneinit_preservation_read.
Qed.

Local Lemma ui_preservation_write : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  no_uninitialized_references m ths ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_write ad te]--> t ->
  unique_initializers m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 2. intros Hnur.
  intros ? Hui ? ad' Had'. sigma. specialize (Hui ad' Had') as [Hfall Hfone].
  assert (ad < #m) by eauto using vad_write_address.
  split; intros; repeat omicron; try discriminate; try spec.
  - destruct (_opt_dec m[ad'].t) as [Hmad' | Hmad']; spec.
    + destruct (Hnur ad' Hmad').
      exfalso. eauto using noref_write_contradiction.
    + intros ?. omicron; eauto using noinit_preservation_write.
  - intros ?. omicron; eauto using noinit_preservation_write.
  - specialize Hfone as [tid' [? ?]]. exists tid'; split; intros;
    omicron; eauto using noinit_preservation_write, oneinit_preservation_write.
Qed.

Local Lemma ui_preservation_acq : forall m ths tid ad t te,
  no_inits te ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  unique_initializers m[ad.X <- true] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hui ? ad' Had'. sigma. specialize (Hui ad' Had') as [Hfall Hfone].
  split; intros; upsilon; spec.
  - intros ?. omicron; eauto using noinit_preservation_acq.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using noinit_preservation_acq, oneinit_preservation_acq.
Qed.

Local Lemma ui_preservation_rel : forall m ths tid ad t,
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_rel ad]--> t ->
  unique_initializers m[ad.X <- false] ths[tid <- t].
Proof.
  intros *.
  intros ? Hui ? ad' Had'. sigma. specialize (Hui ad' Had') as [Hfall Hfone].
  split; intros; upsilon; spec.
  - intros ?. omicron; eauto using noinit_preservation_rel.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using noinit_preservation_rel, oneinit_preservation_rel.
Qed.

Local Lemma ui_preservation_spawn : forall m ths tid t te,
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  unique_initializers m (ths[tid <- t] +++ te).
Proof.
  intros until 1.
  intros ? Hui ? ad' Had'. specialize (Hui ad' Had') as [Hfall Hfone].
  split; intros; upsilon; spec.
  - intros ?. omicron; try constructor;
    eauto using noinit_preservation_spawn, noinit_preservation_spawned.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron; try constructor;
    eauto using noinit_preservation_spawn, oneinit_preservation_spawn.
    + invc_oneinit.
    + eauto using noinit_spawn_term.
Qed.

Theorem ui_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_inits ->
  forall_program m1 ths1 (valid_addresses m1) ->
  forall_program m1 ths1 valid_blocks ->
  no_uninitialized_references m1 ths1 ->
  (* --- *)
  unique_initializers m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  unique_initializers m2 ths2.
Proof.
  intros * ? [? ?] [? ?] ? **. invc_cstep; try invc_mstep.
  - eauto using ui_preservation_none.
  - eauto using ui_preservation_alloc.
  - eauto using ui_preservation_insert.
  - eauto using ui_preservation_read.
  - eauto using ui_preservation_write.
  - eauto using ui_preservation_acq.
  - eauto using ui_preservation_rel.
  - eauto using ui_preservation_spawn.
Qed.

