From Elo Require Import Core.
From Elo Require Import Properties1.

(* ------------------------------------------------------------------------- *)
(* unique-critical-regions                                                   *)
(* ------------------------------------------------------------------------- *)

Definition unique_critical_regions (m : mem) (ths : threads) := forall ad,
  (m[ad].X = false -> forall_threads ths (no_cr ad)) /\
  (m[ad].X = true  -> forone_thread  ths (one_cr ad) (no_cr ad)).

(* preservation -- --------------------------------------------------------- *)

Local Lemma ucr_preservation_none : forall m ths tid t,
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_none]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad. specialize (Hucr ad) as [Hfall Hfone].
  split; intros; aspecialize.
  - intros ?. omicron; eauto using nocr_preservation_none.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split; intros; omicron;
    eauto using nocr_preservation_none, onecr_preservation_none.
Qed.

Local Lemma ucr_preservation_alloc : forall m ths tid t T,
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  unique_critical_regions (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros *.
  intros ? Hucr ? ad. specialize (Hucr ad) as [Hfall Hfone].
  split; intros; upsilon; aspecialize.
  - intros ?. omicron; eauto using nocr_preservation_alloc.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nocr_preservation_alloc, onecr_preservation_alloc.
Qed.

Local Lemma ucr_preservation_insert : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_insert ad te]--> t ->
  unique_critical_regions m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 2.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  assert (ad < #m) by eauto using vad_insert_addr.
  split; intros; repeat omicron; aspecialize; upsilon;
  eauto using nocr_preservation_insert;
  specialize Hfone as [tid' [? ?]]; exists tid'; split; intros;
  omicron; eauto using nocr_preservation_insert, onecr_preservation_insert.
Qed.

Local Lemma ucr_preservation_read : forall m ths tid t ad te,
  no_crs te ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_read ad te]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  split; intros; upsilon; aspecialize.
  - intros ?. omicron; eauto using nocr_preservation_read.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nocr_preservation_read, onecr_preservation_read.
Qed.

Local Lemma ucr_preservation_write : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_write ad te]--> t ->
  unique_critical_regions m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 2.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  assert (ad < #m) by eauto using vad_write_addr.
  split; intros; repeat omicron; aspecialize; upsilon;
  eauto using nocr_preservation_write;
  specialize Hfone as [tid' [? ?]]; exists tid'; split; intros;
  omicron; eauto using nocr_preservation_write, onecr_preservation_write.
Qed.

Local Lemma ucr_preservation_acq : forall m ths tid ad t te,
  no_crs te ->
  (* --- *)
  ad < #m ->
  m[ad].X = false ->
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  unique_critical_regions m[ad.X <- true] ths[tid <- t].
Proof.
  intros until 3.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  split; intros; repeat omicron; aspecialize; upsilon;
  eauto using nocr_preservation_acq.
  - exists tid. sigma. split.
    + eauto using nocr_to_onecr.
    + intros. sigma. eauto.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split.
    + omicron; eauto using onecr_preservation_acq.
    + intros. omicron; eauto using nocr_preservation_acq.
Qed.

Local Lemma ucr_preservation_rel : forall m ths tid ad t,
  ad < #m ->
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_rel ad]--> t ->
  unique_critical_regions m[ad.X <- false] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad'. destruct (Hucr ad') as [Hfall Hfone].
  assert (Had : m[ad].X = true). { (* This is cool *)
    destruct (m[ad].X) eqn:Heq; trivial.
    specialize (Hucr ad) as [? _]. aspecialize.
    exfalso. eauto using nocr_rel_contradiction.
  } 
  split; intros; try intros tid'; repeat omicron; aspecialize; upsilon;
  eauto using nocr_preservation_rel;
  specialize Hfone as [tid'' [? ?]].
  - destruct (nat_eq_dec tid'' tid'); subst; eauto using onecr_to_nocr.
    exfalso. eauto using nocr_rel_contradiction.
  - destruct (nat_eq_dec tid'' tid'); subst;
    eauto using nocr_rel_contradiction.
  - exists tid''.
    destruct (nat_eq_dec tid'' tid); subst; sigma;
    split; eauto using onecr_preservation_rel; intros.
    + sigma. eauto.
    + omicron; eauto using nocr_preservation_rel.
Qed.

Local Ltac eapply_in_tstep tt :=
  match goal with Htstep : _ --[_]--> _ |- _ => eapply tt in Htstep as ? end.

Local Lemma ucr_preservation_spawn : forall m ths tid t te,
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  unique_critical_regions m (ths[tid <- t] +++ te).
Proof.
  intros until 1.
  intros ? Hucr ? ad'. destruct (Hucr ad') as [Hfall Hfone].
  split; intros; repeat omicron; aspecialize; upsilon.
  - eapply_in_tstep nocr_preservation_spawn; eauto using no_cr.
  - eauto using nocr_preservation_spawned.
  - specialize Hfone as [tid' [? ?]]. exists tid'. omicron;
    try invc_onecr; split; eauto using onecr_preservation_spawn; intros;
    omicron; eauto using no_cr.
    + eapply_in_tstep nocrs_spawn_term; eauto.
    + eauto using nocr_preservation_spawn.
    + eapply_in_tstep nocrs_spawn_term; eauto.
Qed.

Theorem ucr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_crs ->
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 valid_blocks ->
  (* --- *)
  unique_critical_regions m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  unique_critical_regions m2 ths2.
Proof.
  intros. invc_cstep; try invc_mstep.
  - eauto using ucr_preservation_none.
  - eauto using ucr_preservation_alloc.
  - eauto using ucr_preservation_insert.
  - eauto using ucr_preservation_read.
  - eauto using ucr_preservation_write.
  - eauto using ucr_preservation_acq.
  - eauto using ucr_preservation_rel.
  - eauto using ucr_preservation_spawn.
Qed.

