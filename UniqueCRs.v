From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import ValidTerm.
From Elo Require Import OneCR.

(* ------------------------------------------------------------------------- *)
(* unique-critical-regions                                                   *)
(* ------------------------------------------------------------------------- *)

Definition unique_critical_regions (m : mem) (ths : threads) := forall ad,
  (m[ad].X = false -> forall_threads ths (no_cr ad)) /\
  (m[ad].X = true  -> forone_thread  ths (one_cr ad) (no_cr ad)).

(* lemmas ------------------------------------------------------------------ *)

Corollary nocr_or_onecr_from_ucr : forall ad m ths tid,
  unique_critical_regions m ths ->
  no_cr ad ths[tid] \/ one_cr ad ths[tid].
Proof.
  intros * Hucr. specialize (Hucr ad) as [? Htrue].
  destruct (m[ad].X); spec; eauto.
  specialize Htrue as [tid' [? ?]].
  nat_eq_dec tid' tid; auto.
Qed.

Corollary ucr_onecr_contradiction : forall ad m ths tid1 tid2,
  unique_critical_regions m ths ->
  (* --- *)
  tid1 <> tid2 ->
  one_cr ad ths[tid1] ->
  one_cr ad ths[tid2] ->
  False.
Proof.
  intros * Hucr **. specialize (Hucr ad) as [? Htrue].
  destruct (m[ad].X); spec;
  eauto using nocr_onecr_contradiction.
  specialize Htrue as [tid [? ?]].
  nat_eq_dec tid1 tid; nat_eq_dec tid2 tid;
  eauto using nocr_onecr_contradiction.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma ucr_mem_region : forall m ths ad R,
  unique_critical_regions m ths ->
  unique_critical_regions m[ad.R <- R] ths.
Proof.
  intros * H. intros ad'. specialize (H ad').
  repeat omicron; upsilon; destruct H; trivial;
  split; repeat intro; repeat omicron; upsilon; spec; eauto.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma ucr_preservation_none : forall m ths tid t,
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_none]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad. specialize (Hucr ad) as [Hfall Hfone].
  split; intros; spec.
  - intros ?. omicron; eauto using nocr_preservation_none.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split; intros; omicron;
    eauto using nocr_preservation_none, onecr_preservation_none.
Qed.

Local Lemma ucr_preservation_alloc : forall m ths tid t T,
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  unique_critical_regions (m +++ (None, T, false, R_invalid)) ths[tid <- t].
Proof.
  intros *.
  intros ? Hucr ? ad. specialize (Hucr ad) as [Hfall Hfone].
  split; intros; upsilon; spec.
  - intros ?. omicron; eauto using nocr_preservation_alloc.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nocr_preservation_alloc, onecr_preservation_alloc.
Qed.

Local Lemma ucr_preservation_insert : forall m ths tid t ad' t' T',
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_insert ad' t' T']--> t ->
  unique_critical_regions m[ad'.t <- t'] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad. specialize (Hucr ad) as [Hfall Hfone].
  assert (ad' < #m) by eauto using vtm_insert_address.
  split; intros; repeat omicron; spec; upsilon;
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
  split; intros; upsilon; spec.
  - intros ?. omicron; eauto using nocr_preservation_read.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nocr_preservation_read, onecr_preservation_read.
Qed.

Local Lemma ucr_preservation_write : forall m ths tid t ad te,
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_write ad te]--> t ->
  unique_critical_regions m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  assert (ad < #m) by eauto using vtm_write_address.
  split; intros; repeat omicron; spec; upsilon;
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
  split; intros; repeat omicron; spec; upsilon;
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
    specialize (Hucr ad) as [? _]. spec.
    exfalso. eauto using nocr_rel_contradiction.
  } 
  split; intros; try intros tid'; repeat omicron; spec; upsilon;
  eauto using nocr_preservation_rel;
  specialize Hfone as [tid'' [? ?]].
  - nat_eq_dec tid'' tid'; eauto using onecr_to_nocr.
    exfalso. eauto using nocr_rel_contradiction.
  - nat_eq_dec tid'' tid'; eauto using nocr_rel_contradiction.
  - exists tid''. nat_eq_dec tid'' tid; sigma;
    split; eauto using onecr_preservation_rel; intros.
    + sigma. auto.
    + omicron; eauto using nocr_preservation_rel.
Qed.

Local Ltac eapply_in_tstep tt :=
  match goal with Htstep : _ --[_]--> _ |- _ => eapply tt in Htstep as ? end.

Local Lemma ucr_preservation_spawn : forall m ths tid t te,
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  unique_critical_regions m (ths[tid <- t] +++ te).
Proof.
  intros until 1.
  intros ? Hucr ? ad'. destruct (Hucr ad') as [Hfall Hfone].
  split; intros; repeat omicron; spec; upsilon.
  - eapply_in_tstep nocr_preservation_spawn; eauto using no_cr.
  - eauto using nocr_preservation_spawned.
  - specialize Hfone as [tid' [? ?]]. exists tid'. omicron;
    try invc_onecr; split; eauto using onecr_preservation_spawn; intros;
    omicron; eauto using no_cr.
    + eapply_in_tstep nocrs_spawn_term; eauto.
    + eauto using nocr_preservation_spawn.
    + eapply_in_tstep nocrs_spawn_term; eauto.
Qed.

Theorem ucr_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value                ->
  forall_program m1 ths1 (valid_term m1) ->
  (* --- *)
  unique_critical_regions m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  unique_critical_regions m2 ths2.
Proof.
  intros * ? [? ?] **. invc_cstep; try invc_mstep.
  - eauto using ucr_preservation_none.
  - eauto using ucr_preservation_alloc.
  - eauto using ucr_preservation_insert.
  - eauto using nocrs_from_value, ucr_preservation_read.
  - eauto using ucr_preservation_write.
  - eauto using nocrs_from_value, ucr_preservation_acq.
  - eauto using ucr_preservation_rel.
  - eauto using ucr_preservation_spawn.
Qed.

Theorem ucr_preservation_rstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value                ->
  forall_program m1 ths1 (valid_term m1) ->
  (* --- *)
  unique_critical_regions m1 ths1 ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  unique_critical_regions m2 ths2.
Proof.
  intros. invc_ostep; eauto using ucr_preservation_cstep.
  match goal with _ : _ / _ ~~[_, _]~~> ?m / ?ths |- _ =>
    assert (unique_critical_regions m ths)
  end;
  eauto using ucr_preservation_cstep, ucr_mem_region.
Qed.

Theorem ucr_preservation_ustep : forall m1 m2 ths1 ths2 tc,
  forall_memory  m1 value                ->
  forall_program m1 ths1 (valid_term m1) ->
  (* --- *)
  unique_critical_regions m1 ths1 ->
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  unique_critical_regions m2 ths2.
Proof.
  intros. ind_ustep;
  eauto using ucr_preservation_rstep,
    value_preservation_ustep,
    vtm_preservation_ustep.
Qed.

Theorem ucr_preservation_base : forall t,
  no_crs t ->
  (* --- *)
  unique_critical_regions base_m (base_t t).
Proof.
  unfold base_m, base_t. intros ** ?. split; intros Hnil.
  - intro. omicron; auto using no_cr.
  - simpl in Hnil. destruct ad; upsilon; auto.
Qed.

