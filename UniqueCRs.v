From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import NoReacq.
From Elo Require Import ValidTerm.
From Elo Require Import OneCR.
From Elo Require Import IsWaiting.
From Elo Require Import InCR.

(* TODO: move *)
From Elo Require Import ConsistentWaits.

Local Lemma noreacq_from_nocr' : forall ad t wr,
  wr <> WR_ad ad        ->
  consistent_waits wr t ->
  (* --- *)
  no_cr    ad t ->
  no_reacq ad t.
Proof.
  intros ? ?. induction t; intros; invc_cw; invc_nocr; eauto using no_reacq;
  constructor; eauto;
  match goal with
  | IH : forall _, _ <> _ -> consistent_waits _ ?t -> _ -> no_reacq _ ?t
  , H  : consistent_waits ?wr ?t
  |- no_reacq _ ?t =>
      eapply (IH wr); eauto
  end;
  intros F; invc F. auto.
Qed.

Corollary noreacq_from_nocr : forall ad t,
  consistent_waits WR_none t ->
  (* --- *)
  no_cr    ad t ->
  no_reacq ad t.
Proof.
  intros. eapply noreacq_from_nocr'; eauto. intros F. invc F.
Qed.

Local Lemma nocr_wacq_contradiction' : forall ad t1 t2 wr,
  wr <> WR_ad ad         ->
  consistent_waits wr t1 ->
  (* --- *)
  no_cr ad t1            ->
  t1 --[e_wacq ad]--> t2 ->
  False.
Proof.
  intros. gendep wr. ind_tstep; intros; invc_cw; invc_nocr; eauto.
  spec. spec.
  match goal with IH : _ -> _ -> _ -> False, H : consistent_waits ?wr _ |- _ =>
   eapply (IH wr); eauto
  end.
  intros F. invc F. auto.
Qed.

Corollary nocr_wacq_contradiction : forall ad t1 t2,
  consistent_waits WR_none t1 ->
  (* --- *)
  no_cr ad t1            ->
  t1 --[e_wacq ad]--> t2 ->
  False.
Proof.
  intros. eapply nocr_wacq_contradiction'; eauto. intros F. invc F.
Qed.

Local Lemma nocr_wrel_contradiction' : forall ad t1 t2 wr,
  wr <> WR_ad ad         ->
  consistent_waits wr t1 ->
  (* --- *)
  no_cr ad t1            ->
  t1 --[e_wrel ad]--> t2 ->
  False.
Proof.
  intros. gendep wr. ind_tstep; intros; invc_cw; invc_nocr; eauto.
  spec. spec.
  match goal with IH : _ -> _ -> _ -> False, H : consistent_waits ?wr _ |- _ =>
   eapply (IH wr); eauto
  end.
  intros F. invc F. auto.
Qed.

Corollary nocr_wrel_contradiction : forall ad t1 t2,
  consistent_waits WR_none t1 ->
  (* --- *)
  no_cr ad t1            ->
  t1 --[e_wrel ad]--> t2 ->
  False.
Proof.
  intros. eapply nocr_wrel_contradiction'; eauto. intros F. invc F.
Qed.

(* ------------------------------------------------------------------------- *)
(* unique-critical-regions                                                   *)
(* ------------------------------------------------------------------------- *)

Definition unique_critical_regions (m : mem) (ths : threads) := forall ad,
  (m[ad].X = false -> forall_threads ths (not_in_cr ad)) /\
  (m[ad].X = true  -> forone_thread  ths (in_cr ad) (not_in_cr ad)).

(* lemmas ------------------------------------------------------------------ *)

Corollary incr_or_nincr_from_ucr : forall ad m ths tid,
  unique_critical_regions m ths ->
  in_cr ad ths[tid] \/ not_in_cr ad ths[tid].
Proof.
  intros * Hucr. specialize (Hucr ad) as [? Htrue].
  destruct (m[ad].X); spec; eauto.
  specialize Htrue as [tid' [? ?]].
  nat_eq_dec tid' tid; auto.
Qed.

Corollary ucr_incr_contradiction : forall ad m ths tid1 tid2,
  unique_critical_regions m ths ->
  (* --- *)
  tid1 <> tid2 ->
  in_cr ad ths[tid1] ->
  in_cr ad ths[tid2] ->
  False.
Proof.
  intros * Hucr **. specialize (Hucr ad) as [? Htrue].
  destruct (m[ad].X); spec;
  eauto using nincr_incr_contradiction.
  specialize Htrue as [tid [? ?]].
  nat_eq_dec tid1 tid; nat_eq_dec tid2 tid;
  eauto using nincr_incr_contradiction.
Qed.

Corollary ucr_incr_equality : forall ad m ths tid1 tid2,
  unique_critical_regions m ths ->
  (* --- *)
  in_cr ad ths[tid1] ->
  in_cr ad ths[tid2] ->
  tid1 = tid2.
Proof.
  intros. nat_eq_dec tid1 tid2; trivial. exfalso.
  eauto using ucr_incr_contradiction.
Qed.

Lemma locked_from_incr : forall m ths tid ad,
  unique_critical_regions m ths ->
  (* --- *)
  in_cr ad ths[tid] ->
  m[ad].X = true.
Proof.
  intros * Hucr ?.
  destruct (m[ad].X) eqn:Heq; trivial.
  specialize (Hucr ad) as [? _]. spec.
  exfalso. eauto using nincr_incr_contradiction.
Qed.

Lemma locked_from_rel : forall m ths tid t ad,
  forall_threads ths (valid_term m) ->
  unique_critical_regions m ths     ->
  (* --- *)
  ths[tid] --[e_rel ad]--> t ->
  m[ad].X = true.
Proof.
  intros * ? Hucr ?.
  destruct (m[ad].X) eqn:Heq; trivial.
  specialize (Hucr ad) as [Hnincr _]. spec.
  exfalso. specialize (Hnincr tid) as [? | ?];
  eauto using nocr_rel_contradiction, isw_effect_contradiction.
Qed.

Lemma locked_from_wrel : forall m ths tid t ad,
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_waits WR_none) ->
  unique_critical_regions m ths     ->
  (* --- *)
  ths[tid] --[e_wrel ad]--> t ->
  m[ad].X = true.
Proof.
  intros * ? ? Hucr ?.
  destruct (m[ad].X) eqn:Heq; trivial.
  specialize (Hucr ad) as [Hnincr _]. spec.
  exfalso. specialize (Hnincr tid) as [? | ?];
  eauto using nocr_wrel_contradiction, isw_effect_contradiction.
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
  - intros ?. omicron; eauto using nincr_preservation_none.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split; intros; omicron;
    eauto using nincr_preservation_none, incr_preservation_none.
Qed.

Local Lemma ucr_preservation_alloc : forall m ths tid t T R,
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  unique_critical_regions (m +++ new_cell T R) ths[tid <- t].
Proof.
  intros *.
  intros ? Hucr ? ad. specialize (Hucr ad) as [Hfall Hfone].
  split; intros; upsilon; spec.
  - intros ?. omicron; eauto using nincr_preservation_alloc.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nincr_preservation_alloc, incr_preservation_alloc.
Qed.

Local Lemma ucr_preservation_init : forall m ths tid t ad' t',
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_init ad' t']--> t ->
  unique_critical_regions m[ad'.t <- t'] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad. specialize (Hucr ad) as [Hfall Hfone].
  assert (ad' < #m) by eauto using vtm_init_address.
  split; intros; omicron; upsilon; spec; solve
    [ intro; omicron; eauto using nincr_preservation_init
    | specialize Hfone as [tid' [? ?]]; exists tid';
      split; intros; omicron;
      eauto using nincr_preservation_init, incr_preservation_init
    ].
Qed.

Local Lemma ucr_preservation_read : forall m ths tid t ad te,
  value te ->
  valid_term m te ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_read ad te]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros until 2.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  split; intros; upsilon; spec.
  - intros ?. omicron; eauto using nincr_preservation_read.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nincr_preservation_read, incr_preservation_read.
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
  eauto using nincr_unit, nincr_preservation_write;
  specialize Hfone as [tid' [? ?]]; exists tid'; split; intros;
  omicron; eauto using nincr_preservation_write, incr_preservation_write.
Qed.

Local Lemma ucr_preservation_acq : forall m ths tid ad t te,
  value te ->
  valid_term m te ->
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_waits WR_none) ->
  (* --- *)
  m[ad].X = false ->
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  unique_critical_regions m[ad.X <- true] ths[tid <- t].
Proof.
  intros until 5.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  assert (ad < #m) by eauto using vtm_acq_address.
  split; intros; repeat omicron; spec; upsilon;
  eauto using nincr_unit, nincr_preservation_acq.
  - exists tid. sigma. split.
    + split.
      * specialize (Hfall tid) as [? | ?].
        ** eauto using nocrs_from_value, nocr_to_onecr.
        ** exfalso. eauto using isw_effect_contradiction.
      * specialize (Hfall tid) as [? | ?].
        ** eauto using noreacq_from_value, noreacq_preservation_acq,
            noreacq_from_nocr.
        ** exfalso. eauto using isw_effect_contradiction.
    + intros. sigma. eauto.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split.
    + omicron; eauto using incr_preservation_acq.
    + intros. omicron; eauto using nincr_preservation_acq.
Qed.

Local Lemma ucr_preservation_rel : forall m ths tid ad t,
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_rel ad]--> t ->
  unique_critical_regions m[ad.X <- false] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad'. destruct (Hucr ad') as [Hfall Hfone].
  assert (Had : m[ad].X = true) by eauto using locked_from_rel.
  split; intros; try intros tid'; repeat omicron; spec; upsilon;
  auto; eauto using nincr_preservation_rel;
  specialize Hfone as [tid'' [Hincr Hnincr]].
  - destruct Hincr. nat_eq_dec tid'' tid'.
    + left. eauto using onecr_to_nocr.
    + specialize (Hnincr tid'). spec. destruct Hnincr; exfalso;
      eauto using nocr_rel_contradiction, isw_effect_contradiction.
  - nat_eq_dec tid'' tid'; auto.
    specialize (Hnincr tid). spec. destruct Hnincr; exfalso;
    eauto using nocr_rel_contradiction, isw_effect_contradiction.
  - exists tid''. nat_eq_dec tid'' tid; sigma;
    split; eauto using incr_preservation_rel; intros.
    + sigma. auto.
    + omicron; eauto using nincr_preservation_rel.
Qed.

Local Lemma ucr_preservation_wacq : forall m ths tid t ad,
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_waits WR_none) ->
  (* --- *)
  ad < #m ->
  m[ad].X = false ->
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_wacq ad]--> t ->
  unique_critical_regions m[ad.X <- true] ths[tid <- t].
Proof.
  intros until 4.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  split; intros; repeat omicron; spec; upsilon;
  eauto using nincr_unit, nincr_preservation_wacq.
  - exists tid. sigma. split.
    + split.
      * specialize (Hfall tid) as [? | ?].
        ** exfalso. eauto using noreacq_from_nocr, noreacq_wacq_contradiction.
        ** admit. (* onecr_from_isw *)
      * specialize (Hfall tid) as [? | ?].
        ** eauto using nocr_preservation_wacq, cw_preservation_wacq,
            noreacq_from_nocr.
        ** eauto using isw_to_noreacq.
    + intros. sigma. eauto.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split.
    + omicron; eauto using incr_preservation_wacq.
    + intros. omicron; eauto using nincr_preservation_wacq.
Abort.

Local Lemma ucr_preservation_wrel : forall m ths tid ad t,
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_waits WR_none) ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_wrel ad]--> t ->
  unique_critical_regions m[ad.X <- false] ths[tid <- t].
Proof.
  intros until 2.
  intros ? Hucr ? ad'. destruct (Hucr ad') as [Hfall Hfone].
  assert (Had : m[ad].X = true) by eauto using locked_from_wrel.
  split; intros; try intros tid'; repeat omicron; spec; upsilon;
  auto; eauto using nincr_preservation_wrel;
  specialize Hfone as [tid'' [Hincr Hnincr]].
  - destruct Hincr. nat_eq_dec tid'' tid'.
    + right. eauto using noreacq_to_isw.
    + specialize (Hnincr tid'). spec. exfalso. destruct Hnincr.
      * eauto using nocr_wrel_contradiction.
      * eauto using isw_effect_contradiction.
  - nat_eq_dec tid'' tid'; auto.
    destruct Hincr. specialize (Hnincr tid). spec. exfalso. destruct Hnincr.
    + eauto using nocr_wrel_contradiction.
    + eauto using isw_effect_contradiction.
  - exists tid''. nat_eq_dec tid'' tid; sigma;
    split; eauto using incr_preservation_wrel; intros.
    + sigma. auto.
    + omicron; eauto using nincr_preservation_wrel.
Qed.

Local Ltac eapply_in_tstep tt :=
  match goal with Htstep : _ --[_]--> _ |- _ => eapply tt in Htstep as ? end.

Local Lemma ucr_preservation_spawn : forall m ths tid t t',
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_spawn t']--> t ->
  unique_critical_regions m (ths[tid <- t] +++ t').
Proof.
  intros until 1.
  intros ? Hucr ? ad'. destruct (Hucr ad') as [Hfall Hfone].
  split; intros; spec.
  - intro. omicron;
    eauto using nincr_preservation_spawn, nincr_unit.
    left. eauto using nocr_spawn_term.
  - specialize Hfone as [tid' [Hincr Hnincr]]. exists tid'. split.
    + omicron; eauto.
      * eauto using incr_preservation_spawn.
      * destruct Hincr. invc_onecr.
    + intros. omicron; eauto using nincr_preservation_spawn, nincr_unit.
      left. eauto using nocr_spawn_term.
Qed.

Theorem ucr_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value                ->
  forall_program m1 ths1 (valid_term m1) ->
  forall_program m1 ths1 (consistent_waits WR_none) ->
  (* --- *)
  unique_critical_regions m1 ths1 ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  unique_critical_regions m2 ths2.
Proof.
  intros * ? [? ?] [? ?] **. invc_cstep; try invc_mstep.
  - eauto using ucr_preservation_none.
  - sigma. upsilon. eauto using ucr_preservation_alloc.
  - eauto using ucr_preservation_init.
  - eauto using ucr_preservation_read.
  - eauto using ucr_preservation_write.
  - eauto using ucr_preservation_acq.
  - eauto using ucr_preservation_rel.
  - admit. (* eauto using ucr_preservation_wacq. *)
  - eauto using ucr_preservation_wrel.
  - eauto using ucr_preservation_spawn.
Qed.

Theorem ucr_preservation_base : forall t,
  no_crs t ->
  (* --- *)
  unique_critical_regions nil (base t).
Proof.
  unfold base. intros ** ?. split; intros Hnil.
  - intro. left. omicron; auto using no_cr.
  - simpl in Hnil. destruct ad; upsilon; auto.
Qed.

