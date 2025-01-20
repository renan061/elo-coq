From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import NoReacq.
From Elo Require Import ValidTerm.
From Elo Require Import ConsistentWaits.
From Elo Require Import OneCR.
From Elo Require Import Waiting.
From Elo Require Import Holding.

(* ------------------------------------------------------------------------- *)
(* unique-holding                                                            *)
(* ------------------------------------------------------------------------- *)

Definition unique_holding (m : mem) (ths : threads) := forall ad,
  (m[ad].X = false -> forall_threads ths (not_holding ad)) /\
  (m[ad].X = true  -> forone_thread  ths (holding ad) (not_holding ad)).

(* lemmas ------------------------------------------------------------------ *)

Corollary hg_or_nhg_from_uhg : forall ad m ths tid,
  unique_holding m ths ->
  holding ad ths[tid] \/ not_holding ad ths[tid].
Proof.
  intros * Huhg. specialize (Huhg ad) as [? Htrue].
  destruct (m[ad].X); spec; eauto.
  specialize Htrue as [tid' [? ?]].
  nat_eq_dec tid' tid; auto.
Qed.

Corollary nocr_or_onecr_from_uhg : forall ad m ths tid,
  unique_holding m ths ->
  no_cr ad ths[tid] \/ one_cr ad ths[tid].
Proof.
  intros * Huhg. specialize (Huhg ad) as [Hfalse Htrue].
  destruct (m[ad].X); spec.
  - specialize Htrue as [tid' [[? ?] Hnhg]].
    nat_eq_dec tid' tid; auto.
    specialize (Hnhg tid). spec. destruct Hnhg as [? | [? ?]]; eauto.
  - specialize (Hfalse tid). destruct Hfalse as [? | [? ?]]; eauto.
Qed.

Corollary uhg_hg_contradiction : forall ad m ths tid1 tid2,
  unique_holding m ths ->
  (* --- *)
  tid1 <> tid2 ->
  holding ad ths[tid1] ->
  holding ad ths[tid2] ->
  False.
Proof.
  intros * Huhg **. specialize (Huhg ad) as [? Htrue].
  destruct (m[ad].X); spec;
  eauto using hg_contradiction.
  specialize Htrue as [tid [? ?]].
  nat_eq_dec tid1 tid; nat_eq_dec tid2 tid;
  eauto using hg_contradiction.
Qed.

Corollary uhg_hg_equality : forall ad m ths tid1 tid2,
  unique_holding m ths ->
  (* --- *)
  holding ad ths[tid1] ->
  holding ad ths[tid2] ->
  tid1 = tid2.
Proof.
  intros. nat_eq_dec tid1 tid2; trivial. exfalso.
  eauto using uhg_hg_contradiction.
Qed.

Lemma locked_from_holding : forall m ths tid ad,
  unique_holding m ths ->
  (* --- *)
  holding ad ths[tid] ->
  m[ad].X = true.
Proof.
  intros * Huhg ?.
  destruct (m[ad].X) eqn:Heq; trivial.
  specialize (Huhg ad) as [? _]. spec.
  exfalso. eauto using hg_contradiction.
Qed.

Lemma locked_from_rel : forall m ths tid t ad,
  forall_threads ths (valid_term m) ->
  unique_holding m ths     ->
  (* --- *)
  ths[tid] --[e_rel ad]--> t ->
  m[ad].X = true.
Proof.
  intros * ? Huhg ?.
  destruct (m[ad].X) eqn:Heq; trivial.
  specialize (Huhg ad) as [Hnholding _]. spec.
  exfalso. specialize (Hnholding tid) as [? | [? ?]];
  eauto using nocr_rel_contradiction, wg_effect_contradiction.
Qed.

Lemma locked_from_wrel : forall m ths tid t ad,
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_waits WR_none) ->
  unique_holding m ths     ->
  (* --- *)
  ths[tid] --[e_wrel ad]--> t ->
  m[ad].X = true.
Proof.
  intros * ? ? Huhg ?.
  destruct (m[ad].X) eqn:Heq; trivial.
  specialize (Huhg ad) as [Hnholding _]. spec.
  exfalso. specialize (Hnholding tid) as [? | [? ?]];
  eauto using nocr_wrel_contradiction, wg_effect_contradiction.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma uhg_mem_region : forall m ths ad R,
  unique_holding m ths ->
  unique_holding m[ad.R <- R] ths.
Proof.
  intros * H. intros ad'. specialize (H ad').
  repeat omicron; upsilon; destruct H; trivial;
  split; repeat intro; repeat omicron; upsilon; spec; eauto.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma uhg_preservation_none : forall m ths tid t,
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_none]--> t ->
  unique_holding m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Huhg ? ad. specialize (Huhg ad) as [Hfall Hfone].
  split; intros; spec.
  - intros ?. omicron; eauto using nhg_preservation_none.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split; intros; omicron;
    eauto using nhg_preservation_none, hg_preservation_none.
Qed.

Local Lemma uhg_preservation_alloc : forall m ths tid t T R,
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  unique_holding (m +++ new_cell T R) ths[tid <- t].
Proof.
  intros *.
  intros ? Huhg ? ad. specialize (Huhg ad) as [Hfall Hfone].
  split; intros; upsilon; spec.
  - intros ?. omicron; eauto using nhg_preservation_alloc.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nhg_preservation_alloc, hg_preservation_alloc.
Qed.

Local Lemma uhg_preservation_init : forall m ths tid t ad' t',
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_init ad' t']--> t ->
  unique_holding m[ad'.t <- t'] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Huhg ? ad. specialize (Huhg ad) as [Hfall Hfone].
  assert (ad' < #m) by eauto using vtm_init_address.
  split; intros; omicron; upsilon; spec; solve
    [ intro; omicron; eauto using nhg_preservation_init
    | specialize Hfone as [tid' [? ?]]; exists tid';
      split; intros; omicron;
      eauto using nhg_preservation_init, hg_preservation_init
    ].
Qed.

Local Lemma uhg_preservation_read : forall m ths tid t ad te,
  value te ->
  valid_term m te ->
  (* --- *)
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_read ad te]--> t ->
  unique_holding m ths[tid <- t].
Proof.
  intros until 2.
  intros ? Huhg ? ad'. specialize (Huhg ad') as [Hfall Hfone].
  split; intros; upsilon; spec.
  - intros ?. omicron; eauto using nhg_preservation_read.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nhg_preservation_read, hg_preservation_read.
Qed.

Local Lemma uhg_preservation_write : forall m ths tid t ad te,
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_write ad te]--> t ->
  unique_holding m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Huhg ? ad'. specialize (Huhg ad') as [Hfall Hfone].
  assert (ad < #m) by eauto using vtm_write_address.
  split; intros; repeat omicron; spec; upsilon;
  eauto using nhg_unit, nhg_preservation_write;
  specialize Hfone as [tid' [? ?]]; exists tid'; split; intros;
  omicron; eauto using nhg_preservation_write, hg_preservation_write.
Qed.

Local Lemma uhg_preservation_acq : forall m ths tid ad t te,
  value te ->
  valid_term m te ->
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_waits WR_none) ->
  (* --- *)
  m[ad].X = false ->
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  unique_holding m[ad.X <- true] ths[tid <- t].
Proof.
  intros until 5.
  intros ? Huhg ? ad'. specialize (Huhg ad') as [Hfall Hfone].
  assert (ad < #m) by eauto using vtm_acq_address.
  split; intros; repeat omicron; spec; upsilon;
  eauto using nhg_unit, nhg_preservation_acq.
  - exists tid. sigma. split.
    + split.
      * specialize (Hfall tid) as [? | [? ?]].
        ** eauto using nocrs_from_value, nocr_to_onecr.
        ** exfalso. eauto using wg_effect_contradiction.
      * specialize (Hfall tid) as [? | [? ?]].
        ** eauto using noreacq_from_value, noreacq_preservation_acq,
            noreacq_from_nocr.
        ** exfalso. eauto using wg_effect_contradiction.
    + intros. sigma. eauto.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split.
    + omicron; eauto using hg_preservation_acq.
    + intros. omicron; eauto using nhg_preservation_acq.
Qed.

Local Lemma uhg_preservation_rel : forall m ths tid ad t,
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_rel ad]--> t ->
  unique_holding m[ad.X <- false] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Huhg ? ad'. destruct (Huhg ad') as [Hfall Hfone].
  assert (Had : m[ad].X = true) by eauto using locked_from_rel.
  split; intros; try intros tid'; repeat omicron; spec; upsilon;
  auto; eauto using nhg_preservation_rel;
  specialize Hfone as [tid'' [Hholding Hnholding]].
  - destruct Hholding. nat_eq_dec tid'' tid'.
    + left. eauto using onecr_to_nocr.
    + specialize (Hnholding tid'). spec. destruct Hnholding as [? | [? ?]];
      exfalso; eauto using nocr_rel_contradiction, wg_effect_contradiction.
  - nat_eq_dec tid'' tid'; auto.
    specialize (Hnholding tid). spec. destruct Hnholding as [? | [? ?]];
    exfalso; eauto using nocr_rel_contradiction, wg_effect_contradiction.
  - exists tid''. nat_eq_dec tid'' tid; sigma;
    split; eauto using hg_preservation_rel; intros.
    + sigma. auto.
    + omicron; eauto using nhg_preservation_rel.
Qed.

Local Lemma uhg_preservation_wacq : forall m ths tid t ad,
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_waits WR_none) ->
  (* --- *)
  m[ad].X = false ->
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_wacq ad]--> t ->
  unique_holding m[ad.X <- true] ths[tid <- t].
Proof.
  intros until 3.
  intros ? Huhg ? ad'. specialize (Huhg ad') as [Hfall Hfone].
  assert (ad < #m) by eauto using vtm_wacq_address.
  split; intros; repeat omicron; spec; upsilon;
  eauto using nhg_unit, nhg_preservation_wacq.
  - exists tid. sigma. split.
    + split.
      * specialize (Hfall tid) as [? | [? ?]].
        ** exfalso. eauto using noreacq_from_nocr, noreacq_wacq_contradiction.
        ** eauto using onecr_preservation_wacq.
      * specialize (Hfall tid) as [? | [? ?]].
        ** eauto using nocr_preservation_wacq, cw_preservation_wacq,
            noreacq_from_nocr.
        ** eauto using wg_to_noreacq.
    + intros. sigma. eauto.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split.
    + omicron; eauto using hg_preservation_wacq.
    + intros. omicron; eauto using nhg_preservation_wacq.
Qed.

Local Lemma uhg_preservation_wrel : forall m ths tid ad t,
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_waits WR_none) ->
  (* --- *)
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_wrel ad]--> t ->
  unique_holding m[ad.X <- false] ths[tid <- t].
Proof.
  intros until 2.
  intros ? Huhg ? ad'. destruct (Huhg ad') as [Hfall Hfone].
  assert (Had : m[ad].X = true) by eauto using locked_from_wrel.
  split; intros; try intros tid'; repeat omicron; spec; upsilon;
  auto; eauto using nhg_preservation_wrel;
  specialize Hfone as [tid'' [Hhg Hnhg]].
  - destruct Hhg. nat_eq_dec tid'' tid'.
    + right. split; eauto using onecr_preservation_wrel, noreacq_to_wg.
    + specialize (Hnhg tid'). spec. exfalso. destruct Hnhg as [? | [? ?]];
      eauto using nocr_wrel_contradiction, wg_effect_contradiction.
  - nat_eq_dec tid'' tid'; auto.
    destruct Hhg. specialize (Hnhg tid). spec. exfalso.
    destruct Hnhg as [? | [? ?]];
    eauto using nocr_wrel_contradiction, wg_effect_contradiction.
  - exists tid''. nat_eq_dec tid'' tid; sigma;
    split; eauto using hg_preservation_wrel; intros.
    + sigma. auto.
    + omicron; eauto using nhg_preservation_wrel.
Qed.

Local Ltac eapply_in_tstep tt :=
  match goal with Htstep : _ --[_]--> _ |- _ => eapply tt in Htstep as ? end.

Local Lemma uhg_preservation_spawn : forall m ths tid t t',
  forall_threads ths (valid_term m) ->
  (* --- *)
  tid < #ths ->
  unique_holding m ths ->
  ths[tid] --[e_spawn t']--> t ->
  unique_holding m (ths[tid <- t] +++ t').
Proof.
  intros until 1.
  intros ? Huhg ? ad'. destruct (Huhg ad') as [Hfall Hfone].
  split; intros; spec.
  - intro. omicron;
    eauto using nhg_preservation_spawn, nhg_unit.
    left. eauto using nocr_spawn_term.
  - specialize Hfone as [tid' [Hholding Hnholding]]. exists tid'. split.
    + omicron; eauto.
      * eauto using hg_preservation_spawn.
      * destruct Hholding. invc_onecr.
    + intros. omicron; eauto using nhg_preservation_spawn, nhg_unit.
      left. eauto using nocr_spawn_term.
Qed.

Theorem uhg_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value                ->
  forall_program m1 ths1 (valid_term m1) ->
  forall_program m1 ths1 (consistent_waits WR_none) ->
  (* --- *)
  unique_holding m1 ths1 ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  unique_holding m2 ths2.
Proof.
  intros * ? [? ?] [? ?] **. invc_cstep; try invc_mstep.
  - eauto using uhg_preservation_none.
  - sigma. upsilon. eauto using uhg_preservation_alloc.
  - eauto using uhg_preservation_init.
  - eauto using uhg_preservation_read.
  - eauto using uhg_preservation_write.
  - eauto using uhg_preservation_acq.
  - eauto using uhg_preservation_rel.
  - eauto using uhg_preservation_wacq.
  - eauto using uhg_preservation_wrel.
  - eauto using uhg_preservation_spawn.
Qed.

Theorem uhg_preservation_base : forall t,
  no_crs t ->
  (* --- *)
  unique_holding nil (base t).
Proof.
  unfold base. intros ** ?. split; intros Hnil.
  - intro. left. omicron; auto using no_cr.
  - simpl in Hnil. destruct ad; upsilon; auto.
Qed.

