From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Invariants.

(* ------------------------------------------------------------------------- *)
(* holding inheritance                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma holding_inheritance_cstep :
  forall ad m1 m2 ths1 ths2 tid tid' e,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    holding ad ths2[tid]               ->
    m1 \ ths1 ~~[tid', e]~~> m2 \ ths2 ->
    (  is_acquire ad e -> tid = tid') /\
    (~ is_acquire ad e -> holding ad ths1[tid]).
Proof.
  intros * ? ? Hhg **.
  assert (forall_memory m1 value) by eauto with inva.
  assert (forall_memory m1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (consistent_waits WR_none)) by eauto with inva.
  assert (mutual_exclusion m1 ths1) by eauto with inva.
  assert (mutual_exclusion m2 ths2) by eauto with inva.
  assert (forall_threads ths1 term_init_cr_exc) by eauto with inva.
  assert (H' : forall_threads ths2 term_init_cr_exc) by eauto with inva.
  invc_cstep; try invc_mstep; split;
  try solve [intros [[? F] | F]; invc F].
  - intro. omicron; eauto using hg_inheritance_none.
  - intro. omicron; eauto using hg_inheritance_alloc.
  - intro. omicron; eauto using hg_inheritance_init.
  - intro. omicron; eauto using hg_inheritance_read.
  - intro. omicron; eauto using hg_inheritance_write.
  - intros [[? Heq] | Heq]; invc Heq.
    omicron; trivial.
    specialize (H' tid'). sigma.
    assert (no_cr ad ths1[tid']) by eauto using nocr_from_acq.
    assert (no_reacq ad ths1[tid']) by eauto using noreacq_from_nocr1.
    assert (one_cr ad t) by eauto using nocrs_from_value, nocr_to_onecr.
    assert (no_reacq ad t)
      by eauto using noreacq_from_value, noreacq_preservation_acq.
    assert (holding ad ths1[tid' <- t][tid])  by (sigma; trivial).
    assert (holding ad ths1[tid' <- t][tid']) by (sigma; split; trivial).
    exfalso. eauto using holding_exclusivity.
  - intros Hisacq.
    assert (ad <> ad') by (intro; subst; apply Hisacq; left; eauto).
    omicron; eauto using hg_inheritance_acq.
  - intro. omicron; trivial. nat_eq_dec ad' ad; eauto using hg_inheritance_rel.
    destruct Hhg. exfalso.
    eauto using onecr_from_rel, onecr_to_nocr, nocr_onecr_contradiction.
  - intros [[? Heq] | Heq]; invc Heq.
    omicron; trivial.
    assert (one_cr ad ths1[tid']) by eauto using onecr_from_wacq.
    assert (one_cr ad t) by eauto using onecr_preservation_wacq.
    assert (no_reacq ad t) by eauto using noreacq_from_wacq.
    assert (holding ad ths1[tid' <- t][tid])  by (sigma; trivial).
    assert (holding ad ths1[tid' <- t][tid']) by (sigma; split; trivial).
    exfalso. eauto using holding_exclusivity.
  - intros Hisacq.
    assert (ad <> ad') by (intro; subst; apply Hisacq; right; reflexivity).
    omicron; eauto using hg_inheritance_wacq.
  - intro. omicron; eauto using hg_inheritance_wrel.
  - intro. omicron; eauto using hg_inheritance_spawn.
    exfalso. eauto using hg_inheritance_spawned.
Qed.

(* ------------------------------------------------------------------------- *)
(* initialized preservation                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma initialized_preservation_cstep : forall m1 m2 ths1 ths2 tid e ad t,
  m1[ad].t = Some t                 ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  exists t', m2 [ad].t = Some t'.
Proof.
  intros.
  assert (ad < #m1) by (lt_eq_gt ad (#m1); sigma; upsilon; eauto).
  invc_cstep; try invc_mstep; sigma; eauto;
  omicron; upsilon; eauto.
Qed.

Lemma initialized_preservation_ustep : forall m1 m2 ths1 ths2 tc ad t,
  m1[ad].t = Some t              ->
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  exists t', m2 [ad].t = Some t'.
Proof.
  intros. ind_ustep; eauto.
  destruct IHmultistep; trivial.
  eauto using initialized_preservation_cstep.
Qed.

(* ------------------------------------------------------------------------- *)
(* one-init preservation                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma oneinit_preservation_cstep :
  forall ad m1 m2 ths1 ths2 tid tid' e,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_init ad ths1[tid]              ->
    m1 \ ths1 ~~[tid', e]~~> m2 \ ths2 ->
     (forall t, e <> e_init ad t /\ one_init ad ths2[tid]) \/
     (exists t, e =  e_init ad t /\ tid' = tid /\ m2[ad].t = Some t).
Proof.
  intros.
  assert (forall_memory m1 value) by eauto with inva.
  assert (forall_memory m1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (consistent_term m1)) by eauto with inva.
  assert (unique_initializers m1 ths1) by eauto with inva.
  invc_cstep; try invc_mstep.
  - left. intros. split; eauto.
    omicron; eauto using oneinit_preservation_none.
  - left. split; try omicron; auto; try congruence.
    assert (ad < #m1) by eauto using oneinit_ad_bound.
    eauto using oneinit_preservation_alloc.
  - match goal with _ : _ --[e_init ?x _]--> _ |- _ => rename x into ad' end.
    nat_eq_dec ad' ad.
    + assert (ad < #m1) by eauto using vtm_init_address.
      right. repeat eexists; sigma; upsilon; trivial.
      eauto using oneinit_from_init, ui_oneinit_equality.
    + left. intros. split; auto.
      omicron; eauto using oneinit_preservation_init.
  - left. split; auto; try congruence.
    omicron; eauto using noinits_from_value, oneinit_preservation_read.
  - left. split; auto; try congruence.
    omicron; eauto using oneinit_preservation_write.
  - left. split; auto.
    omicron; eauto using noinits_from_value, oneinit_preservation_acq.
  - left. split; auto.
    omicron; eauto using oneinit_preservation_rel.
  - left. split; auto; try congruence.
    omicron; eauto using oneinit_preservation_wacq.
  - left. split; auto; try congruence.
    omicron; eauto using oneinit_preservation_wrel.
  - left. split; auto; try congruence.
    omicron; eauto using oneinit_preservation_spawn.
    invc_oneinit.
Qed.

Lemma oneinit_preservation_ustep :
  forall tc m1 m2 ths1 ths2 ad tid,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_init ad ths1[tid]          ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_init ad ths2[tid] \/ exists t, m2[ad].t = Some t.
Proof.
  intros. ind_ustep; auto.
  match goal with _ : ?m \ ?ths ~~[?tid, _]~~> ?m' \ ?ths' |- _ =>
    rename tid into tid';
    rename m' into m3; rename ths' into ths3;
    rename m  into m2; rename ths  into ths2
  end.
  assert (invariants m2 ths2) by eauto using invariants_preservation_ustep.
  destruct IHmultistep as [? | [? ?]]; trivial.
  - assert (
      (forall t, e <> e_init ad t /\ one_init ad ths3[tid]) \/
      (exists t, e =  e_init ad t /\ tid' = tid /\ m3[ad].t = Some t)
    ) as [H' | [t' [? [? ?]]]]
      by eauto using oneinit_preservation_cstep.
    + specialize (H' <{unit}>) as [? ?]. eauto.
    + subst. eauto.
  - right. eauto using initialized_preservation_cstep.
Qed.

(* ------------------------------------------------------------------------- *)
(* holding preservation                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma holding_preservation_cstep :
  forall ad m1 m2 ths1 ths2 tid tid' e,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    holding ad ths1[tid]               ->
    m1 \ ths1 ~~[tid', e]~~> m2 \ ths2 ->
    (  is_release ad e -> tid = tid') /\
    (~ is_release ad e -> holding ad ths2[tid]).
Proof.
  intros * ? ? Hhg Hcstep.
  assert (forall_memory m1 value) by eauto with inva.
  assert (forall_memory m1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (consistent_waits WR_none)) by eauto with inva.
  assert (mutual_exclusion m1 ths1) by eauto with inva.
  assert (forall_threads ths1 term_init_cr_exc) by eauto with inva.
  assert (Htice : forall_threads ths2 term_init_cr_exc) by eauto with inva.
  invc_cstep; try invc_mstep; split; try solve [intros [F | F]; invc F].
  - intros _. omicron; trivial. eauto using hg_preservation_none.
  - intros _. omicron; trivial. eauto using hg_preservation_alloc.
  - intros _. omicron; trivial. eauto using hg_preservation_init.
  - intros _. omicron; trivial. eauto using hg_preservation_read.
  - intros _. omicron; trivial. eauto using hg_preservation_write.
  - intros _. omicron; trivial.
    nat_eq_dec ad' ad; eauto using hg_preservation_acq.
    specialize (Htice tid). sigma. destruct Hhg.
    exfalso. eauto using nocr_from_acq, nocr_onecr_contradiction.
  - intros [Heq | Heq]; invc Heq.
    eauto using holding_from_rel, holding_equality.
  - intros Hisrel. omicron; trivial. nat_eq_dec ad' ad.
    + contradict Hisrel. left. reflexivity.
    + eauto using hg_preservation_rel.
  - intros _. omicron; trivial. eauto using hg_preservation_wacq.
  - intros [Heq | Heq]; invc Heq.
    eauto using holding_from_wrel, holding_equality.
  - intros Hisrel. omicron; trivial. nat_eq_dec ad' ad.
    + contradict Hisrel. right. reflexivity.
    + eauto using hg_preservation_wrel.
  - intros _. omicron; eauto using hg_preservation_spawn.
    destruct Hhg. invc_onecr.
Qed.

