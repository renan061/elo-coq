From Coq Require Import Lists.List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Multistep.
From Elo Require Import SafetyUtil.
From Elo Require Import MemoryRegions.
From Elo Require Import GCR.
From Elo Require Import HappensBefore.
From Elo Require Import SafetyLemmas.
From Elo Require Import SafetyGCR.

(* ------------------------------------------------------------------------- *)

Corollary ptyp_for_write_cstep : forall m1 m2 ths1 ths2 tid ad' t',
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  exists T, m1[ad'].T = `w&T`.
Proof.
  intros. destruct_invariants. invc_cstep. invc_mstep.
  eauto using ptyp_for_write. 
Qed.

Lemma same_pointer_type :
  forall m1 mA mB m2 ths1 thsA thsB ths2 tc tid1 tid2 e1 e2 ad,
    invariants m1 ths1 ->
    (* --- *)
    ad < #m1 ->
    m1 \ ths1 ~~[tid1, e1]~~>  mA \ thsA ->
    mA \ thsA ~~[tc      ]~~>* mB \ thsB ->
    mB \ thsB ~~[tid2, e2]~~>  m2 \ ths2 ->
    (m1[ad].T = mA[ad].T /\ mA[ad].T = mB[ad].T /\ mB[ad].T = m2[ad].T).
Proof.
  intros.
  assert (ad < #mA) by eauto using cstep_nondecreasing_memory_size.
  assert (ad < #mB) by eauto using ustep_nondecreasing_memory_size.
  assert (ad < #m2) by eauto using cstep_nondecreasing_memory_size.
  assert (HtA : m1[ad].T = mA[ad].T) by eauto using ptyp_preservation_cstep.
  assert (HtB : mA[ad].T = mB[ad].T) by eauto using ptyp_preservation_ustep.
  assert (Ht2 : mB[ad].T = m2[ad].T) by eauto using ptyp_preservation_cstep.
  auto.
Qed.

Lemma same_regions :
  forall m1 mA mB m2 ths1 thsA thsB ths2 tc tid1 tid2 e1 e2 ad,
    invariants m1 ths1 ->
    (* --- *)
    ad < #m1 ->
    m1 \ ths1 ~~[tid1, e1]~~>  mA \ thsA ->
    mA \ thsA ~~[tc      ]~~>* mB \ thsB ->
    mB \ thsB ~~[tid2, e2]~~>  m2 \ ths2 ->
    m1[ad].R = mB[ad].R.
Proof.
  intros.
  assert (ad < #mA) by eauto using cstep_nondecreasing_memory_size.
  assert (ad < #mB) by eauto using ustep_nondecreasing_memory_size.
  assert (HrA : m1[ad].R = mA[ad].R) by eauto using mreg_preservation_cstep.
  assert (HrB : mA[ad].R = mB[ad].R) by eauto using mreg_preservation_ustep.
  rewrite HrB in HrA.
  assumption.
Qed.


(* ------------------------------------------------------------------------- *)
(* safety -- final 0                                                         *)
(* ------------------------------------------------------------------------- *)

Local Corollary write_address_cstep : forall m1 m2 ths1 ths2 tid ad' t',
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  ad' < #m1.
Proof.
  intros * H ?.
  eapply des_inva_vtm in H. eapply des_forallprogram_threads in H.
  invc_cstep. invc_mstep. eauto using vtm_write_address.
Qed.

Local Corollary read_address_cstep : forall m1 m2 ths1 ths2 tid ad' t',
  m1 \ ths1 ~~[tid, e_read ad' t']~~> m2 \ ths2 ->
  ad' < #m1.
Proof.
  intros. invc_cstep. invc_mstep.
  lt_eq_gt ad' (#m2); sigma; trivial; discriminate.
Qed.

Lemma todo1 : forall R m t ad,
  valid_term m t ->
  (* -- *)
  R <> R_reacq ad      ->
  gcr t R = R_reacq ad ->
  waiting ad t.
Proof.
  intros. gendep R.
  induction t; intros; invc_vtm; kappa; try discriminate;
  eauto using waiting;
  match goal with
  | H : _ _ (R_ad ?ad) = _          |- _ => spec; specialize (IHt (R_ad ad))
  | H : R_reacq ?ad1 = R_reacq ?ad2 |- _ => invc H
  end;
  auto using waiting with gcr.
Qed.

Lemma todo2 : forall m1 m2 ths1 ths2 tid ad ad' t',
  waiting ad ths1[tid]                           ->
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  False.
Proof.
  intros. invc_cstep. invc_mstep.
  remember (ths1[tid]) as t1. clear Heqt1.
  ind_tstep; repeat invc_wg; auto; (value_does_not_step || value_does_not_wait).
Qed.

Lemma todo2' : forall m1 m2 ths1 ths2 tid ad' t',
  forall_threads ths1 (valid_term m1) ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  no_reacqs ths1[tid].
Proof.
  intros * Hvtm **. invc_cstep. invc_mstep.
  specialize (Hvtm tid).
  remember (ths1[tid]) as t1. clear Heqt1.
  ind_tstep; invc_vtm; try value_does_not_step;
  repeat spec; intro; eauto using noreacq_from_value, no_reacq.
Qed.

Corollary todo3 : forall m1 m2 ths1 ths2 tid ad ad' t',
  forall_threads ths1 (valid_term m1) ->
  (* --- *)
  gcr ths1[tid] (R_tid tid) = R_reacq ad         ->
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  False.
Proof.
  assert (forall tid ad, R_tid tid <> R_reacq ad) by congruence.
  eauto using todo1, todo2.
Qed.

(* ------------------------------------------------------------------------- *)

Local Corollary noreacq_from_write_cstep :
  forall m1 m2 ths1 ths2 tid ad' t' ad,
    invariants m1 ths1 ->
    (* --- *)
    m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
    no_reacq ad ths1[tid].
Proof.
  intros * Hinva **. invc_cstep. invc_mstep. 
  eapply noreacq_from_effect; eauto; eauto.
  eapply des_inva_vtm in Hinva.
  eapply des_forallprogram_threads in Hinva.
  eauto.
Qed.

Local Corollary noreacq_preservation_write_cstep :
  forall m1 m2 ths1 ths2 tid ad' t' ad,
    no_reacq ad ths1[tid]                          ->
    m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
    no_reacq ad ths2[tid].
Proof.
  intros * Hinva **. invc_cstep. invc_mstep. sigma. 
  eauto using noreacq_preservation_write.
Qed.

(* ------------------------------------------------------------------------- *)

Local Corollary noreacq_from_read_cstep :
  forall m1 m2 ths1 ths2 tid ad' t' ad,
    invariants m1 ths1 ->
    (* --- *)
    m1 \ ths1 ~~[tid, e_read ad' t']~~> m2 \ ths2 ->
    no_reacq ad ths1[tid].
Proof.
  intros * Hinva **. invc_cstep. invc_mstep. 
  eapply noreacq_from_effect; eauto; eauto.
  eapply des_inva_vtm in Hinva.
  eapply des_forallprogram_threads in Hinva.
  eauto.
Qed.

Local Corollary noreacq_preservation_read_cstep :
  forall m1 m2 ths1 ths2 tid ad' t' ad,
    forall_memory m1 value           ->
    forall_memory m1 (valid_term m1) ->
    (* --- *)
    no_reacq ad ths1[tid]                         ->
    m1 \ ths1 ~~[tid, e_read ad' t']~~> m2 \ ths2 ->
    no_reacq ad ths2[tid].
Proof.
  intros * ? ? Hinva **. invc_cstep. invc_mstep. sigma. 
  eauto using noreacq_from_value, noreacq_preservation_read.
Qed.

(* ------------------------------------------------------------------------- *)
(* final three                                                               *)
(* ------------------------------------------------------------------------- *)

Theorem safety_write_write : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2                             ->
  tc = <<(tid1, e_write ad t1), tc', (tid2, e_write ad t2)>> ->
  happens_before tc.
Proof.
  intros. subst.
  nat_eq_dec tid1 tid2; eauto using happens_before.

  destruct_ustep2.
  assert (invariants mA thsA) by eauto using invariants_preservation_cstep.
  assert (invariants mB thsB) by eauto using invariants_preservation_ustep.
  assert (invariants m2 ths2) by eauto using invariants_preservation_cstep.

  assert (ad < #m1) by eauto using write_address_cstep.

  assert (exists T, m1[ad].T = `w&T`)
    as [T Hptyp1]
    by eauto using ptyp_for_write_cstep.
  assert (m1[ad].T = mA[ad].T /\ mA[ad].T = mB[ad].T /\ mB[ad].T = m2[ad].T)
    as [HptypA [HptypB Hptyp2]]
    by eauto using same_pointer_type.
  rewrite Hptyp1 in HptypA. symmetry in HptypA.
  rewrite HptypA in HptypB. symmetry in HptypB.
  rewrite HptypB in Hptyp2. symmetry in Hptyp2.

  assert (Hgcr1 : gcr ths1[tid1] (R_tid tid1) = m1[ad].R)
    by eauto 7 using cstep_gcr_write with inva.
  assert (HgcrB : gcr thsB[tid2] (R_tid tid2) = mB[ad].R)
    by eauto 7 using cstep_gcr_write with inva.

  assert (HR : m1[ad].R = mB[ad].R) by eauto using same_regions.
  rewrite <- HR in *.

  destruct (m1[ad].R).
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - erewrite gcr_preservation_write_cstep in Hgcr1; eauto with inva.
    eapply (happens_before_from_gcr mA mB thsA thsB);
    eauto using noreacq_from_write_cstep, noreacq_preservation_write_cstep.
  - exfalso. eauto using todo3 with inva.
Qed.

Theorem safety_write_read : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2                            ->
  tc = <<(tid1, e_write ad t1), tc', (tid2, e_read ad t2)>> ->
  happens_before tc.
Proof.
  intros. subst.
  nat_eq_dec tid1 tid2; eauto using happens_before.

  destruct_ustep2.
  assert (invariants mA thsA) by eauto using invariants_preservation_cstep.
  assert (invariants mB thsB) by eauto using invariants_preservation_ustep.
  assert (invariants m2 ths2) by eauto using invariants_preservation_cstep.

  assert (ad < #m1) by eauto using write_address_cstep.

  assert (exists T, m1[ad].T = `w&T`)
    as [T Hptyp1]
    by eauto using ptyp_for_write_cstep.
  assert (m1[ad].T = mA[ad].T /\ mA[ad].T = mB[ad].T /\ mB[ad].T = m2[ad].T)
    as [HptypA [HptypB Hptyp2]]
    by eauto using same_pointer_type.
  rewrite Hptyp1 in HptypA. symmetry in HptypA.
  rewrite HptypA in HptypB. symmetry in HptypB.
  rewrite HptypB in Hptyp2. symmetry in Hptyp2.

  assert (Hgcr1 : gcr ths1[tid1] (R_tid tid1) = m1[ad].R)
    by eauto 7 using cstep_gcr_write with inva.
  assert (HgcrB : gcr thsB[tid2] (R_tid tid2) = mB[ad].R)
    by eauto using cstep_gcr_read with inva.

  assert (HR : m1[ad].R = mB[ad].R) by eauto using same_regions.
  rewrite <- HR in *.

  destruct (m1[ad].R).
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - erewrite gcr_preservation_write_cstep in Hgcr1; eauto with inva.
    eapply (happens_before_from_gcr mA mB thsA thsB); eauto;
    eauto using noreacq_from_read_cstep;
    eauto using noreacq_from_write_cstep, noreacq_preservation_write_cstep.
  - exfalso. eauto using todo3 with inva.
Qed.

Theorem safety_read_write : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2                            ->
  tc = <<(tid1, e_read ad t1), tc', (tid2, e_write ad t2)>> ->
  happens_before tc.
Proof.
  intros. subst.
  nat_eq_dec tid1 tid2; eauto using happens_before.

  destruct_ustep2.
  assert (invariants mA thsA) by eauto using invariants_preservation_cstep.
  assert (invariants mB thsB) by eauto using invariants_preservation_ustep.
  assert (invariants m2 ths2) by eauto using invariants_preservation_cstep.

  assert (ad < #m1) by eauto using read_address_cstep.

  assert (exists T, mB[ad].T = `w&T`)
    as [T HptypB]
    by eauto using ptyp_for_write_cstep.
  assert (m1[ad].T = mA[ad].T /\ mA[ad].T = mB[ad].T /\ mB[ad].T = m2[ad].T)
    as [Hptyp1 [HptypA Hptyp2]]
    by eauto using same_pointer_type.
  rewrite HptypB in HptypA.
  rewrite HptypA in Hptyp1.
  rewrite HptypB in Hptyp2.
  symmetry in Hptyp2.

  assert (Hgcr1 : gcr ths1[tid1] (R_tid tid1) = m1[ad].R)
    by eauto using cstep_gcr_read with inva.
  assert (HgcrB : gcr thsB[tid2] (R_tid tid2) = mB[ad].R)
    by eauto 7 using cstep_gcr_write with inva.

  assert (HR : m1[ad].R = mB[ad].R) by eauto using same_regions.
  rewrite <- HR in *.

  destruct (m1[ad].R).
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - erewrite (gcr_preservation_read_cstep m1 mA ths1 thsA) in Hgcr1;
    eauto with inva.
    eapply (happens_before_from_gcr mA mB thsA thsB); eauto;
    eauto using noreacq_from_write_cstep.
    eapply (noreacq_preservation_read_cstep m1 mA ths1 thsA); eauto with inva.
    eauto using noreacq_from_read_cstep.
  - exfalso. eauto using todo3 with inva.
Qed.

