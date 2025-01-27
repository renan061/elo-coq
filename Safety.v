From Coq Require Import Lists.List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Invariants.
From Elo Require Import GCR.
From Elo Require Import SafetyLemmas.
From Elo Require Import SafetyUtil.
From Elo Require Import HappensBefore.

(* ------------------------------------------------------------------------- *)
(* auxiliary - address                                                       *)
(* ------------------------------------------------------------------------- *)

Local Corollary read_address_cstep : forall m1 m2 ths1 ths2 tid ad' t',
  m1 \ ths1 ~~[tid, e_read ad' t']~~> m2 \ ths2 ->
  ad' < #m1.
Proof.
  intros. invc_cstep. invc_mstep.
  lt_eq_gt ad' (#m2); sigma; trivial; discriminate.
Qed.

Local Corollary write_address_cstep : forall m1 m2 ths1 ths2 tid ad' t',
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  ad' < #m1.
Proof.
  intros * Hinva ?.
  eapply des_inva_vtm in Hinva. eapply des_forallprogram_threads in Hinva.
  invc_cstep. invc_mstep. eauto using vtm_write_address.
Qed.

(* ------------------------------------------------------------------------- *)
(* auxiliary - pointer types                                                 *)
(* ------------------------------------------------------------------------- *)

Local Corollary same_pointer_type :
  forall m1 mA mB m2 ths1 thsA thsB ths2 tc tid1 tid2 e1 e2 ad,
    invariants m1 ths1 ->
    (* --- *)
    ad < #m1                             ->
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

Local Corollary ptyp_for_write_cstep : forall m1 m2 ths1 ths2 tid ad' t',
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  exists T, m1[ad'].T = `w&T`.
Proof.
  intros. destruct_invariants. invc_cstep. invc_mstep.
  eauto using ptyp_for_write. 
Qed.

Local Corollary pointer_type_at_P1 :
  forall m1 m2 mA mB ths1 ths2 thsA thsB tid1 tid2 tc ad t1 t2,
    invariants m1 ths1 ->
    invariants mB thsB ->
    (* --- *)
    m1 \ ths1 ~~[tid1, e_read  ad t1]~~>  mA \ thsA ->
    mA \ thsA ~~[tc                 ]~~>* mB \ thsB ->
    mB \ thsB ~~[tid2, e_write ad t2]~~>  m2 \ ths2 ->
    exists T, m1[ad].T = `w&T`.
Proof.
  intros.
  assert (ad < #m1) by eauto using read_address_cstep.
  assert (exists T, mB[ad].T = `w&T`)
    as [T HptypB]
    by eauto using ptyp_for_write_cstep.
  assert (m1[ad].T = mA[ad].T /\ mA[ad].T = mB[ad].T /\ mB[ad].T = m2[ad].T)
    as [Hptyp1 [HptypA _]]
    by eauto using same_pointer_type.
  rewrite HptypB in HptypA.
  rewrite HptypA in Hptyp1.
  eauto.
Qed.

Local Corollary pointer_type_at_PB :
  forall m1 m2 mA mB ths1 ths2 thsA thsB tid1 tid2 tc ad t1 t2,
    invariants m1 ths1 ->
    invariants mB thsB ->
    (* --- *)
    m1 \ ths1 ~~[tid1, e_write ad t1]~~>  mA \ thsA ->
    mA \ thsA ~~[tc                 ]~~>* mB \ thsB ->
    mB \ thsB ~~[tid2, e_read  ad t2]~~>  m2 \ ths2 ->
    exists T, mB[ad].T = `w&T`.
Proof.
  intros.
  assert (ad < #m1) by eauto using write_address_cstep.
  assert (exists T, m1[ad].T = `w&T`)
    as [T Hptyp1]
    by eauto using ptyp_for_write_cstep.
  assert (m1[ad].T = mA[ad].T /\ mA[ad].T = mB[ad].T /\ mB[ad].T = m2[ad].T)
    as [HptypA [Hptyp2 _]]
    by eauto using same_pointer_type.
  rewrite Hptyp2 in HptypA.
  rewrite HptypA in Hptyp1.
  eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* auxiliary - regions                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma mreg_preservation_cstep : forall m1 m2 ths1 ths2 tid e ad,
  ad < #m1                          ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  m1[ad].R = m2[ad].R.
Proof.
  intros. invc_cstep; trivial; invc_mstep; sigma; trivial; omicron; trivial.
Qed.

Local Corollary mreg_preservation_ustep : forall m1 m2 ths1 ths2 tc ad,
  ad < #m1                       ->
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  m1[ad].R = m2[ad].R.
Proof.
  intros. ind_ustep; trivial. rewrite IHmultistep;
  eauto using ustep_nondecreasing_memory_size, mreg_preservation_cstep.
Qed.

Local Lemma same_regions :
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
(* auxiliary - no-reacq                                                      *)
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
  intros. invc_cstep. invc_mstep. sigma.
  eauto using noreacq_preservation_write.
Qed.

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
    invariants m1 ths1 ->
    (* --- *)
    no_reacq ad ths1[tid]                         ->
    m1 \ ths1 ~~[tid, e_read ad' t']~~> m2 \ ths2 ->
    no_reacq ad ths2[tid].
Proof.
  intros.
  assert (forall_memory m1 value) by eauto with inva.
  assert (forall_memory m1 (valid_term m1)) by eauto with inva.
  invc_cstep. invc_mstep. sigma. 
  eauto using noreacq_from_value, noreacq_preservation_read.
Qed.

(* ------------------------------------------------------------------------- *)
(* safety                                                                    *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_safety H1A HAB HB2 :=
  (* Given the step relations. *)
  match type of H1A with | ?m1 \ ?ths1 ~~[?tid1, ?e1 ?ad _]~~>  ?mA \ ?thsA =>
  match type of HAB with | ?mA \ ?thsA ~~[?tc             ]~~>* ?mB \ ?thsB =>
  match type of HB2 with | ?mB \ ?thsB ~~[?tid2, ?e2 ?ad _]~~>  ?m2 \ ?ths2 =>

    (* Asserts the invariants for PA, PB, and P2. *)
    assert (invariants mA thsA) by eauto using invariants_preservation_cstep;
    assert (invariants mB thsB) by eauto using invariants_preservation_ustep;
    assert (invariants m2 ths2) by eauto using invariants_preservation_cstep;

    (* Analyzes the first effect. *)
    match e1 with
    | e_read =>
      (* If the first effect is a READ, asserts the pointer type. *)
      (* Lemma cstep_gcr_read requires it. *)
      assert (exists T, m1[ad].T = `w&T`) as [T ?]
        by eauto using pointer_type_at_P1;
      (* Then gets the current region for P1. *)
      assert (HgcrA : gcr ths1[tid1] (R_tid tid1) = m1[ad].R)
        by eauto using cstep_gcr_read with inva;
      (* And for PA by preservation. *)
      erewrite (gcr_preservation_read_cstep m1 mA ths1 thsA) in HgcrA;
      eauto with inva
    | e_write =>
      (* If the first effect is a WRITE, gets the current region for P1. *)
      assert (HgcrA : gcr ths1[tid1] (R_tid tid1) = m1[ad].R)
        by eauto 7 using cstep_gcr_write with inva;
      (* And for PA by preservation. *)
      erewrite gcr_preservation_write_cstep in HgcrA; eauto with inva
    end;

    (* Analyzes the second effect. *)
    match e2 with
    | e_read =>
      (* If the second effect is a READ, asserts the pointer type. *)
      (* Lemma cstep_gcr_read requires it. *)
      assert (exists T, mB[ad].T = `w&T`) as [T ?]
        by eauto using pointer_type_at_PB;
      (* Then gets the current region for PB. *)
      assert (HgcrB : gcr thsB[tid2] (R_tid tid2) = mB[ad].R)
        by eauto using cstep_gcr_read with inva
    | e_write =>
      (* If the second effect is a WRITE, gets the current region for PB. *)
      assert (HgcrB : gcr thsB[tid2] (R_tid tid2) = mB[ad].R)
        by eauto 7 using cstep_gcr_write with inva
    end;

    (* Asserts both PA and PB are in the same region. *)
    assert (HR : m1[ad].R = mB[ad].R)
      by eauto using read_address_cstep, write_address_cstep, same_regions;
    rewrite <- HR in *;

    (* Analyzes the region in which PA and PB are in. *)
    destruct (m1[ad].R);
    (* A thread cannot be in an invalid region. *)
    try solve [exfalso; eauto using gcr_invalid_contradiction];
    (* Two different threads cannot be in the same thread region. *)
    try solve [exfalso; eauto using gcr_tid_contradiction];

    (* The two threads are in a monitored region. *)
    eapply (happens_before_from_gcr mA mB thsA thsB); eauto
  end
  end
  end.

Theorem safety_write_write : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2                             ->
  tc = <<(tid1, e_write ad t1), tc', (tid2, e_write ad t2)>> ->
  happens_before tc.
Proof.
  intros. subst.
  nat_eq_dec tid1 tid2; eauto using happens_before. destruct_ustep2.
  solve_safety H1A HAB HB2;
  eauto using noreacq_from_write_cstep, noreacq_preservation_write_cstep.
Qed.

Theorem safety_write_read : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2                            ->
  tc = <<(tid1, e_write ad t1), tc', (tid2, e_read ad t2)>> ->
  happens_before tc.
Proof.
  intros. subst.
  nat_eq_dec tid1 tid2; eauto using happens_before. destruct_ustep2.
  solve_safety H1A HAB HB2;
  eauto using noreacq_from_write_cstep, noreacq_preservation_write_cstep.
  eauto using noreacq_from_read_cstep.
Qed.

Theorem safety_read_write : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2                            ->
  tc = <<(tid1, e_read ad t1), tc', (tid2, e_write ad t2)>> ->
  happens_before tc.
Proof.
  intros. subst.
  nat_eq_dec tid1 tid2; eauto using happens_before. destruct_ustep2.
  solve_safety H1A HAB HB2;
  eauto using noreacq_from_write_cstep.
  eauto using noreacq_from_read_cstep, noreacq_preservation_read_cstep.
Qed.

