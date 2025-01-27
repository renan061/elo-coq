From Coq Require Import Lists.List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Multistep.
From Elo Require Import MemoryRegions.
From Elo Require Import GCR.
From Elo Require Import HappensBefore.
From Elo Require Import SafetyLemmas.

Local Lemma in_app_head : forall {A} (l : list A) (a : A),
  In a (l ++ a :: nil).
Proof.
  intros. induction l; simpl; eauto.
Qed.

Local Lemma in_app_tail : forall {A} (l : list A) (a a' : A),
  In a l ->
  In a (l ++ a' :: nil).
Proof.
  intros. induction l; simpl in *; auto.
  match goal with H : _ \/ _ |- _ => destruct H end; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Ltac destruct_invariants :=
  repeat match goal with
  | H : invariants _ _       |- _ =>
    unfold invariants in H; decompose record H; clear H
  | H : forall_program _ _ _ |- _ =>
    destruct H
  end.

Corollary cstep_ptyp_for_write : forall m1 m2 ths1 ths2 tid ad' t',
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  exists T, m1[ad'].T = `w&T`.
Proof.
  intros. destruct_invariants. invc_cstep. invc_mstep.
  eauto using  ptyp_for_write. 
Qed.

Local Lemma same_pointer_type :
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
(* destructs                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Lemma _destruct_ustep2 : forall tc m1 m3 ths1 ths3 tid e,
  m1 \ ths1 ~~[tc +++ (tid, e)]~~>* m3 \ ths3 ->
  (exists m2 ths2,
    m1 \ ths1 ~~[tid, e]~~>  m2 \ ths2 /\
    m2 \ ths2 ~~[tc    ]~~>* m3 \ ths3 ).
Proof.
  intros ?. induction tc; intros; invc_ustep.
  - invc_ustep. eauto using multistep.
  - match goal with Hustep : _ \ _ ~~[ _ ]~~>* _ \ _ |- _ => 
      decompose record (IHtc _ _ _ _ _ _ Hustep); eauto using multistep
    end.
Qed.

Ltac destruct_ustep2 :=
  match goal with
  | H : _ \ _  ~~[_ +++ (_, _)]~~>* _ \ _ |- _ =>
    eapply _destruct_ustep2 in H as [? [? [? ?]]]
  end.

Local Lemma _destruct_ustep3 : forall tc m1 m4 ths1 ths4 tid1 tid2 e1 e2,
  m1 \ ths1 ~~[(tid2, e2) :: tc +++ (tid1, e1)]~~>* m4 \ ths4 ->
  (exists m2 ths2 m3 ths3,
    m1 \ ths1 ~~[tid1, e1]~~>  m2 \ ths2 /\
    m2 \ ths2 ~~[tc      ]~~>* m3 \ ths3 /\
    m3 \ ths3 ~~[tid2, e2]~~>  m4 \ ths4 ).
Proof.
  intros. invc_ustep. destruct_ustep2. do 4 eexists. repeat split; eauto.
Qed.

Ltac destruct_ustep3 :=
  match goal with 
  | H : _ \ _ ~~[(_, _) :: _ +++ (_, _)]~~>* _ \ _ |- _ =>
    eapply _destruct_ustep3 in H
      as [mA [thsA [mB [thsB [H1A [HAB HB2]]]]]]
  end.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma destruct_ustep' : forall m1 m2 ths1 ths2 tc1 tc2 tid e,
  m1 \ ths1 ~~[tc2 ++ (tid, e) :: tc1]~~>* m2 \ ths2 ->
  exists mA mB thsA thsB,
    m1 \ ths1 ~~[tc1   ]~~>* mA \ thsA /\
    mA \ thsA ~~[tid, e]~~>  mB \ thsB /\
    mB \ thsB ~~[tc2   ]~~>* m2 \ ths2.
Proof.
  intros.
  gendep ths2. gendep ths1. gendep m2. gendep m1. gendep e. gendep tid.
  induction tc2; intros.
  - rewrite app_nil_l in *. invc_ustep. repeat eexists; eauto using multistep.
  - invc_ustep.
    match goal with H : _ \ _ ~~[_]~~>* _ \ _ |- _ =>
      decompose record (IHtc2 _ _ _ _ _ _ H)
    end.
    repeat eexists; eauto using multistep.
Qed.

(* ------------------------------------------------------------------------- *)
(* one-init ~~>* one-init                                                    *)
(* ------------------------------------------------------------------------- *)

Local Lemma oneinit_multistep_oneinit :
  forall tc m1 m2 ths1 ths2 tid1 tid2 ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_init ad ths1[tid1]         ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_init ad ths2[tid2]         ->
    False.
Proof.
  intros.
  assert (one_init ad ths2[tid1] \/ exists t, m2[ad].t = Some t)
    as [? | [? Hsome]]
    by eauto using oneinit_preservation_ustep.
  - assert (forall_threads ths2 (valid_term m2)) by eauto with inva.
    assert (Hui : unique_initializers m2 ths2) by eauto with inva.
    assert (Had : ad < #m2) by eauto using oneinit_ad_bound.
    eauto using ui_oneinit_contradiction. 
  - assert (forall_threads ths2 (consistent_term m2)) by eauto with inva.
    assert (Hnone : m2[ad].t = None) by eauto using oneinit_then_uninitialized.
    rewrite Hnone in Hsome. auto.
Qed.

(* ------------------------------------------------------------------------- *)
(* one-init ~~>* one-cr                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma oneinit_multistep_holding_requires_acquire' :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_init ad ths1[tid1]         ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    holding ad ths2[tid2]          ->
    exists e, In (tid2, e) tc /\ is_acquire ad e.
Proof.
  intros * ? ? ? ? ? Hhg. ind_ustep.
  - exfalso. destruct Hhg.
    assert (Hice : init_cr_exclusivity ths) by eauto with inva.
    specialize (Hice ad tid1 tid2) as [? _].
    eauto using nocr_onecr_contradiction.
  - assert (invariants m2 ths2) by eauto using invariants_preservation_ustep.
    repeat spec.
    assert ((  is_acquire ad e -> tid2 = tid) /\
            (~ is_acquire ad e -> holding ad ths2[tid2]))
      as [? Hnot]
      by eauto using holding_inheritance_cstep.
      destruct (isacquire_dec ad e) as [Hisacq | ?]; repeat spec.
      + subst. eexists. split; eauto. left. reflexivity.
      + decompose record IHmultistep. simpl. eexists. split; eauto.
Qed.

Local Corollary oneinit_multistep_holding_requires_acquire :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_init ad ths1[tid1]         ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    holding ad ths2[tid2]          ->
    exists e tc1 tc2, is_acquire ad e /\ tc = tc2 ++ (tid2, e) :: tc1.
Proof.
  intros.
  assert (exists e, In (tid2, e) tc /\ is_acquire ad e)
    as [e [Hin ?]] by eauto using oneinit_multistep_holding_requires_acquire'.
  apply in_split in Hin as [tc2 [tc1 Htc]].
  exists e. exists tc1. exists tc2. split; assumption.
Qed.

Local Corollary multistep_acquire_requires_initialized :
  forall m1 m2 ths1 ths2 tid1 tid2 tc1 tc2 ad e,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                                        ->
    is_acquire ad e                                     ->
    m1 \ ths1 ~~[tc2 ++ (tid2, e) :: tc1]~~>* m2 \ ths2 ->
    exists mA thsA t,
      m1 \ ths1 ~~[tc1]~~>* mA \ thsA /\
      mA[ad].t = Some t.
Proof.
  intros * ? ? ? Hisacq Hcstep.
  eapply destruct_ustep' in Hcstep.
  destruct Hcstep as [mA [mB [thsA [thsB [? [? ?]]]]]].
  assert (invariants mA thsA) by eauto using invariants_preservation_ustep .
  destruct Hisacq as  [[? ?] | ?]; subst; invc_cstep; invc_mstep; eauto.
  assert (exists t, mA[ad].t = Some t) as [? ?]
    by (eapply initialized_from_wacq; eauto with inva).
  eauto.
Qed.

Local Lemma oneinit_multistep_initialized_requires_init :
  forall tc m1 m2 ths1 ths2 tid ad t,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_init ad ths1[tid] ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    m2[ad].t = Some t ->
    exists t, In (tid, e_init ad t) tc.
Proof.
  intro. induction tc using rev_ind; intros.
  - invc_ustep.
    assert (Hui : unique_initializers m2 ths2) by eauto with inva.
    assert (ad < #m2) by (lt_eq_gt ad (#m2); sigma; upsilon; auto).
    assert (m2[ad].t <> None) by (intros F; rewrite F in *; auto).
    specialize (Hui ad) as [Hsome _]; trivial. spec.
    exfalso. eauto using noinit_oneinit_contradiction.
  - match goal with H : _ \ _ ~~[_ ++ ?e :: nil]~~>* _ \ _ |- _ => 
      destruct e as [tid' e'];
      eapply destruct_ustep' in H as [mA [mB [thsA [thsB [H1A [? ?]]]]]]
    end.
    invc H1A.
    assert (invariants mB thsB) by eauto using invariants_preservation_cstep.
    specialize (IHtc mB m2 thsB ths2 tid ad t). do 2 spec.
    assert (
      (forall t, e' <> e_init ad t /\ one_init ad thsB[tid]) \/
      (exists t, e' =  e_init ad t /\ tid' = tid /\ mB[ad].t = Some t)
    ) as [H' | [t' [? [? _]]]]
      by eauto using oneinit_preservation_cstep.
      + specialize (H' t) as [? Honeinit].
        specialize IHtc as [t' Hin]; trivial.
        eauto using in_app_tail.
      + subst. eauto using in_app_head.
Qed.

Local Lemma oneinit_multistep_onecr :
  forall tc m1 m2 ths1 ths2 tid1 tid2 ad e1 e2,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_init ad ths1[tid1]         ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    holding ad ths2[tid2]          ->
    happens_before <<(tid1, e1), tc, (tid2, e2)>>.
Proof.
  intros.
  assert (exists e tc2 tc3, is_acquire ad e /\ tc = tc3 ++ (tid2, e) :: tc2)
    as [eAcq [tc2 [tc3 [Hisacq Htc]]]]
    by eauto using oneinit_multistep_holding_requires_acquire.
  subst.
  assert (exists mA thsA t,
    m1 \ ths1 ~~[tc2]~~>* mA \ thsA /\ mA[ad].t = Some t)
    as [mA [thsA [? [? ?]]]]
    by eauto using multistep_acquire_requires_initialized.

  assert (invariants mA thsA) by eauto using invariants_preservation_ustep.
  assert (exists t, In (tid1, e_init ad t) tc2)
    as [t' Hin]
    by eauto using oneinit_multistep_initialized_requires_init.
  eapply in_split in Hin as [tc1 [tc0 ?]]. subst.

  eauto using happens_before_from_initialize_acquire_effects.
Qed.

(* ------------------------------------------------------------------------- *)
(* one-cr ~~>* one-init                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma onecr_multistep_oneinit :
  forall tc m1 m2 ths1 ths2 tid1 tid2 ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_cr   ad ths1[tid1]         ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_init ad ths2[tid2]         ->
    False.
Proof.
  intros.
  assert (m1[ad].t <> None). {
    assert (forall_threads ths1 (valid_term m1)) by eauto with inva.
    assert (Hui : unique_initializers m1 ths1) by eauto with inva.
    assert (Hice : init_cr_exclusivity ths1) by eauto with inva.
    assert (Had : ad < #m1) by eauto using onecr_ad_bound.
    intro. specialize (Hui ad Had) as [_ Hforone]. spec. 
    specialize Hforone as [tid' [Honeinit _]].
    specialize (Hice ad tid1 tid') as [_ ?].
    eauto using noinit_oneinit_contradiction.
  }
  assert (exists t, m1[ad].t = Some t)
    as [? ?]
    by (destruct (alt_opt_dec (m1[ad].t)); auto).
  assert (exists t, m2 [ad].t = Some t)
    as [t Hsome]
    by eauto using initialized_preservation_ustep.
  assert (forall_threads ths2 (consistent_term m2)) by eauto with inva.
  assert (Hnone : m2[ad].t = None) by eauto using oneinit_then_uninitialized.
  rewrite Hnone in Hsome. auto.
Qed.

(* ------------------------------------------------------------------------- *)
(* safety -- final 1                                                         *)
(* ------------------------------------------------------------------------- *)

Local Ltac _preservation L :=
  repeat (invc_cstep; invc_mstep); sigma;
  destruct_invariants; eauto using L.

Theorem happens_before_from_gcr : forall m1 m2 ths1 ths2 tid1 tid2 e1 e2 tc ad,
  invariants m1 ths1 ->
  invariants m2 ths2 ->
  (* --- *)
  tid1 <> tid2                          ->
  gcr ths1[tid1] (R_tid tid1) = R_ad ad ->
  gcr ths2[tid2] (R_tid tid2) = R_ad ad ->
  no_reacq ad ths1[tid1]                ->
  no_reacq ad ths2[tid2]                ->
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2        ->
  happens_before <<(tid1, e1), tc, (tid2, e2)>>.
Proof.
  intros * ? ? ? Hgcr1 Hgcr2 ? ? Hustep.
  assert (forall_threads ths1 term_init_cr_exc) by eauto with inva.
  assert (forall_threads ths2 term_init_cr_exc) by eauto with inva.
  assert (forall_threads ths1 (consistent_waits WR_none)) by eauto with inva.
  assert (forall_threads ths2 (consistent_waits WR_none)) by eauto with inva.
  eapply oneinit_or_onecr_from_gcr in Hgcr1 as [Honeinit1 | Honecr1];
  eapply oneinit_or_onecr_from_gcr in Hgcr2 as [Honeinit2 | Honecr2];
  eauto;
  try solve
    [ exfalso; eauto using oneinit_multistep_oneinit
    | exfalso; eauto using onecr_multistep_oneinit
  ];
  assert (holding ad ths2[tid2]) by (split; trivial).
  - eauto using oneinit_multistep_onecr.
  - assert (holding ad ths1[tid1]) by (split; trivial).
    (* TODO *)
Qed.

(* ------------------------------------------------------------------------- *)
(* safety -- final 0                                                         *)
(* ------------------------------------------------------------------------- *)

Local Corollary vtm_write_address_cstep : forall m1 m2 ths1 ths2 tid ad' t',
  invariants m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  ad' < #m1.
Proof.
  intros * H ?.
  eapply des_inva_vtm in H. eapply des_forallprogram_threads in H.
  invc_cstep. invc_mstep. eauto using vtm_write_address.
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

Theorem safety_write_write : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  invariants m1 ths1 ->
  (* --- *)
  tid1 <> tid2                                               ->
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2                             ->
  tc = <<(tid1, e_write ad t1), tc', (tid2, e_write ad t2)>> ->
  happens_before tc.
Proof.
  intros. subst. destruct_ustep3.
  assert (invariants mA thsA) by eauto using invariants_preservation_cstep.
  assert (invariants mB thsB) by eauto using invariants_preservation_ustep.
  assert (invariants m2 ths2) by eauto using invariants_preservation_cstep.

  assert (ad < #m1) by eauto using vtm_write_address_cstep.

  assert (exists T, m1[ad].T = `w&T`)
    as [T Hptyp1]
    by eauto using cstep_ptyp_for_write.
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

  assert (no_reacq ad thsA[tid1])
    by eauto using noreacq_from_write_cstep, noreacq_preservation_write_cstep.
  assert (no_reacq ad thsB[tid2])
    by eauto using noreacq_from_write_cstep.

  destruct (m1[ad].R).
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - admit.
  - exfalso. eauto using todo3 with inva.
Qed.

