From Coq Require Import Lists.List.

From Elo Require Import Core.
From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Multistep.

From Elo Require Import SafetyUtil.
From Elo Require Import GCR.
From Elo Require Import HappensBefore.
From Elo Require Import SafetyLemmas.

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
  intros * ? ? ? Hisacq Hcstep. destruct_ustep3.
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
      destruct e as [tid' e']; destruct_ustep3
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
(* holding ~~>* holding                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma holding_multistep_holding_requires_acquire' :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    holding ad ths1[tid1]          ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    holding ad ths2[tid2]          ->
    exists e, In (tid2, e) tc /\ is_acquire ad e.
Proof.
  intros * ? ? ? Hhg1 ? Hhg2. ind_ustep.
  - exfalso. eauto using holding_exclusivity with inva.
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

Local Corollary holding_multistep_holding_requires_acquire :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    holding ad ths1[tid1]          ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    holding ad ths2[tid2]          ->
    exists e tc1 tc2, is_acquire ad e /\ tc = tc2 ++ (tid2, e) :: tc1.
Proof.
  intros.
  assert (exists e, In (tid2, e) tc /\ is_acquire ad e)
    as [e [Hin ?]] by eauto using holding_multistep_holding_requires_acquire'.
  apply in_split in Hin as [tc2 [tc1 Htc]].
  exists e. exists tc1. exists tc2. split; assumption.
Qed.

Local Corollary multistep_acquire_requires_unlocked :
  forall m1 m2 ths1 ths2 tid1 tid2 tc1 tc2 ad e,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                                        ->
    is_acquire ad e                                     ->
    m1 \ ths1 ~~[tc2 ++ (tid2, e) :: tc1]~~>* m2 \ ths2 ->
    exists mA thsA,
      m1 \ ths1 ~~[tc1]~~>* mA \ thsA /\
      mA[ad].X = false.
Proof.
  intros until 3. intros Hisacq **. destruct_ustep3. repeat eexists; eauto.
  destruct Hisacq as  [[? ?] | ?]; subst; invc_cstep; invc_mstep; assumption.
Qed.

Local Lemma holding_multistep_unlocked_requires_release :
  forall tc m1 m2 ths1 ths2 tid ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    holding ad ths1[tid]           ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    m2[ad].X = false               ->
    exists e, is_release ad e /\ In (tid, e) tc.
Proof.
  intro. induction tc using rev_ind; intros.
  - invc_ustep.
    assert (mutual_exclusion m2 ths2) by eauto with inva.
    assert (Htrue : m2[ad].X = true) by eauto using locked_from_holding.
    rewrite Htrue in *. congruence.
  - match goal with H : _ \ _ ~~[_ ++ ?e :: nil]~~>* _ \ _ |- _ => 
      destruct e as [tid' e']; destruct_ustep3
    end.
    invc H1A.
    assert (invariants mB thsB) by eauto using invariants_preservation_cstep.
    specialize (IHtc mB m2 thsB ths2 tid ad). repeat spec.
    assert ((  is_release ad e' -> tid = tid') /\
            (~ is_release ad e' -> holding ad thsB[tid]))
      as [His Hnot]
      by eauto using holding_preservation_cstep.
    destruct (isrelease_dec ad e') as [Hisrel | ?]; repeat spec.
    + subst. eexists. split; eauto using in_app_head.
    + decompose record IHtc. eexists. split; eauto.
      eauto using in_app_tail.
Qed.

Local Lemma onecr_multistep_onecr :
  forall tc m1 m2 ths1 ths2 tid1 tid2 ad e1 e2,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    holding ad ths1[tid1]          ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    holding ad ths2[tid2]          ->
    happens_before <<(tid1, e1), tc, (tid2, e2)>>.
Proof.
  intros.
  assert (exists e tc2 tc3, is_acquire ad e /\ tc = tc3 ++ (tid2, e) :: tc2)
    as [eAcq [tc2 [tc3 [Hisacq Htc]]]]
    by eauto using holding_multistep_holding_requires_acquire.
  subst.
  assert (exists mA thsA,
    m1 \ ths1 ~~[tc2]~~>* mA \ thsA /\ mA[ad].X = false)
    as [mA [thsA [? ?]]]
    by eauto using multistep_acquire_requires_unlocked.

  assert (invariants mA thsA) by eauto using invariants_preservation_ustep.

  assert (exists e, is_release ad e /\ In (tid1, e) tc2)
    as [eRel [Hisrel Hin]]
    by eauto using holding_multistep_unlocked_requires_release.
  eapply in_split in Hin as [tc1 [tc0 ?]]. subst.

  eauto using happens_before_from_release_acquire_effects.
Qed.

(* ------------------------------------------------------------------------- *)
(* happens-before-from-gcr                                                   *)
(* ------------------------------------------------------------------------- *)

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
  try solve [ exfalso; eauto using oneinit_multistep_oneinit
            | exfalso; eauto using onecr_multistep_oneinit
            ];
  assert (holding ad ths2[tid2]) by (split; trivial).
  - eauto using oneinit_multistep_onecr.
  - assert (holding ad ths1[tid1]) by (split; trivial).
    eauto using onecr_multistep_onecr.
Qed.

