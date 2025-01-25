
(* ------------------------------------------------------------------------- *)
(* one-init ~~>* one-cr                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma oneinit_multistep_onecr_requires_acq' :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_init ad ths1[tid1]         ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_cr   ad ths2[tid2]         ->
    exists t, In (tid2, (e_acq ad t)) tc.
Proof.
  intros. ind_ustep.
  - exfalso.
    assert (Hice : init_cr_exclusivity ths) by eauto with inva.
    specialize (Hice ad tid1 tid2) as [? _].
    eauto using nocr_onecr_contradiction.
  - assert (invariants m2 ths2) by eauto using invariants_preservation_ustep.
    repeat spec.
    assert (exists t, (e <> e_acq ad t /\ one_cr ad ths2[tid2]) \/
                      (e =  e_acq ad t /\ tid = tid2))
      as [t [[? ?] | [? ?]]]
      by eauto using onecr_inheritance_cstep.
    + destruct IHmultistep; trivial. eexists. right. eauto.
    + subst. exists t. left. eauto.
Qed.

Local Corollary oneinit_multistep_onecr_requires_acq :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_init ad ths1[tid1]         ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_cr   ad ths2[tid2]         ->
    exists t tc1 tc2, tc = tc2 ++ (tid2, e_acq ad t) :: tc1.
Proof.
  intros.
  assert (exists t, In (tid2, (e_acq ad t)) tc)
    as [t Hin] by eauto using oneinit_multistep_onecr_requires_acq'.
  apply in_split in Hin as [tc2 [tc1 Htc]].
  exists t. exists tc1. exists tc2. assumption.
Qed.

Local Corollary multistep_acq_requires_initialized :
  forall m1 m2 ths1 ths2 tid1 tid2 tc1 tc2 ad t,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2 ->
    m1 \ ths1 ~~[tc2 ++ (tid2, e_acq ad t) :: tc1]~~>* m2 \ ths2 ->
    exists mA thsA t,
      m1 \ ths1 ~~[tc1]~~>* mA \ thsA /\
      mA[ad].t = Some t.
Proof.
  intros * ? ? ? H.
  eapply destruct_ustep' in H. decompose record H.
  repeat eexists; eauto.
  invc_cstep. invc_mstep. eauto.
Qed.

Local Lemma oneinit_multistep_initialized_requires_init :
  forall tc m1 m2 ths1 ths2 tid ad t,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_init ad ths1[tid]          ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    m2[ad].t = Some t              ->
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
  forall tc m1 m2 ths1 ths2 tid1 tid2 ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_init ad ths1[tid1]         ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_cr   ad ths2[tid2]         ->
    exists tc1 tc2 tc3 tc' t1 t2,
      tc  = tc3 ++ tc2 ++ tc1                                  /\
      tc2 = <<(tid1, e_init ad t1), tc', (tid2, e_acq ad t2)>> /\
      happens_before tc2.
Proof.
  intros.
  assert (exists t tc1 tc2, tc = tc2 ++ (tid2, e_acq ad t) :: tc1)
    as [t [tc1 [tc2 Hacq]]]
    by eauto using oneinit_multistep_onecr_requires_acq.
  subst.
  assert (exists mA thsA t,
    m1 \ ths1 ~~[tc1]~~>* mA \ thsA /\ mA[ad].t = Some t)
    as [mA [thsA [? [? ?]]]]
    by eauto using multistep_acq_requires_initialized.
  assert (invariants mA thsA) by eauto using invariants_preservation_ustep.
  assert (exists t, In (tid1, e_init ad t) tc1)
    as [t' ?]
    by eauto using oneinit_multistep_initialized_requires_init.
  exists tc1. exists (tc2 ++ (tid2, e_acq ad t) :: nil).
  exists t. exists t'.
  repeat split; eauto using in_app_head.
  rewrite <- app_assoc. reflexivity.
Abort.

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
(* one-cr ~~>* one-cr                                                        *)
(* ------------------------------------------------------------------------- *)

(*
Local Lemma onecr_multistep_onecr_requires_acq' :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2 ->
    one_cr ad ths1[tid1] ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_cr ad ths2[tid2] ->
    exists t, In (tid2, (e_acq ad t)) tc.
Proof.
  intros. ind_ustep.
  - exfalso.
    assert (Hmu : mutual_exclusion m ths) by eauto with inva.
    specialize (Hmu ad) as [Hfalse Htrue].
    destruct (m[ad].X); spec.
    + specialize Htrue as [tid [? ?]].
      nat_eq_dec tid1 tid; nat_eq_dec tid2 tid;
      eauto using nocr_onecr_contradiction.
    + eauto using nocr_onecr_contradiction.
  - assert (invariants m2 ths2) by eauto using invariants_preservation_ustep.
    repeat spec.
    assert (exists t, (e <> e_acq ad t /\ one_cr ad ths2[tid2]) \/
                      (e =  e_acq ad t /\ tid = tid2))
      as [t [[? ?] | [? ?]]]
      by eauto using onecr_inheritance_cstep.
    + destruct IHmultistep; trivial. eexists. right. eauto.
    + subst. exists t. left. eauto.
Qed.

Local Corollary onecr_multistep_onecr_requires_acq :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2 ->
    one_cr ad ths1[tid1] ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_cr ad ths2[tid2] ->
    exists t tc1 tc2, tc = tc2 ++ (tid2, e_acq ad t) :: tc1.
Proof.
  intros.
  assert (exists t, In (tid2, (e_acq ad t)) tc)
    as [t Hin] by eauto using onecr_multistep_onecr_requires_acq'.
  apply in_split in Hin as [tc2 [tc1 Htc]].
  exists t. exists tc1. exists tc2. assumption.
Qed.

Local Corollary multistep_acq_requires_unlocked :
  forall m1 m2 ths1 ths2 tid1 tid2 tc1 tc2 ad t,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2 ->
    m1 \ ths1 ~~[tc2 ++ (tid2, e_acq ad t) :: tc1]~~>* m2 \ ths2 ->
    exists mA thsA,
      m1 \ ths1 ~~[tc1]~~>* mA \ thsA /\
      mA[ad].X = false.
Proof.
  intros * ? ? ? H.
  eapply destruct_ustep' in H. decompose record H.
  repeat eexists; eauto.
  invc_cstep. invc_cstep. invc_mstep. assumption.
Qed.

Local Lemma onecr_multistep_unlocked_requires_rel :
  forall tc m1 m2 ths1 ths2 tid ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_cr ad ths1[tid] ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    m2[ad].X = false ->
    In (tid, e_rel ad) tc.
Proof.
  intro. induction tc using rev_ind; intros.
  - invc_ustep.
    assert (unique_critical_regions m2 ths2) by eauto with inva.
    assert (Htrue : m2[ad].X = true) by eauto using locked_from_onecr.
    rewrite Htrue in *. auto.
  - match goal with H : _ \ _ ~~[_ ++ ?e :: nil]~~>* _ \ _ |- _ => 
      destruct e as [tid' e'];
      eapply destruct_ustep' in H as [mA [mB [thsA [thsB [H1A [? ?]]]]]]
    end.
    invc H1A.
    assert (invariants mB thsB) by eauto using invariants_preservation_cstep.
    assert ((e' <> e_rel ad /\ one_cr ad thsB[tid]) \/
            (e' =  e_rel ad /\ tid' = tid))
      as [[? ?] | [? ?]]
      by eauto using onecr_preservation_cstep;
    subst; eauto using in_app_head, in_app_tail.
Qed.

Local Lemma onecr_multistep_onecr :
  forall tc m1 m2 ths1 ths2 tid1 tid2 ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_cr ad ths1[tid1]           ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_cr ad ths2[tid2]           ->
    exists tc1 tc2 t,
      tc = tc2 ++ tc1           /\
      In (tid1, e_rel ad)   tc1 /\
      In (tid2, e_acq ad t) tc2.
Proof.
  intros.
  assert (exists t tc1 tc2, tc = tc2 ++ (tid2, e_acq ad t) :: tc1)
    as [t [tc1 [tc2 Hacq]]]
    by eauto using onecr_multistep_onecr_requires_acq.
  subst.
  assert (exists mA thsA, m1 \ ths1 ~~[tc1]~~>* mA \ thsA /\ mA[ad].X = false)
    as [mA [thsA [H1A Hunlocked]]]
    by eauto using multistep_acq_requires_unlocked.
  assert (invariants mA thsA) by eauto using invariants_preservation_ustep.
  exists tc1. exists (tc2 ++ (tid2, e_acq ad t) :: nil). exists t.
  repeat split; eauto using in_app_head, onecr_multistep_unlocked_requires_rel.
  rewrite <- app_assoc. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* safety                                                                    *)
(* ------------------------------------------------------------------------- *)

Local Ltac _preservation L :=
  repeat (invc_cstep; invc_mstep); sigma;
  destruct_invariants; eauto using L.

(*
Theorem happens_before_from_gcrR :
  forall m mA mB ths thsA thsB tid1 tid2 tc adx ad' t',
    invariants m  ths  ->
    invariants mA thsA ->
    invariants mB thsB ->
    (* --- *)
    tid1 <> tid2                                    ->
    gcr thsA[tid1] (R_tid tid1) = R_ad adx          ->
    gcr thsB[tid2] (R_tid tid2) = R_ad adx          ->
    mA \ thsA ~~~[tid1, e_read ad' t']~~> m  \ ths  ->
    m  \ ths  ~~[tc]~~>*                  mB \ thsB ->
    exists tc1 tc2, tc = tc2 ++ tc1 /\
    exists adx t t',
      (In (tid1, e_rel    adx)    tc1 /\ In (tid2, e_acq adx t) tc2) \/
      (In (tid1, e_init adx t') tc1 /\ In (tid2, e_acq adx t) tc2).
Proof.
  intros * ? ? ? ? HgcrA HgcrB Hcstep Hustep.
  assert (forall_memory mA value) by eauto with inva.
  assert (forall_memory mA (valid_term mA)) by eauto with inva.
  assert (no_inits t' /\ no_crs t') as [? ?]. {
    invc_cstep; invc_cstep; invc_mstep;
    split; eauto using noinits_from_value, nocrs_from_value.
  }
  assert (forall_threads thsA term_init_cr_exc) by eauto using des_inva_tice.
  assert (forall_threads thsB term_init_cr_exc) by eauto using des_inva_tice.
  eapply oneinit_or_onecr_from_gcr in HgcrA as [HoneinitA | HonecrA];
  eapply oneinit_or_onecr_from_gcr in HgcrB as [HoneinitB | HonecrB];
  eauto.
  - assert (one_init adx ths[tid1]) by _preservation oneinit_preservation_read.
    exfalso. eauto using oneinit_multistep_oneinit.
  - assert (one_init adx ths[tid1]) by _preservation oneinit_preservation_read.
    assert (exists tc1 tc2 t t',
      tc = tc2 ++ tc1                /\
      In (tid1, e_init adx t') tc1 /\
      In (tid2, e_acq    adx t)     tc2)
      as [tc1 [tc2 [t [t'' [? [? ?]]]]]]
      by eauto using oneinit_multistep_onecr.
    exists tc1, tc2. split; trivial.
    repeat eexists. eauto.
  - assert (one_cr adx ths[tid1]) by _preservation onecr_preservation_read.
    exfalso. eauto using onecr_multistep_oneinit.
  - assert (one_cr adx ths[tid1]) by _preservation onecr_preservation_read.
    assert (exists tc1 tc2 t,
      tc = tc2 ++ tc1            /\
      In (tid1, e_rel adx)   tc1 /\
      In (tid2, e_acq adx t) tc2)
      as [tc1 [tc2 [t [? [? ?]]]]]
      by eauto using onecr_multistep_onecr.
    exists tc1, tc2. split; trivial.
    eexists. eexists. exists <{unit}>. eauto.
Qed.

Theorem safety_write_read : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  tid1 <> tid2 ->
  invariants m1 ths1 ->
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  tc = (tid2, e_read ad t2) :: tc' +++ (tid1, e_write ad t1) ->
  exists tc1 tc2, tc' = tc2 ++ tc1 /\
  exists adx t t',
    (In (tid1, e_rel    adx)    tc1 /\ In (tid2, e_acq adx t) tc2) \/
    (In (tid1, e_init adx t') tc1 /\ In (tid2, e_acq adx t) tc2).
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
    by eauto using cstep_gcr_read with inva.

  assert (HR : m1[ad].R = mB[ad].R) by eauto using same_regions.
  rewrite <- HR in *.

  destruct (m1[ad].R);
  try solve [exfalso; eauto using gcr_tid_contradiction with gcr].

  eauto using happens_before_from_gcrW.
Qed.

Corollary _rel_acq : forall m1 m2 ths1 ths2 tc1 tc2 e1 e2 tid1 tid2 adx t,
  m1 \ ths1 ~~[(tid2, e2) :: (tc2 ++ tc1) +++ (tid1, e1)]~~>* m2 \ ths2 ->
  In (tid1, e_rel adx) tc1 ->
  In (tid2, e_acq adx t) tc2 ->
  happens_before ((tid2, e2) :: (tc2 ++ tc1) +++ (tid1, e1)).
Proof.
  intros * Hustep Hin1 Hin2.
  remember (tid1, e_rel adx) as evR.
  remember (tid2, e_acq adx t) as evA.
  apply in_split in Hin1 as [tcB [tcA Heq1]].
  apply in_split in Hin2 as [tcD [tcC Heq2]].

  unfold add.
  rewrite <- app_assoc.
  rewrite Heq1; clear Heq1.
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  rewrite app_assoc.
  apply hb_trans.
  - rewrite HeqevR. auto using happens_before.
  - unfold add.
    rewrite <- app_assoc.
    rewrite Heq2; clear Heq2.
    rewrite <- app_assoc.
    rewrite <- app_comm_cons.
    rewrite app_assoc.
    apply hb_trans.
    + rewrite HeqevA.
      rewrite HeqevR.
      auto using happens_before.
    + rewrite HeqevA.
      auto using happens_before.
Qed.

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

Theorem happens_before_from_gcrW :
  forall m mA mB ths thsA thsB tid1 tid2 tc e adx ad' t',
    invariants m  ths  ->
    invariants mA thsA ->
    invariants mB thsB ->
    (* --- *)
    tid1 <> tid2                                     ->
    gcr thsA[tid1] (R_tid tid1) = R_ad adx           ->
    gcr thsB[tid2] (R_tid tid2) = R_ad adx           ->
    mA \ thsA ~~[tid1, e_write ad' t']~~>  m  \ ths  ->
    m  \ ths  ~~[tc                  ]~~>* mB \ thsB ->
    happens_before <<(tid1, e_write ad' t'), tc, (tid2, e)>>.
Proof.
  intros * ? ? ? ? HgcrA HgcrB Hcstep Hustep.
  assert (forall_threads thsA term_init_cr_exc) by eauto with inva.
  assert (forall_threads thsB term_init_cr_exc) by eauto with inva.
  assert (forall_threads thsA (consistent_waits WR_none)) by eauto with inva.
  assert (forall_threads thsB (consistent_waits WR_none)) by eauto with inva.
  eapply oneinit_or_onecr_from_gcr in HgcrA as [HoneinitA | HonecrA];
  eapply oneinit_or_onecr_from_gcr in HgcrB as [HoneinitB | HonecrB];
  eauto.
  - assert (one_init adx ths[tid1]) by _preservation oneinit_preservation_write.
    exfalso. eauto using oneinit_multistep_oneinit.
  - assert (one_init adx ths[tid1]) by _preservation oneinit_preservation_write.
    assert (exists tc1 tc2 t t',
      tc = tc2 ++ tc1                   /\
      In (tid1, e_init adx t') tc1    /\
      In (tid2, e_acq    adx t)     tc2)
      as [tc1 [tc2 [t [t'' [? [? ?]]]]]]
      by eauto using oneinit_multistep_onecr.
    exists tc1, tc2. split; trivial.
    repeat eexists. eauto.
  - assert (one_cr adx ths[tid1]) by _preservation onecr_preservation_write.
    exfalso. eauto using onecr_multistep_oneinit.
  - assert (one_cr adx ths[tid1]) by _preservation onecr_preservation_write.
    assert (exists tc1 tc2 t,
      tc = tc2 ++ tc1            /\
      In (tid1, e_rel adx)   tc1 /\
      In (tid2, e_acq adx t) tc2)
      as [tc1 [tc2 [t [? [? ?]]]]]
      by eauto using onecr_multistep_onecr.
    exists tc1, tc2. split; trivial.
    eexists. eexists. exists <{unit}>. eauto.
Abort.

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

  destruct (m1[ad].R).
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - exfalso. eauto using gcr_tid_contradiction with gcr.
  - eauto using happens_before_from_gcrW.
  - exfalso. eauto using todo3 with inva.

Qed.

Theorem safety_read_write : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  tid1 <> tid2 ->
  invariants m1 ths1 ->
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  tc = (tid2, e_write ad t2) :: tc' +++ (tid1, e_read ad t1) ->
  exists tc1 tc2, tc' = tc2 ++ tc1 /\
  exists adx t t',
    (In (tid1, e_rel  adx)    tc1 /\ In (tid2, e_acq adx t) tc2) \/
    (In (tid1, e_init adx t') tc1 /\ In (tid2, e_acq adx t) tc2).
Proof.
  intros. subst. destruct_ustep3.
  assert (invariants mA thsA) by eauto using invariants_preservation_cstep.
  assert (invariants mB thsB) by eauto using invariants_preservation_ustep.
  assert (invariants m2 ths2) by eauto using invariants_preservation_cstep.

  assert (ad < #m1) by (repeat (invc_cstep; invc_cstep; invc_mstep); trivial).

  assert (exists T, mB[ad].T = `w&T`)
    as [T HptypB]
    by eauto using cstep_ptyp_for_write.
  assert (m1[ad].T = mA[ad].T /\ mA[ad].T = mB[ad].T /\ mB[ad].T = m2[ad].T)
    as [Hptyp1 [HptypA _]]
    by eauto using same_pointer_type.
  rewrite HptypB in HptypA.
  rewrite HptypA in Hptyp1.

  assert (Hgcr1 : gcr ths1[tid1] (R_tid tid1) = m1[ad].R)
    by eauto   using cstep_gcr_read with inva.
  assert (HgcrB : gcr thsB[tid2] (R_tid tid2) = mB[ad].R)
    by eauto 7 using cstep_gcr_write with inva.

  assert (HR : m1[ad].R = mB[ad].R) by eauto using same_regions.
  rewrite <- HR in *.

  destruct (m1[ad].R);
  try solve [exfalso; eauto using gcr_tid_contradiction with gcr].

  eauto using happens_before_from_gcrR.
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem write_happens_before_read :
  forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
    invariants m1 ths1 ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    tc = (tid2, e_read ad t2) :: tc' +++ (tid1, e_write ad t1) ->
    happens_before tc.
Proof.
  intros. subst. nat_eq_dec tid1 tid2; auto using happens_before.


  destruct_ustep3.
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
    by eauto using cstep_gcr_read with inva.

  assert (HR : m1[ad].R = mB[ad].R) by eauto using same_regions.
  rewrite <- HR in *.

  destruct (m1[ad].R);
  try solve [exfalso; eauto using gcr_tid_contradiction with gcr].

  eauto using happens_before_from_gcrW.
Qed.
