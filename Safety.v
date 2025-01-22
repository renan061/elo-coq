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

(* TODO: posso usar consistent_term *)
Local Lemma uninitialized_from_oneinit : forall m ths tid ad,
  forall_threads ths (valid_term m) ->
  unique_initializers m ths ->
  (* --- *)
  one_init ad ths[tid] ->
  m[ad].t = None.
Proof.
  intros * ? Hui ?.
  assert (Had : ad < #m) by eauto using oneinit_ad_bound.
  destruct (Hui ad Had). opt_dec (m[ad].t); trivial.
  spec. exfalso. eauto using noinit_oneinit_contradiction.
Qed.

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

(*
Local Lemma oneinit_multistep_onecr_requires_acq' :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2 ->
    one_init ad ths1[tid1] ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_cr ad ths2[tid2] ->
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
    tid1 <> tid2 ->
    one_init ad ths1[tid1] ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_cr ad ths2[tid2] ->
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
  invc_cstep. invc_cstep. invc_mstep. eauto.
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
  forall tc m1 m2 ths1 ths2 tid1 tid2 ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_init ad ths1[tid1]         ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_cr   ad ths2[tid2]         ->
    exists tc1 tc2 t t',
      tc = tc2 ++ tc1               /\
      In (tid1, e_init ad t') tc1 /\
      In (tid2, e_acq    ad t)  tc2.
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
Qed.
*)

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
    assert (Hucr : unique_holding m ths) by eauto with inva.
    specialize (Hucr ad) as [Hfalse Htrue].
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
*)

(* ------------------------------------------------------------------------- *)
(* safety                                                                    *)
(* ------------------------------------------------------------------------- *)

Local Ltac _preservation L :=
  repeat (invc_cstep; invc_cstep; invc_mstep); sigma;
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
*)

Notation "'<<' ev1 ',' tc ',' ev2 '>>'" := (ev2 :: tc +++ ev1).

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
  forall m mA mB ths thsA thsB tid1 tid2 tc adx ad' t',
    invariants m  ths  ->
    invariants mA thsA ->
    invariants mB thsB ->
    (* --- *)
    tid1 <> tid2                                    ->
    gcr thsA[tid1] (R_tid tid1) = R_ad adx          ->
    gcr thsB[tid2] (R_tid tid2) = R_ad adx          ->
    mA \ thsA ~~[tid1, e_write ad' t']~~> m  \ ths  ->
    m  \ ths  ~~[tc]~~>*                  mB \ thsB ->
    exists tc1 tc2, tc = tc2 ++ tc1 /\
    exists adx t t',
      (In (tid1, e_rel    adx)    tc1 /\ In (tid2, e_acq adx t) tc2) \/
      (In (tid1, e_init adx t') tc1 /\ In (tid2, e_acq adx t) tc2).
Proof.
  intros * ? ? ? ? HgcrA HgcrB Hcstep Hustep.
  assert (forall_threads thsA term_init_cr_exc) by eauto using des_inva_tice.
  assert (forall_threads thsB term_init_cr_exc) by eauto using des_inva_tice.
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
  - admit.
  - admit.

  eauto using happens_before_from_gcrW.
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
