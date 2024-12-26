From Coq Require Import Lists.List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Multistep.
From Elo Require Import MemoryRegions.
From Elo Require Import GCR.
From Elo Require Import InheritanceSafety.

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

Corollary rstep_ptyp_for_write : forall m1 m2 ths1 ths2 tid ad' t',
  invariants m1 ths1 ->
  (* --- *)
  m1 / ths1 ~~~[tid, e_write ad' t']~~> m2 / ths2 ->
  exists T, m1[ad'].T = `w&T`.
Proof.
  intros. destruct_invariants. invc_ostep. invc_cstep. invc_mstep.
  eauto using  ptyp_for_write. 
Qed.

Local Lemma same_pointer_type :
  forall m1 mA mB m2 ths1 thsA thsB ths2 tc tid1 tid2 e1 e2 ad,
    invariants m1 ths1 ->
    (* --- *)
    ad < #m1 ->
    m1 / ths1 ~~~[tid1, e1]~~>  mA / thsA ->
    mA / thsA  ~~[tc      ]~~>* mB / thsB ->
    mB / thsB ~~~[tid2, e2]~~>  m2 / ths2 ->
    (m1[ad].T = mA[ad].T /\ mA[ad].T = mB[ad].T /\ mB[ad].T = m2[ad].T).
Proof.
  intros.
  assert (ad < #mA) by eauto using rstep_nondecreasing_memory_size.
  assert (ad < #mB) by eauto using ustep_nondecreasing_memory_size.
  assert (ad < #m2) by eauto using rstep_nondecreasing_memory_size.
  assert (HtA : m1[ad].T = mA[ad].T) by eauto using ptyp_preservation_rstep.
  assert (HtB : mA[ad].T = mB[ad].T) by eauto using ptyp_preservation_ustep.
  assert (Ht2 : mB[ad].T = m2[ad].T) by eauto using ptyp_preservation_rstep.
  eauto.
Qed.

Local Lemma same_regions :
  forall m1 mA mB m2 ths1 thsA thsB ths2 tc tid1 tid2 e1 e2 ad,
    invariants m1 ths1 ->
    (* --- *)
    ad < #m1 ->
    m1 / ths1 ~~~[tid1, e1]~~>  mA / thsA ->
    mA / thsA  ~~[tc      ]~~>* mB / thsB ->
    mB / thsB ~~~[tid2, e2]~~>  m2 / ths2 ->
    m1[ad].R = mB[ad].R.
Proof.
  intros.
  assert (ad < #mA) by eauto using rstep_nondecreasing_memory_size.
  assert (ad < #mB) by eauto using ustep_nondecreasing_memory_size.
  assert (HrA : m1[ad].R = mA[ad].R) by eauto using mreg_preservation_rstep.
  assert (HrB : mA[ad].R = mB[ad].R) by eauto using mreg_preservation_ustep.
  rewrite HrB in HrA.
  assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma _destruct_ustep2 : forall tc m1 m3 ths1 ths3 tid e,
  m1 / ths1 ~~[tc ++ (tid, e) :: nil]~~>* m3 / ths3 ->
  (exists m2 ths2,
    m1 / ths1 ~~~[tid, e]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*     m3 / ths3 ).
Proof.
  intros ?. induction tc; intros; invc_ustep.
  - invc_ustep. eauto using multistep.
  - match goal with Hustep : _ / _ ~~[ _ ]~~>* _ / _ |- _ => 
      decompose record (IHtc _ _ _ _ _ _ Hustep); eauto using multistep
    end.
Qed.

Ltac destruct_ustep2 :=
  match goal with
  | H : _ / _  ~~[_ ++ (_, _) :: nil]~~>* _ / _ |- _ =>
    eapply _destruct_ustep2 in H as [? [? [? ?]]]
  end.

Local Lemma _destruct_ustep3 : forall tc m1 m4 ths1 ths4 tid1 tid2 e1 e2,
  m1 / ths1 ~~[(tid2, e2) :: tc ++ (tid1, e1) :: nil]~~>* m4 / ths4 ->
  (exists m2 ths2 m3 ths3,
    m1 / ths1 ~~~[tid1, e1]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*      m3 / ths3 /\
    m3 / ths3 ~~~[tid2, e2]~~> m4 / ths4 ).
Proof.
  intros. invc_ustep. destruct_ustep2. do 4 eexists. repeat split; eauto.
Qed.

Ltac destruct_ustep3 :=
  match goal with 
  | H : _ / _ ~~[(_, _) :: _ ++ (_, _) :: nil]~~>* _ / _ |- _ =>
    eapply _destruct_ustep3 in H
      as [mA [thsA [mB [thsB [H1A [HAB HB2]]]]]]
  end.

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

Local Lemma uninitialized_inheritance_rstep : forall m1 m2 ths1 ths2 tid e ad,
  m2[ad].t = None ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  m1[ad].t = None.
Proof.
  intros. invc_ostep; invc_cstep; try invc_mstep; sigma; upsilon; trivial.
  repeat omicron; trivial.
Qed.

Local Lemma uninitialized_inheritance_ustep : forall m1 m2 ths1 ths2 tc ad,
  m2[ad].t = None ->
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  m1[ad].t = None.
Proof.
  intros. ind_ustep; eauto using uninitialized_inheritance_rstep. 
Qed.

Local Lemma todo : forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
  invariants m1 ths1 ->
  invariants m2 ths2 ->
  (* --- *)
  ad < #m1 ->
  tid1 <> tid2 ->
  one_init ad ths1[tid1] ->
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  one_init ad ths2[tid2] ->
  False.
Proof.
  intros. ind_ustep; eauto using ui_oneinit_contradiction with inva.
  assert (invariants m2 ths2) by eauto using invariants_preservation_ustep.
  repeat spec.
  (* WIP *)
  eapply IHmultistep. clear IHmultistep.
Abort.

Theorem safety_write_read : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  tid1 <> tid2 ->
  invariants m1 ths1 ->
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  tc = (tid2, e_read ad t2) :: tc' ++ (tid1, e_write ad t1) :: nil ->
  False. (* TODO *)
Proof.
  intros. subst. destruct_ustep3.
  assert (invariants mA thsA) by eauto using invariants_preservation_rstep.
  assert (invariants mB thsB) by eauto using invariants_preservation_ustep.
  assert (invariants m2 ths2) by eauto using invariants_preservation_rstep.

  assert (ad < #m1) by (repeat (invc_ostep; invc_cstep; invc_mstep); trivial).

  assert (exists T, m1[ad].T = `w&T`)
    as [T Hptyp1]
    by eauto using rstep_ptyp_for_write.
  assert (m1[ad].T = mA[ad].T /\ mA[ad].T = mB[ad].T /\ mB[ad].T = m2[ad].T)
    as [HptypA [HptypB Hptyp2]]
    by eauto using same_pointer_type.
  rewrite Hptyp1 in HptypA. symmetry in HptypA.
  rewrite HptypA in HptypB. symmetry in HptypB.
  rewrite HptypB in Hptyp2. symmetry in Hptyp2.

  assert (Hgcr1 : gcr ths1[tid1] (R_tid tid1) = m1[ad].R)
    by eauto 7 using rstep_gcr_write with inva.
  assert (HgcrB : gcr thsB[tid2] (R_tid tid2) = mB[ad].R)
    by eauto using rstep_gcr_read with inva.

  assert (HR : m1[ad].R = mB[ad].R) by eauto using same_regions.
  rewrite <- HR in *.

  destruct (m1[ad].R); eauto using gcr_tid_contradiction with gcr.
  match goal with H : R_ad ?ad' = _ |- _ => rename ad' into adx end.

  assert (forall_threads ths1 term_init_cr_exc) by eauto using des_inva_tice.
  assert (forall_threads thsB term_init_cr_exc) by eauto using des_inva_tice.
  eapply oneinit_or_onecr_from_gcr in Hgcr1 as [Honeinit1 | Honecr1];
  eapply oneinit_or_onecr_from_gcr in HgcrB as [HoneinitB | HonecrB];
  eauto.
  - assert (one_init adx thsA[tid1]). {
      repeat (invc_ostep; invc_cstep; invc_mstep). sigma.
      destruct_invariants. eauto using oneinit_preservation_write.
    }
    exfalso. admit.
  - assert (one_init adx thsA[tid1]). {
      repeat (invc_ostep; invc_cstep; invc_mstep). sigma.
      destruct_invariants. eauto using oneinit_preservation_write.
    }
    admit.
  - assert (one_cr adx thsA[tid1]). {
      repeat (invc_ostep; invc_cstep; invc_mstep). sigma.
      destruct_invariants. eauto using onecr_preservation_write.
    }
    exfalso. admit.
  - assert (one_cr adx thsA[tid1]). {
      repeat (invc_ostep; invc_cstep; invc_mstep). sigma.
      destruct_invariants. eauto using onecr_preservation_write.
    }
    admit.
Abort.

(* ------------------------------------------------------------------------- *)
(* one-cr x one-cr case                                                      *)
(* ------------------------------------------------------------------------- *)


(*

(ths1[tid1], READ ad) --[tc1 + REL + tc2 + ACQ + tc3]-->* (ths2[tid2], WRITE ad)

*)

Local Lemma onecr_multistep_onecr_aux1 :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2 ->
    one_cr ad ths1[tid1] ->
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    one_cr ad ths2[tid2] ->
    exists t, In (tid2, (e_acq ad t)) tc.
Proof.
  intros. ind_ustep; eauto using ui_oneinit_contradiction with inva.
  - exfalso.
    assert (Hucr : unique_critical_regions m ths) by eauto with inva.
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
      by eauto using onecr_inheritance_rstep.
    + destruct IHmultistep; trivial. eexists. right. eauto.
    + subst. exists t. left. eauto.
Qed.

Local Corollary onecr_multistep_onecr_aux1' :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2 ->
    one_cr ad ths1[tid1] ->
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    one_cr ad ths2[tid2] ->
    exists t tc1 tc2, tc = tc2 ++ (tid2, e_acq ad t) :: tc1.
Proof.
  intros. Search (_ ++ _ :: _ = _).
  assert (exists t, In (tid2, (e_acq ad t)) tc)
    as [t Hin] by eauto using onecr_multistep_onecr_aux1.
  apply in_split in Hin as [tc2 [tc1 Htc]].
  exists t. exists tc1. exists tc2. assumption.
Qed.

Local Lemma destruct_ustep' : forall m1 m2 ths1 ths2 tc1 tc2 tid e,
  m1 / ths1 ~~[tc2 ++ (tid, e) :: tc1]~~>* m2 / ths2 ->
  exists mA mB thsA thsB,
    m1 / ths1  ~~[tc1   ]~~>* mA / thsA /\
    mA / thsA ~~~[tid, e]~~>  mB / thsB /\
    mB / thsB  ~~[tc2   ]~~>* m2 / ths2.
Proof.
  intros.
  gendep ths2. gendep ths1. gendep m2. gendep m1. gendep e. gendep tid.
  induction tc2; intros.
  - rewrite app_nil_l in *. invc_ustep. repeat eexists; eauto using multistep.
  - invc_ustep.
    match goal with H : _ / _ ~~[_]~~>* _ / _ |- _ =>
      decompose record (IHtc2 _ _ _ _ _ _ H)
    end.
    repeat eexists; eauto using multistep.
Qed.

Local Corollary onecr_multistep_onecr_aux1'' :
  forall m1 m2 ths1 ths2 tid1 tid2 tc1 tc2 ad t,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2 ->
    one_cr ad ths1[tid1] ->
    m1 / ths1 ~~[tc2 ++ (tid2, e_acq ad t) :: tc1]~~>* m2 / ths2 ->
    exists mA thsA,
      m1 / ths1 ~~[tc1]~~>* mA / thsA /\
      mA[ad].X = false.
Proof.
  intros * ? ? ? ? H.
  eapply destruct_ustep' in H. decompose record H.
  repeat eexists; eauto.
  invc_ostep. invc_cstep. invc_mstep. assumption.
Qed.

Local Lemma onecr_multistep_onecr_aux2 :
  forall tc m1 m2 ths1 ths2 tid ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_cr ad ths1[tid] ->
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    m2[ad].X = false ->
    In (tid, e_rel ad) tc.
Proof.
  intro. induction tc using rev_ind; intros.
  - invc_ustep.
    assert (unique_critical_regions m2 ths2) by eauto with inva.
    assert (Htrue : m2[ad].X = true) by eauto using locked_from_onecr.
    rewrite Htrue in *. auto.
  - match goal with H : _ / _ ~~[_ ++ ?e :: nil]~~>* _ / _ |- _ => 
      destruct e as [tid' e'];
      eapply destruct_ustep' in H as [mA [mB [thsA [thsB [H1A [? ?]]]]]]
    end.
    invc H1A.
    assert (invariants mB thsB) by eauto using invariants_preservation_rstep.
    assert ((e' <> e_rel ad /\ one_cr ad thsB[tid]) \/
            (e' =  e_rel ad /\ tid' = tid))
      as [[? ?] | [? ?]]
      by eauto using onecr_preservation_rstep;
    subst; eauto using in_app_head, in_app_tail.
Qed.

Local Lemma onecr_multistep_onecr :
  forall tc m1 m2 ths1 ths2 tid1 tid2 ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    tid1 <> tid2                   ->
    one_cr ad ths1[tid1]           ->
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    one_cr ad ths2[tid2]           ->
    exists tc1 tc2 t,
      tc = tc2 ++ tc1           /\
      In (tid1, e_rel ad)   tc1 /\
      In (tid2, e_acq ad t) tc2.
Proof.
  intros * ? ? ? ? Hustep ?.
  assert (exists t tc1 tc2, tc = tc2 ++ (tid2, e_acq ad t) :: tc1)
    as [t [tc1 [tc2 Hacq]]]
    by eauto using onecr_multistep_onecr_aux1'.
  subst.
  assert (exists mA thsA, m1 / ths1 ~~[tc1]~~>* mA / thsA /\ mA[ad].X = false)
    as [mA [thsA [H1A Hunlocked]]]
    by eauto using onecr_multistep_onecr_aux1''.
  assert (invariants mA thsA) by eauto using invariants_preservation_ustep.
  exists tc1. exists (tc2 ++ (tid2, e_acq ad t) :: nil). exists t.
  repeat split; eauto using in_app_head, onecr_multistep_onecr_aux2.
  rewrite <- app_assoc. reflexivity.
Qed.

(* TODO -------------------------------------------------------------------- *)

Local Lemma todo : forall (ev ev' : (nat * eff)) tc,
  ~ (In ev' (ev :: tc)) ->
  (ev <> ev') /\ (~ In ev' tc).
Proof.
  intros * H. split; intro.
  - subst. eapply H. left. reflexivity.
  - eapply H. right. assumption.
Qed.

Local Lemma todotodo : forall (tid1 tid2 : nat) (e1 e2 : eff),
  (tid1, e1) <> (tid2, e2) ->
  tid1 <> tid2 \/ e1 <> e2. 
Proof.
  intros * H. rewrite pair_equal_spec in H. eapply Decidable.not_and in H; auto.
  unfold Decidable.decidable. nat_eq_dec tid1 tid2; auto.
Qed.

Local Lemma onecr_multistep_onecr_aux3'' :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad t,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    ad < #m1 ->
    tid1 <> tid2 ->
    one_cr ad ths1[tid1] ->
    ~ (In (tid2, e_acq ad t) tc) ->
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    no_cr ad ths2[tid2].
Proof.
  intros. ind_ustep.
  - admit. (* exclusivity *)
  - assert (invariants m2 ths2) by eauto using invariants_preservation_ustep.
    repeat spec.
    eapply todo in H4 as [? ?].
    spec. clear H6.
    eapply todotodo in H4 as [? | ?].
    + (* Se tid <> tid2 então continua sem cr         *) admit.
    + (* Se de um passo que não é acq continua sem cr *) admit.
Qed.

Local Lemma onecr_multistep_onecr_aux3' :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad tid t,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    ad < #m1 ->
    tid1 <> tid2 ->
    one_cr ad ths1[tid1] ->
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    ~ (In (tid, e_acq ad t) tc) ->
    m2[ad].X = false ->
    In (tid1, e_rel ad) tc.
Proof.
  intros. ind_ustep.
  - exfalso.
    assert (Hucr : unique_critical_regions m ths) by eauto with inva.
    specialize (Hucr ad) as [Hfalse Htrue]. spec.
    eauto using nocr_onecr_contradiction.
  - assert (invariants m2 ths2) by eauto using invariants_preservation_ustep.
    eapply todo in H5 as [? ?].
    repeat spec.
    assert ((e <> e_rel ad /\ m2[ad].X = false) \/
            (e =  e_rel ad /\ m2[ad].X = true ))
      as [[? ?] | [? ?]]
      by eauto 6 using unlocked_inheritance_rstep.
    + spec. simpl. eauto.
    + subst. simpl.
Abort.

Local Lemma onecr_multistep_onecr_aux3 :
  forall m1 m2 ths1 ths2 tid1 tid2 tc ad,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    ad < #m1 ->
    tid1 <> tid2 ->
    one_cr ad ths1[tid1] ->
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    m2[ad].X = false ->
    In (tid1, e_rel ad) tc.
Proof.
  intros. ind_ustep.
  - exfalso.
    assert (Hucr : unique_critical_regions m ths) by eauto with inva.
    specialize (Hucr ad) as [Hfalse Htrue]. spec.
    eauto using nocr_onecr_contradiction.
  - assert (invariants m2 ths2) by eauto using invariants_preservation_ustep.
    repeat spec.
    assert ((e <> e_rel ad /\ m2[ad].X = false) \/
            (e =  e_rel ad /\ m2[ad].X = true ))
      as [[? ?] | [? ?]]
      by eauto 6 using unlocked_inheritance_rstep.
    + spec. simpl. eauto.
    + subst. simpl.
Abort.



Check multistep_ind.

Print multistep_ind.

(*
multistep_ind :
  forall P : mem -> threads -> trace -> mem -> threads -> Prop,
  (forall m ths,
    P m ths nil m ths) ->
  (forall m1 m2 m3 ths1 ths2 ths3 tid e tc,
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    P m1 ths1 tc m2 ths2 ->
    m2 / ths2 ~~~[tid, e]~~> m3 / ths3 ->
    P m1 ths1 ((tid, e) :: tc) m3 ths3) ->
  forall m1 ths1 tc m2 ths2,
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    P m1 ths1 tc m2 ths2.
*)

Local Lemma todo : forall tcA tcB (tid1 tid2 : nat) (e1 e2 : eff),
  (tid2, e2) :: tcB = tcA ++ (tid1, e1) :: nil ->
  exists tc, (tid2, e2) :: tc ++ (tid1, e1) :: nil = (tid2, e2) :: tcB.
Proof.
  intros ? ? * H. induction tcA, tcB; intros.
  - simpl in *. invc H. eexists. eauto.
Abort.

Lemma multistep_ind_rev :
  forall P : mem -> threads -> trace -> mem -> threads -> Prop,
    (forall m ths,
      P m ths nil m ths) ->
    (forall m1 m2 ths1 ths2 tid e,
      P m1 ths1 ((tid, e) :: nil) m2 ths2) ->
    (forall m1 m2 m3 ths1 ths2 ths3 tid e tc,
      m1 / ths1 ~~~[tid, e]~~> m2 / ths2         ->
      m2 / ths2 ~~[tc]~~>* m3 / ths3             ->
      P m2 ths2 tc m3 ths3                       ->
      P m1 ths1 (tc ++ (tid, e) :: nil) m3 ths3) ->
    forall m1 ths1 tc m2 ths2,
      m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
      P m1 ths1 tc m2 ths2.
Proof.
  intros P Hbase0 Hbase1 Hind ? ? tc' ? ? Hustep.

  ind_ustep; trivial.
  rename m2 into mB; rename ths2 into thsB;
  rename m3 into m2; rename ths3 into ths2.

  gendep ths2; gendep thsB; gendep ths1.
  gendep m2;   gendep mB;   gendep m1.
  induction tc using rev_ind; intros.
  - invc_ustep.
    specialize (Hind mB m2 m2 thsB ths2 ths2 tid e nil Hrstep).
    specialize (Hind (multistep_refl m2 ths2)).
    specialize (Hind (Hbase0 m2 ths2)).
    rewrite app_nil_l in Hind.
    auto.
  - invc_ustep.
    + eapply app_cons_not_nil in H2. auto.
    + rename tid0 into tid'. rename e0 into e'. rename tc0 into tc'.
      rename m3 into mA; rename ths3 into thsA.
      rewrite H.
      rewrite app_comm_cons. destruct x.
Abort.

