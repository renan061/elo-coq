From Coq Require Import Lia.
From Coq Require Import Lists.List.

From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* monotonic-nondecreasing                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma cstep_nondecreasing_memory : forall m1 m2 ths1 ths2 tid e,
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  #m1 <= #m2.
Proof.
  intros. invc_cstep; trivial. invc_mstep; trivial; sigma; lia.
Qed.

Lemma ustep_nondecreasing_memory : forall m1 m2 ths1 ths2 tc,
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  #m1 <= #m2.
Proof.
  intros. ind_ustep; trivial.
  assert (#m2 <= #m3) by eauto using cstep_nondecreasing_memory. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* happens-before                                                            *)
(* ------------------------------------------------------------------------- *)

Notation " tc '[' ev '].ev' " := (tc[ev] or tc_default)
  (at level 9, ev at next level).

Notation " tc '[' ev '].tid' " := (fst (tc[ev] or tc_default))
  (at level 9, ev at next level).

Notation " tc '[' ev '].eff' " := (snd (tc[ev] or tc_default))
  (at level 9, ev at next level).

Reserved Notation "evA '<<' evB 'in' tc" (at level 50).

Inductive happens_before (tc : trace) : nat -> nat -> Prop :=
  | hb_thread : forall evA evB,
    evB < evA ->
    tc[evA].tid = tc[evB].tid ->
    evA << evB in tc

  | hb_sync : forall evA evB tidA tidB ad t,
    evB < evA ->
    tc[evA].ev = (tidA, e_rel ad) ->
    tc[evB].ev = (tidB, e_acq ad t) ->
    evA << evB in tc

  | hb_spawn : forall evA evB tid t,
    evB < evA -> (* TODO: is this necessary? *)
    tc[evA].eff = e_spawn tid t ->
    tc[evB].tid = tid ->
    evA << evB in tc

  | hb_trans : forall evA evB evC,
    evA << evB in tc ->
    evB << evC in tc ->
    evA << evC in tc

  where "evA '<<' evB 'in' tc" := (happens_before tc evA evB).

(* ------------------------------------------------------------------------- *)
(* safety                                                                    *)
(* ------------------------------------------------------------------------- *)

Local Lemma destruct_ustep2 : forall tc m1 m3 ths1 ths3 tid e,
  m1 / ths1 ~~[tc +++ (tid, e)]~~>* m3 / ths3 ->
  (exists m2 ths2,
    m1 / ths1 ~~[tid, e]~~>  m2 / ths2 /\
    m2 / ths2 ~~[  tc  ]~~>* m3 / ths3).
Proof.
  intros ?. induction tc; intros; invc_ustep.
  - inv_ustep. eauto using multistep.
  - match goal with
    | Hustep : _ / _ ~~[ _ ]~~>* _ / _ |- _ => 
      decompose record (IHtc _ _ _ _ _ _ Hustep); eauto using multistep
    end.
Qed.

Local Lemma destruct_ustep3 : forall tc m1 m4 ths1 ths4 tid1 tid2 e1 e2,
  m1 / ths1  ~~[(tid2, e2) :: tc +++ (tid1, e1)]~~>* m4 / ths4 ->
  (exists m2 ths2 m3 ths3,
    m1 / ths1 ~~[tid1, e1]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*      m3 / ths3 /\
    m3 / ths3 ~~[tid2, e2]~~> m4 / ths4 ).
Proof.
  intros. invc_ustep.
  match goal with H : _ / _ ~~[_]~~>* _ / _ |- _ =>
    eapply destruct_ustep2 in H; decompose record H
  end.
  repeat eexists; eauto.
Qed.

Local Lemma unlock_requires_release : forall tc m1 m2 ths1 ths2 ad,
  ad < #m1 ->
  m1[ad].X = true ->
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  m2[ad].X = false ->
  exists tid, In (tid, e_rel ad) tc.
Proof.
  induction tc; intros * Had Hx1 ? Hx2; invc_ustep.
  - rewrite Hx1 in Hx2. discriminate.
  - simpl. rename m3 into m.
    rename H4 into Hustep.
    specialize (IHtc _ _ _ _ ad Had Hx1 Hustep). invc_cstep.
    + assert (#m1 <= #m) by eauto using ustep_nondecreasing_memory.
      assert (ad < #m) by lia.
      invc_mstep.
      * auto_specialize. destruct IHtc. eauto.
      * sigma. auto_specialize. destruct IHtc. eauto.
      * auto_specialize. destruct IHtc. eauto.
      * omicron; auto_specialize; destruct IHtc; eauto.
      * omicron; auto_specialize; destruct IHtc; eauto.
      * omicron; eauto. auto_specialize. destruct IHtc. eauto.
    + auto_specialize. destruct IHtc. eauto.
Qed.

Local Lemma lock_requires_acquire : forall tc m1 m2 ths1 ths2 ad,
  ad < #m1 ->
  m1[ad].X = false ->
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  m2[ad].X = true ->
  exists tid t, In (tid, e_acq ad t) tc.
Proof.
  induction tc; intros * Had Hx1 ? Hx2; invc_ustep.
  - rewrite Hx1 in Hx2. discriminate.
  - simpl. rename m3 into m.
    rename H4 into Hustep.
    specialize (IHtc _ _ _ _ ad Had Hx1 Hustep). invc_cstep.
    + assert (#m1 <= #m) by eauto using ustep_nondecreasing_memory.
      assert (ad < #m) by lia.
      invc_mstep.
      * auto_specialize. decompose record IHtc. eauto.
      * sigma. auto_specialize. decompose record IHtc. eauto.
      * auto_specialize. decompose record IHtc. eauto.
      * omicron; auto_specialize; decompose record IHtc; eauto.
      * omicron; eauto. auto_specialize. decompose record IHtc. eauto.
      * omicron. auto_specialize. decompose record IHtc. eauto.
    + auto_specialize. decompose record IHtc. eauto.
Qed.

Local Lemma safety_wr : forall m2 m3 ths2 ths3 tc,
  m2 / ths2 ~~[tc]~~>* m3 / ths3 ->
  forall m1 m4 ths1 ths4 tidW tidR ad tW tR T,
  tidW <> tidR ->
  m1 / ths1 ~~[tidW, e_write ad tW T]~~>  m2 / ths2 ->
  m3 / ths3 ~~[tidR, e_read ad tR   ]~~>  m4 / ths4 ->
  exists mD thsD mC thsC mB thsB mA thsA tcX tcY tcZ ad' t,
    m2 / ths2 ~~[tcX              ]~~>* mA / thsA /\
    mA / thsA ~~[tidW, e_rel ad'  ]~~>  mB / thsB /\
    mB / thsB ~~[tcY              ]~~>* mC / thsC /\
    mC / thsC ~~[tidR, e_acq ad' t]~~>  mD / thsD /\
    mD / thsD ~~[tcZ              ]~~>* m3 / ths3.
Proof.
  intros * Hustep.
  induction Hustep as [| m2 mA m3 ths2 thsA ths3 tid e tc Hustep IH Hcstep];
  intros * Hneq HcstepW HcstepR. 
  - admit.
  - 
    inv_ustep.
    match goal with
    | Hustep: m2 / ths2 ~~[tc]~~>* ?m' / ?ths' |- _ =>
      rename m' into m;
      rename ths' into ths;
      rename Hustep into Hustep'
    end.

    inversion Hustep
      as [| ? mD ? ? thsD ? tidD eD ? Hustep' HcstepD]; subst;
      clear Hustep; rename Hustep' into Hustep.
    exists mD, thsD.

    specialize (IHtc m1 m2 m3 m4 ths1 ths2 ths3 ths4 tidW tidR ad tW tR T
      Hneq).
Qed.

Local Lemma safety_wr : forall m1 m4 ths1 ths4 tc tidW tidR ad tW tR T,
  tidW <> tidR ->
  m1/ ths1
    ~~[((tidR, e_read ad tR) :: tc) +++ (tidW, e_write ad tW T)]~~>*
  m4 / ths4 ->
  0 << (S (#tc)) in tc.
Proof.
  intros * Hneq Hustep.
  eapply destruct_ustep3 in Hustep
    as [m2 [ths2 [m3 [ths3 [HcstepW [Hustep_ HcstepR]]]]]].
Qed.

Local Lemma safety_write_read_neq : forall m1 m2 ths1 ths2 tc,
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  forall evW evR tidW tidR ad tW tR T,
    evW < evR ->
    tc[evW].ev = (tidW, e_write ad tW T) ->
    tc[evR].ev = (tidR, e_read ad tR) ->
    tidW <> tidR ->
    evW << evR in tc.
Proof.
  intros ? ? ? ? ? ?. ind_ustep; intros * Hlt Hw Hr Hneq.
  - invc Hw.
    destruct evW; match goal with H : tc_default = _ |- _ => invc H end.
  - destruct (nat_eq_dec evW (#tc)); destruct (nat_eq_dec evR (#tc)); subst.
    + sigma. invc Hw. invc Hr.
    + sigma. invc Hr.
    + sigma. invc Hr.
      destruct (nat_eq_dec evW 0); subst.
      * admit.
      * assert (0 < evW ) by eauto using Lt.neq_0_lt.
        induction tc.
        ** invc Hw. destruct evW; invc H1.
        ** admit. (* TODO *)
    + assert (evR < #tc) by (omicron; eauto; invc Hr).
      assert (evW < #tc) by (omicron; eauto; invc Hw).
      sigma.
      specialize (IHmultistep evW evR tidW tidR ad tW tR T Hlt Hw Hr Hneq).
      (* Prove that:
        evW < #tc ->
        evR < #tc ->
        evW << evR in tc ->
        evW << evR in (tc +++ (tid, e)) 
      *)
      shelve.
Qed.

Theorem safety_write_read :
  forall m1 m2 ths1 ths2 tc evW evR tidW tidR ad tW tR T,
    m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
    evW < evR ->
    tc[evW].ev = (tidW, e_write ad tW T) ->
    tc[evR].ev = (tidR, e_read ad tR) ->
    evW << evR in tc.
Proof.
  intros * ? ? Hw Hr.
  destruct (nat_eq_dec tidW tidR); subst.
  - eapply hb_thread; eauto. rewrite Hw. rewrite Hr. trivial.
  - eauto using safety_write_read_neq.
Qed.

(*
(* ad guards ad' in m *)
Definition guards ad ad' m := exists T,
  m[ad].ty = `x&T` /\ write_access ad' m m[ad].tm.

Definition guard_exclusivity m := forall ad1 ad2 ad,
  ad1 <> ad2 ->
  guards ad1 ad m ->
  ~ guards ad2 ad m.

Definition safe_memory_sharing1 m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  write_access ad m ths[tid1] ->
  ~ write_access ad m ths[tid2].

Definition safe_memory_sharing2 m ths := forall tid1 tid2 ad T,
  tid1 <> tid2 ->
  access ad m ths[tid1] ->
  access ad m ths[tid2] ->
  m[ad].ty = `w&T` ->
  exists ad', guards ad' ad m.
*)
