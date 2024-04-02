From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Elo Require Import Map.
From Elo Require Import Properties.
From Elo Require Import Lemmas.
From Elo Require Import Preservation.
From Elo Require Import PtrTyp.
From Elo Require Import Soundness.
From Elo Require Import Multistep.

Local Lemma multistep_app : forall m1 m2 m3 ths1 ths2 ths3 tcA tcB,
  m1 / ths1 ~~[tcA]~~>* m2 / ths2 ->
  m2 / ths2 ~~[tcB]~~>* m3 / ths3 ->
  m1 / ths1 ~~[tcB ++ tcA]~~>* m3 / ths3.
Proof.
  intros * ? Hmultistep. induction Hmultistep; eauto using multistep.
Qed.

Local Corollary multistep_append : forall m1 m2 m3 ths1 ths2 ths3 tid e tc,
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  m2 / ths2 ~~[tc]~~>* m3 / ths3 ->
  m1 / ths1 ~~[tc +++ (tid, e)]~~>* m3 / ths3.
Proof.
  eauto using multistep, multistep_app.
Qed.

Local Lemma destruct_multistep2 : forall tc m1 m3 ths1 ths3 tid e,
  m1 / ths1  ~~[tc ++ (tid, e) :: nil]~~>* m3 / ths3 ->
  (exists m2 ths2,
    m1 / ths1 ~~[tid, e]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*    m3 / ths3).
Proof.
  intros ?. induction tc; intros * Hmultistep; invc_mulst.
  - inv_mulst. eauto using multistep.
  - match goal with
    | Hmultistep : _ / _ ~~[ _ ]~~>* _ / _ |- _ => 
      decompose record (IHtc _ _ _ _ _ _ Hmultistep); eauto using multistep
    end.
Qed.

Local Lemma destruct_multistep3 : forall tc m1 m4 ths1 ths4 tid1 tid2 e1 e2,
  m1 / ths1  ~~[(tid2, e2) :: tc ++ (tid1, e1) :: nil]~~>* m4 / ths4 ->
  (exists m2 ths2 m3 ths3,
    m1 / ths1 ~~[tid1, e1]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*      m3 / ths3 /\
    m3 / ths3 ~~[tid2, e2]~~> m4 / ths4 ).
Proof.
  intros. invc_mulst.
  match goal with H : _ / _ ~~[_]~~>* _ / _ |- _ =>
    eapply destruct_multistep2 in H; decompose record H
  end.
  do 4 eexists. splits 3; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Theorem spawned_thread_nacc_or_sacc : forall m m' ths ths' tid ad e,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths well_typed_term ->
  forall_threads ths safe_spawns ->
  safe_memory_sharing m ths ->
  (* --- *)
  ad < #m ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  ~ access ad m' ths'[#ths] \/ safe_access ad m' ths'[#ths].
Proof.
  intros. destruct (acc_dec ad m' ths'[#ths]); subst; eauto.
  right. split; trivial. inv_cstep; simpl_array; eauto using spawn_nuacc.
  intros ?. inv_uacc.
Qed.

Theorem nacc_or_sacc_cstep_preservation : forall m m' ths ths' tid tid' ad e,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths well_typed_term ->
  forall_threads ths safe_spawns ->
  safe_memory_sharing m ths ->
  (* --- *)
  ad < #m ->
  ~ access ad m ths[tid] ->
  m / ths ~~[tid', e]~~> m' / ths' ->
  (~ access ad m' ths'[tid]) \/ (tid = #ths /\ safe_access ad m' ths'[tid]).
Proof.
  pose proof nacc_preservation.
  intros. decompose sum (lt_eq_lt_dec tid (#ths)); subst; eauto.
  - destruct (acc_dec ad m' ths'[#ths]); subst; eauto. right.
    do 2 (split; trivial). inv_cstep; simpl_array.
    eauto using spawn_nuacc. intros ?. inv_uacc.
  - destruct (nat_eq_dec tid tid'); subst; simpl_array;
    inv_cstep; simpl_array; eauto with acc. inv_mstep; inv_tstep.
Qed.

Theorem nacc_or_sacc_preservation : forall m m' ths ths' tid ad tc,
  valid_program m ths ->
  (* --- *)
  ad < #m ->
  ~ access ad m ths[tid] ->
  m / ths ~~[tc]~~>* m' / ths' ->
  (~ access ad m' ths'[tid]) \/ (safe_access ad m' ths'[tid]).
Proof.
  intros * Hvp Hlt Hnacc **. induction_mulst; eauto.
  destruct (IHmultistep Hvp Hlt Hnacc) as [? | [? ?]]; subst.
  - assert (valid_program m' ths') by eauto using vp_preservation. 
    assert (#m <= #m')
      by eauto using multistep_monotonic_nondecreasing_memory_length.
    assert (ad < #m') by lia.
    eapply nacc_or_sacc_cstep_preservation in Hcstep as [? | [_ ?]]; subst;
    eauto with vp.
  - assert (valid_program m' ths') by eauto using vp_preservation.
    assert (#m <= #m')
      by eauto using multistep_monotonic_nondecreasing_memory_length.
    assert (ad < #m') by lia.
    destruct (acc_dec ad m'' ths''[tid]); eauto. right. split; trivial.
    eapply nuacc_preservation in Hcstep; eauto with vp.
    decompose sum (lt_eq_lt_dec tid (#ths')); subst; trivial;
    simpl_array; inv_acc.
Qed.

Theorem safety_write_read :
  forall m m' ths ths' tid1 tid2 ad v1 v2 tc tc' T,
    valid_program m ths ->
    (* --- *)
    tid1 <> tid2 ->
    m / ths ~~[tc]~~>* m' / ths' ->
    tc <> (tid2, EF_Read ad v2) :: tc' ++ (tid1, EF_Write ad v1 T) :: nil.
Proof.
  intros * Hvp Hneq Hmultistep Heq. rewrite Heq in Hmultistep.
  specialize Hvp as H; destruct H as [_ [[_ ?] [[? ?] [[_ _] [_ Hsms]]]]].
  rename m into m1. rename ths into ths1.
  eapply destruct_multistep3 in Hmultistep
    as [m2 [ths2 [m3 [ths3 [Hcstep1___ [Hmultistep Hcstep2___]]]]]].
  (* --- *)
  assert (valid_program m2 ths2) by eauto using vp_preservation. 
  assert (valid_program m3 ths3) by eauto using vp_preservation. 
  (* --- *)
  assert (ad < #m1)
    by eauto using vad_acc, write_requires_uacc, uacc_then_acc.
  (* --- *)
  assert (Hacc : access ad m3 ths3[tid2])
    by eauto using read_requires_acc.
  assert (Huacc : unsafe_access ad m1 ths1[tid1])
    by eauto using write_requires_uacc.
  assert (Hnacc : ~ access ad m1 ths1[tid2])
    by (intros ?; eapply (Hsms tid1 tid2); eauto).
  (* --- *)
  assert (H' : m1 / ths1 ~~[tc' +++ (tid1, EF_Write ad v1 T)]~~>* m3 / ths3)
    by eauto using multistep_append.
  assert (m1[ad].typ = m3[ad].typ) by eauto using memtyp_preservation.
  eapply nacc_or_sacc_preservation in H' as [? | ?]; eauto with vp.
  eapply (ptyp_sacc_uacc_contradiction m3 m1 ths3[tid2] ths1[tid1]);
  eauto with vp.
Qed.

Theorem safety_write_write :
  forall m m' ths ths' tid1 tid2 ad v1 v2 tc tc' T1 T2,
    valid_program m ths ->
    (* --- *)
    tid1 <> tid2 ->
    m / ths ~~[tc]~~>* m' / ths' ->
    tc <> (tid2, EF_Write ad v2 T2) :: tc' ++ (tid1, EF_Write ad v1 T1) :: nil.
Proof.
  intros * Hvp Hneq Hmultistep Heq. rewrite Heq in Hmultistep.
  specialize Hvp as H; destruct H as [? [[? ?] [[? ?] [[? ?] [? Hsms]]]]].
  rename m into m1. rename ths into ths1.
  eapply destruct_multistep3 in Hmultistep
    as [m2 [ths2 [m3 [ths3 [Hcstep1___ [Hmultistep Hcstep2___]]]]]].
  (* --- *)
  assert (valid_program m2 ths2) by eauto using vp_preservation. 
  assert (Hvp3 : valid_program m3 ths3) by eauto using vp_preservation. 
  destruct Hvp3 as [? [[? ?] [[? ?] [[? ?] [? Hsms3]]]]].
  (* --- *)
  assert (ad < #m1)
    by eauto using vad_acc, write_requires_uacc, uacc_then_acc.
  (* --- *)
  assert (Huacc1 : unsafe_access ad m1 ths1[tid1])
    by eauto using write_requires_uacc.
  assert (Huacc3 : unsafe_access ad m3 ths3[tid2])
    by (eapply write_requires_uacc; eauto; eapply des_vp_wtt; eauto).
  assert (Hnacc : ~ access ad m1 ths1[tid2])
    by (intros ?; eapply (Hsms tid1 tid2); eauto).
  assert (Hnacc2 : ~ access ad m3 ths3[tid1])
    by (intros ?; eapply (Hsms3 tid2 tid1); eauto).
  (* --- *)
  assert (H' : m1 / ths1 ~~[tc' +++ (tid1, EF_Write ad v1 T1)]~~>* m3 / ths3)
    by eauto using multistep_append.
  assert (m1[ad].typ = m3[ad].typ) by eauto using memtyp_preservation.
  eapply nacc_or_sacc_preservation in H' as [? | ?];
  eauto using uacc_then_acc.
  eapply (ptyp_sacc_uacc_contradiction m3 m1 ths3[tid2] ths1[tid1]); eauto.
Qed.

