From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

From Elo Require Import PropertiesVAD.
From Elo Require Import PropertiesACC.
From Elo Require Import PropertiesUACC.
From Elo Require Import PropertiesSS.
From Elo Require Import PropertiesSMS.
From Elo Require Import Soundness.
From Elo Require Import Multistep.

Local Lemma destruct_multistep : forall tc m1 m3 ths1 ths3 tid eff,
  m1 / ths1  ~~[tc ++ (tid, eff) :: nil]~~>* m3 / ths3 ->
  (exists m2 ths2,
    m1 / ths1 ~~[tid, eff]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*      m3 / ths3).
Proof.
  intros ?. induction tc; intros * Hmultistep;
  invc_multistep.
  - inv_multistep. do 2 eexists. split; eauto using multistep.
  - match goal with
    | Hmultistep : _ / _ ~~[ _ ]~~>* _ / _ |- _ => 
      decompose record (IHtc _ _ _ _ _ _ Hmultistep);
      do 2 eexists; split; eauto using multistep
    end.
Qed.

Local Lemma cstep_read_requires_acc : forall m m' ths ths' tid ad v,
  m / ths ~~[tid, EF_Read ad v]~~> m' / ths' ->
  access ad m ths[tid].
Proof.
  intros. invc_cstep. invc_mstep. induction_tstep; eauto using access.
Qed.

Local Lemma cstep_write_requires_uacc : forall m m' ths ths' tid ad v Tr,
  forall_threads ths well_typed_term ->
  m / ths ~~[tid, EF_Write ad v Tr]~~> m' / ths' ->
  unsafe_access ad m ths[tid].
Proof.
  intros * Htype. intros. destruct (Htype tid) as [T ?].
  invc_cstep. invc_mstep. generalize dependent T.
  induction_tstep; intros; inv_type; eauto using unsafe_access.
  inv_type. eauto using unsafe_access.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

(* TODO *)
Lemma vac_length : forall m t ad,
  valid_accesses m t ->
  access ad m t ->
  ad < #m.
Proof.
  intros * Hvac Hacc.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; trivial.
  - specialize (Hvac (#m) Hacc). lia.
  - specialize (Hvac ad Hacc). lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

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
  intros. decompose sum (lt_eq_lt_dec tid (#ths)); subst;
  eauto using nacc_cstep_preservation.
  - destruct (acc_dec ad m' ths'[#ths]); subst; eauto. right.
    do 2 (split; trivial). inv_cstep; simpl_array.
    eauto using nuacc_spawn_block. intros ?. inv_uacc.
  - destruct (nat_eq_dec tid tid'); subst; simpl_array;
    inv_cstep; simpl_array; eauto with acc. inv_mstep; inv_step.
Qed.

Theorem nacc_or_sacc_multistep_preservation : forall m m' ths ths' tid ad tc,
  valid_program m ths ->
  (* --- *)
  ad < #m ->
  ~ access ad m ths[tid] ->
  m / ths ~~[tc]~~>* m' / ths' ->
  (~ access ad m' ths'[tid]) \/ (safe_access ad m' ths'[tid]).
Proof.
  intros * Hvp Hlt Hnacc **. induction_multistep; eauto.
  destruct (IHmultistep Hvp Hlt Hnacc) as [? | [? ?]]; subst.
  - assert (valid_program m' ths') by eauto using vp_multistep_preservation. 
    assert (#m <= #m')
      by eauto using multistep_monotonic_nondecreasing_memory_length.
    assert (ad < #m') by lia.
    eapply nacc_or_sacc_cstep_preservation in Hcstep as [? | [_ ?]]; subst;
    eauto with vp.
  - assert (valid_program m' ths') by eauto using vp_multistep_preservation.
    assert (#m <= #m')
      by eauto using multistep_monotonic_nondecreasing_memory_length.
    assert (ad < #m') by lia.
    destruct (acc_dec ad m'' ths''[tid]); eauto. right. split; trivial.
    eapply nuacc_cstep_preservation in Hcstep; eauto with vp.
    decompose sum (lt_eq_lt_dec tid (#ths')); subst; trivial;
    simpl_array; inv_acc.
Qed.

Lemma something :
  forall m1 m2 m3 m4 ths1 ths2 ths3 ths4 tid1 tid2 ad v1 v2 T tc,
    valid_program m1 ths1 ->

    forall_threads ths1 (valid_accesses m1) ->

    ad < #m1 ->
    ~ access ad m1 ths1[tid2] ->
    access ad m3 ths3[tid2] ->
    unsafe_access ad m1 ths1[tid1] ->

    tid1 <> tid2 ->
    m1 / ths1 ~~[tid1, EF_Write ad v1 T]~~> m2 / ths2 ->
    m2 / ths2 ~~[tc]~~>* m3 / ths3 ->
    m3 / ths3 ~~[tid2, EF_Read ad v2]~~> m4 / ths4 ->

    False.
Proof.
  intros * ? ? ? ? ? Huacc ? Hcstep1 Hmultistep Hcstep2.

  assert (valid_program m2 ths2) by eauto using vp_preservation. 
  assert (valid_program m3 ths3) by eauto using vp_multistep_preservation. 
  assert (#m1 <= #m2)
    by eauto using cstep_monotonic_nondecreasing_memory_length.
  assert (ad < #m2) by lia.
  specialize Hcstep1 as Hcstep1'.
  specialize Hmultistep as Hmultistep'.
  eapply nacc_or_sacc_cstep_preservation in Hcstep1' as [? | [_ [? Hnuacc]]];
  eauto with vp.
  + eapply nacc_or_sacc_multistep_preservation
      in Hmultistep' as [? | [? Hnuacc]];
    eauto.
    eapply memtyp_multistep_preservation in Hmultistep as Heq; eauto.
    eapply memtyp_preservation in Hcstep1 as Heq'; eauto with vp.
    rewrite Heq' in Heq.
    eapply uacc_iff_memtyp_mut in Huacc as [? Hmt1];
    eauto using uacc_then_acc with vp.
    * eapply nuacc_iff_memtyp_immut in Hnuacc as [? Hmt2]; eauto with vp.
      ** rewrite Hmt1 in Heq. rewrite Hmt2 in Heq. discriminate.
      ** eapply des_vp_ctr. eauto. (* TODO *)
    * eapply des_vp_ctr. eauto. (* TODO *)
  + eapply memtyp_preservation in Hcstep1 as Heq; eauto with vp.
    eapply uacc_iff_memtyp_mut in Huacc as [? Hmt1];
    eauto using uacc_then_acc with vp.
    * eapply nuacc_iff_memtyp_immut in Hnuacc as [? Hmt2]; eauto with vp.
      ** rewrite Hmt1 in Heq. rewrite Hmt2 in Heq. discriminate.
      ** eapply des_vp_ctr. eauto. (* TODO *)
    * eapply des_vp_ctr. eauto. (* TODO *)
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Theorem safety : forall m m' ths ths' tid1 tid2 ad v1 v2 tc T,
  valid_program m ths ->
  (* --- *)
  tid1 <> tid2 ->
  m / ths ~~[(tid2, EF_Read  ad v2  ) :: tc ++
             (tid1, EF_Write ad v1 T) :: nil]~~>* m' / ths' ->
  False.
Proof.
  intros * Hvp Hneq Hmultistep. specialize Hvp as H.
  destruct H as [Hmval [[Hmwtt Hwtt] [[Hmvad Hvad] [[Hmctr Hctr] [Hss Hsms]]]]].
  invc_multistep.

  rename m'0 into m3. rename ths'0 into ths3.
  rename H6 into Hmultistep. rename H7 into Hcstep.
  match goal with
  | H1 : _ / _ ~~[ _    ]~~>* _ / _
  , H2 : _ / _ ~~[ _, _ ]~~>  _ / _
  |- _ =>
    rename H1 into Hmultistep; rename H2 into H3_cstep
  end.

  assert (Hacc' : access ad m3 ths3[tid2])
    by eauto using cstep_read_requires_acc.
  eapply destruct_multistep in Hmultistep
    as [m2 [ths2 [H1_cstep H2_multistep]]].
  assert (Huacc : unsafe_access ad m ths[tid1])
    by eauto using cstep_write_requires_uacc.
  destruct (acc_dec ad m ths[tid2]) as [? | Hnacc];
  try solve [eapply (Hsms tid1 tid2); eauto].
  assert (Hvac : forall_threads ths (valid_accesses m))
    by (intros ?; eauto using vad_then_vac).
  assert (Hlen1 : ad < #m)
    by eauto using vac_length, cstep_write_requires_uacc, uacc_then_acc.

  eapply something; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

(*
Lemma access_granted_by_alloc_is_memory_length : forall m t t' ad v Tr,
  ~ access ad m t ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  access ad (m +++ (v, Tr)) t' ->
  ad = length m.
Proof.
  intros * Hnacc ? Hacc.
  induction_tstep; inv_nacc; inv_acc; eauto using access.
  - match goal with F : access _ _ _ |- _ => contradict F end.
    simpl_array. eapply access_add; eauto.
  - do 2 auto_specialize. eapply IHstep.
    eapply acc_asg in Hacc as [? | ?]; eauto.
    exfalso. eapply (not_access_allocated_value _ l) in HnaccL; eauto. 
    eapply (access_add _ r); eauto.
  - eapply asg_access_inverse in Hnacc as [? HnaccR].
    match goal with IH : _ -> _ -> _ -> ?x |- ?x => eapply IH; eauto end.
    eapply asg_access in Hacc as [? | ?]; eauto.
    exfalso. eapply (not_access_allocated_value _ r) in HnaccR; eauto. 
    eapply (access_add _ l); eauto.
  - eapply seq_access_inverse in Hnacc as [HnaccT1 ?].
    match goal with IH : _ -> _ -> _ -> ?x |- ?x => eapply IH; eauto end.
    eapply seq_access in Hacc as [? | ?]; eauto.
    exfalso. eapply (not_access_allocated_value _ t1) in HnaccT1; eauto. 
    eapply (access_add _ t2); eauto.
Qed.

Theorem access_needs_alloc : forall m m' t t' eff ad,
  ~ access m t ad ->
  m / t ==[eff]==> m' / t' ->
  access m' t' ad ->
  exists v, eff = (EF_Alloc ad v).
Proof.
  intros * Hnacc Hmstep Hacc. inversion Hmstep; subst.
  - contradict Hacc. eauto using none_does_not_grant_access.
  - eexists. erewrite <- access_granted_by_alloc_is_memory_length; eauto.
  - contradict Hacc. eauto using load_does_not_grant_access.
  - contradict Hacc. eauto using store_does_not_grant_access.
Qed.

Theorem access_needs_alloc_multistep : forall m m' t t' ad tc,
  ~ access m t ad ->
  m / t ==[tc]==>* m' / t' ->
  access m' t' ad ->
  exists v, In (EF_Alloc ad v) tc.
Proof.
  intros * Hnacc Hmultistep Hacc.
  induction Hmultistep; try solve [exfalso; eauto].
  destruct (access_dec m' t' ad) as [Hacc' | ?].
  - destruct (IHHmultistep Hnacc Hacc').
    eexists. right. eauto.
  - assert (Heq : exists v, eff = EF_Alloc ad v);
    eauto using access_needs_alloc.
    destruct Heq. eexists. left. eauto.
Qed.
*)

(*

(* PART 6 *)

Theorem concurrent_duplicate_alloc :
  forall m m' ths ths' tid tid' tc1 tc2 ad v v',
  ~ (m / ths ~~[tc1 ++ (tid , EF_Alloc ad v ) ::
                tc2 ++ (tid', EF_Alloc ad v') :: nil]~~>* m' / ths').
Proof.
  intros * F. inversion F; subst; clear F.
Abort.

*)
