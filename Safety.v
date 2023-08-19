From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

From Elo Require Import MemTyp.
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
    eapply nuacc_cstep_preservation in Hcstep; eauto with vp.
    decompose sum (lt_eq_lt_dec tid (#ths')); subst; trivial;
    simpl_array; inv_acc.
Qed.

Theorem safety : forall m m' ths ths' tid1 tid2 ad v1 v2 tc T,
  valid_program m ths ->
  (* --- *)
  tid1 <> tid2 ->
  m / ths ~~[(tid2, EF_Read  ad v2  ) :: tc ++
             (tid1, EF_Write ad v1 T) :: nil]~~>* m' / ths' ->
  False.
Proof.
  intros * Hvp Hneq Hmultistep. specialize Hvp as H.
  destruct H as [? [[? ?] [[? ?] [[? ?] [? Hsms]]]]].
  invc_multistep.
  (* some renamings to make the hypotheses readable *)
  match goal with
  | H1 : ?m / ?ths ~~[ _    ]~~>* ?m' / ?ths'
  , H2 : _  / _    ~~[ _, _ ]~~>  _   / _
  |- _ =>
    rename m into m1; rename ths into ths1;
    rename m' into m3; rename ths' into ths3;
    eapply destruct_multistep in H1 as [m2 [ths2 [Hcstep1___ Hmultistep]]];
    move H2 after Hmultistep; rename H2 into Hcstep2___
  end.
  (* --- *)
  assert (Hvac : forall_threads ths1 (valid_accesses m1))
    by (intros ?; eauto using vad_then_vac).
  assert (valid_program m2 ths2) by eauto using vp_preservation. 
  assert (valid_program m3 ths3) by eauto using vp_preservation. 
  (* --- *)
  assert (#m1 <= #m2)
    by eauto using cstep_monotonic_nondecreasing_memory_length.
  assert (ad < #m1)
    by eauto using vac_length, cstep_write_requires_uacc, uacc_then_acc.
  assert (ad < #m2) by lia.
  (* --- *)
  assert (Hacc : access ad m3 ths3[tid2])
    by eauto using cstep_read_requires_acc.
  assert (Huacc : unsafe_access ad m1 ths1[tid1])
    by eauto using cstep_write_requires_uacc.
  assert (Hnacc : ~ access ad m1 ths1[tid2])
    by (intros ?; eapply (Hsms tid1 tid2); eauto).
  (* --- *)
  assert (m1[ad].typ = m2[ad].typ) as HeqA by eauto using memtyp_preservation.
  eapply nacc_or_sacc_cstep_preservation in Hcstep1___ as [? | [_ Hsacc]];
  eauto with vp.
  + assert (m2[ad].typ = m3[ad].typ) as HeqB by eauto using memtyp_preservation.
    eapply nacc_or_sacc_multistep_preservation in Hmultistep as [? | Hsacc];
    eauto.
    rewrite HeqB in HeqA.
    eapply (memtyp_inconsistency m3 m1 ths3[tid2] ths1[tid1]); eauto with vp.
  + eapply (memtyp_inconsistency m2 m1 ths2[tid2] ths1[tid1]); eauto with vp.
Qed.

