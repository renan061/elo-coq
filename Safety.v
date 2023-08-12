From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

From Elo Require Import PropertiesVAD.
From Elo Require Import PropertiesACC.
From Elo Require Import PropertiesSS.
From Elo Require Import PropertiesSMS.
From Elo Require Import Soundness.
From Elo Require Import Multistep.

(* ------------------------------------------------------------------------- *)
(* mstep -- reflexive transitive closure                                     *)
(* ------------------------------------------------------------------------- *)

(* TODO: remove *)

Reserved Notation "m / t '==[' tc ']==>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Definition mtrace := list effect.

Inductive mmultistep : mem -> tm -> mtrace -> mem -> tm -> Prop :=
  | mmultistep_refl: forall m t,
    m / t ==[nil]==>* m / t

  | mmultistep_trans : forall m m' m'' t t' t'' tc eff,
    m  / t  ==[tc]==>* m'  / t'  ->
    m' / t' ==[eff]==> m'' / t'' ->
    m  / t  ==[eff :: tc]==>* m'' / t''

  where "m / t '==[' tc ']==>*' m' / t'" := (mmultistep m t tc m' t').

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma monotonic_nondecreasing_memory_length' : forall m m' eff t t',
  m / t ==[eff]==>* m' / t' ->
  #m <= #m'.
Proof.
  assert (forall m m' eff t t',
    m / t ==[eff]==> m' / t' ->
    length m <= length m'). {
    intros * Hmstep. inversion Hmstep; subst; eauto.
    - rewrite add_increments_length. eauto.
    - rewrite set_preserves_length. eauto.
  }
  intros * Hmmultistep. induction Hmmultistep; eauto using Nat.le_trans.
Qed.

Lemma alloc_increments_memory_length : forall m m' t t' ad v Tr,
  m / t ==[EF_Alloc ad v Tr]==> m' / t' ->
  #m' = S (#m).
Proof.
  intros. inv_mstep. eauto using add_increments_length.
Qed.

Lemma destruct_multistep' : forall tc eff m0 mF t0 tF,
  m0 / t0  ==[tc ++ eff :: nil]==>* mF / tF ->
  (exists m t, m0 / t0 ==[eff]==> m / t /\ m / t ==[tc]==>* mF / tF).
Proof.
  intros ?. induction tc as [| eff tc IH];
  intros * Hmultistep; inversion Hmultistep; subst.
  - eexists. eexists. inversion H3; subst. split; eauto using mmultistep.
  - specialize (IH _ _ _ _ _ H3) as [? [? [? ?]]].
    eexists. eexists. split; eauto using mmultistep.
Qed.

Theorem duplicate_alloc : forall m m' t t' tc ad v v' Tr Tr',
  ~ (m / t ==[EF_Alloc ad v Tr :: tc ++ EF_Alloc ad v' Tr' :: nil]==>* m' / t').
Proof.
  assert (not_Sn_le_n : forall n, ~ (S n <= n)). {
    unfold not. intros * F. induction n;
    eauto using le_S_n. inversion F.
  }
  unfold not. intros * Hmultistep.
  inversion Hmultistep; subst; clear Hmultistep;
  destruct tc; try discriminate.
  - match goal with H : _ / _ ==[_]==>* _ / _ |- _ =>
      rewrite app_nil_l in H; inversion H; subst
    end.
    match goal with
    H1 : _ / _ ==[_]==> _ / _,
    H2 : _ / _ ==[_]==> _ / _ |- _ =>
      inversion H1; inversion H2; subst;
      eapply alloc_increments_memory_length in H1;
      eapply alloc_increments_memory_length in H2
    end.
    lia.
  - match goal with
    H : _ / _ ==[_]==>* _ / _ |- _ =>
      eapply destruct_multistep' in H as [? [? [? Hmultistep']]]
    end.
    eapply monotonic_nondecreasing_memory_length' in Hmultistep'.
    match goal with
    H1 : _ / _ ==[_]==> _ / _,
    H2 : _ / _ ==[_]==> _ / _ |- _ =>
      inversion H1; inversion H2; subst
    end.
    match goal with
    | H1 : length ?x = length _, H2 : length _ <= length ?x |- _ =>
      rewrite H1 in H2;
      rewrite add_increments_length in H2
    end.
    lia.
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

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

Local Lemma split_trace3 : forall m m' ths ths' tc,
  #ths < #ths' ->
  m / ths ~~[tc]~~>* m' / ths' ->
  exists mA thsA mB thsB tc1 tc2 tid block,
    tc = tc1 ++ (tid, EF_Spawn block) :: tc2 /\
    m  / ths  ~~[tc1]~~>*                mA / thsA /\
    mA / thsA ~~[tid, EF_Spawn block]~~> mB / thsB /\
    mB / thsB ~~[tc2]~~>*                m' / ths'.
Proof.
  intros. 
  generalize dependent m'. generalize dependent ths'. 
  induction tc; intros; inv_multistep; try lia.
  rename m'0 into mA. rename ths'0 into thsA.
  specialize (IHtc thsA).
Abort.

Local Lemma spawn_sacc : forall m m' ths ths' tid ad eff,
  forall_threads ths safe_spawns ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  access ad m' ths'[#ths] ->
  ~ unsafe_access ad m' ths'[#ths].
Proof.
  intros. invc_cstep; simpl_array; intros ?;
  eauto using nomut_then_nuacc, nomut_block.
  unfold thread_default in *. inv_acc.
Qed.

Local Lemma memtyp_sacc : forall m t ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  access ad m t ->
  ~ unsafe_access ad m t ->
  exists T, m[ad].typ = <{{ i&T }}>.
Proof.
  intros * ? HctrM ? Hacc Hnuacc. induction Hacc;
  invc_ctr; try inv_nuacc.
Abort.

Lemma memtyp_immut_then_nuacc : forall m t ad T,
  value t ->
  empty |-- t is <{{ Immut T }}> ->
  ~ unsafe_access ad m t.
Proof.
  intros * Hval ? ?. destruct Hval; inv_type; inv_uacc.
Qed.

Lemma acc_then_uacc : forall m t ad T,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  m[ad].typ = <{{ &T }}> ->
  access ad m t ->
  unsafe_access ad m t .
Proof.
  intros * ? Hmctr Hctr ? Hacc. generalize dependent T.
  induction Hacc; intros; inv_ctr; eauto using unsafe_access; exfalso.
  - eapply memtyp_immut_then_nuacc; eauto.
  - rewrite H0 in H4. discriminate. 
Qed.

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

Theorem safety : forall m m' ths ths' tid1 tid2 ad v1 v2 tc Tr,
  valid_program m ths ->
  (* --- *)
  tid1 <> tid2 ->
  m / ths ~~[(tid2, EF_Read  ad v2   ) :: tc ++
             (tid1, EF_Write ad v1 Tr) :: nil]~~>* m' / ths' ->
  False.
Proof.
  intros * Hvp Hneq Hmultistep. remember Hvp as H.
  destruct H as [Hmval [[Hmwtt Hwtt] [[Hmvad Hvad] [[Hmctr Hctr] [Hss Hsms]]]]].
  invc_multistep.
  rename m'0 into m3. rename ths'0 into ths3.

  rename H6 into Hmultistep. rename H7 into Hcstep.

  assert (Hacc' : access ad m3 ths3[tid2])
    by eauto using cstep_read_requires_acc.
  match goal with
  | H1 : _ / _ ~~[ _    ]~~>* _ / _
  , H2 : _ / _ ~~[ _, _ ]~~>  _ / _
  |- _ =>
    rename H1 into Hmultistep; rename H2 into H3_cstep
  end.

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
  assert (Hlen2 : ad < #m2) by eauto using Nat.lt_le_trans,
    monotonic_nondecreasing_memory_length, multistep.

  move Hvac after Hvad.
  move H3_cstep after H2_multistep. 
  move Hacc' after Huacc.
  move m2 at top. move m3 at top.
  move Hneq at top.
  move ths2 after ths. move ths3 after ths.

  decompose sum (lt_eq_lt_dec tid2 (#ths)); subst.
  (* a thread tid2 já existia quando ocorreu o WRITE *)
  - assert (tid2 < #ths2) by eauto using Nat.lt_le_trans,
      monotonic_nondecreasing_threads_length, multistep.
    eapply (not_access_multistep_preservation m2 m3 ths2 ths3); eauto.
    + eapply memory_value_multistep_preservation; eauto using multistep.
    + eapply valid_addresses_multistep_preservation; eauto using multistep.
    + eapply typing_multistep_preservation; eauto using multistep.
    + eapply typing_multistep_preservation; eauto using multistep.
    + eapply safe_spawns_multistep_preservation; eauto using multistep.
    + eapply safe_memory_sharing_multistep_preservation; eauto using multistep.
    + eapply (not_access_multistep_preservation m m2 ths ths2);
      eauto using multistep.
  (* a thread tid2 não existia quand ocorreu o WRITE *)
  - assert (exists T, m[ad].typ = <{{&T}}>) as [T Htype1]
      by (eapply (uacc_iff_memtyp_mut _ ths[tid1]); eauto using uacc_then_acc).
    move T at top.
    eapply memtyp_preservation in H1_cstep as Htype2; eauto.
    rewrite Htype1 in Htype2.
    pose proof H2_multistep as H2.
    eapply typing_multistep_preservation in H2 as [_ [_ Hext]].
    + shelve.
    + eapply valid_addresses_multistep_preservation; eauto using multistep.
    + eapply typing_multistep_preservation; eauto using multistep.
    + eapply typing_multistep_preservation; eauto using multistep.
    Unshelve.
    assert (m3[ad].typ = <{{ &T }}>). admit.
    eapply acc_then_uacc in Hacc' as Huacc'; eauto.
    * move Huacc' before Hacc'.
      eapply Hsms.
      admit. admit. admit.
    * shelve.
    * shelve.
  - admit.
  (*
  assert (m3 extends m). {
    eapply MemExtension.trans; eauto.
  }
  by eauto using extension, MemExtension.trans.
  assert (Htype1': m3[ad].typ = m[ad].typ) by eauto using MemExtension.get.
  rewrite Htype1 in Htype1'.
  admit.
  *)
Admitted.

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
