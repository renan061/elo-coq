From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.
From Elo Require Import References.
From Elo Require Import SafeAccess.
From Elo Require Import Soundness.
From Elo Require Import Compat.
From Elo Require Import AccessProp.
From Elo Require Import Safe.

Local Definition sms1 m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access m ths[tid1] ad ->
  access m ths[tid2] ad ->
  SafeAccess m ths[tid1] ad.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Require Import Coq.Program.Equality.

Lemma refM_loop : forall T,
  T = <{{ &T }}> -> False.
Proof.
  intros T F. dependent induction T; inversion F; eauto.
Qed.

Lemma refI_loop : forall T,
  T = TY_RefI T -> False.
Proof.
  intros T F. dependent induction T; inversion F; eauto.
Qed.

Lemma the_one : forall m ad,
  well_typed_memory m ->
  access m m[ad] ad ->
  False.
Proof.
  intros * Hwtm Hacc.
  destruct (Hwtm ad) as [[T Htype] Hwtr]; eauto using access_length.
  clear Hwtr. assert (Hwtr : strong_well_typed_references m m[ad]) by admit.
  remember empty as Gamma; clear HeqGamma.
  generalize dependent Gamma. generalize dependent T.
  induction Hwtr; intros;
  inversion_subst_clear Htype;
  try solve [
    inversion_subst_clear Hacc;
    eauto
  ];
  inversion_access;
  try solve [
    auto_specialize;
    destruct (Hwtm ad0) as [[? ?] ?]; eauto using access_length
  ].
  - assert (Heq : m[ad] = <{ & ad :: (& T) }>) by admit.
    rewrite Heq in H.
    inversion H; subst.
    eauto using refM_loop.
  - assert (Heq : m[ad] = <{ & ad :: (i& T) }>) by admit.
    rewrite Heq in H.
    inversion H; subst.
    eauto using refI_loop.
Abort.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma uacc_subst : forall m t tx ad x,
  UnsafeAccess m t ad ->
  UnsafeAccess m ([x := tx] t) ad.
Proof.
  intros * Huacc. induction Huacc; eauto using UnsafeAccess.
  simpl. destruct String.string_dec; subst; eauto using UnsafeAccess.
Qed.

Lemma uacc_subst_call : forall m x Tx t t' ad,
  UnsafeAccess m ([x := t'] t) ad ->
  UnsafeAccess m <{ call <{ fn x Tx --> t }> t' }> ad.
Proof.
  intros. induction t; eauto using UnsafeAccess; simpl in *;
  try (destruct String.string_dec; eauto using UnsafeAccess);
  inversion_uacc; auto_specialize; inversion_uacc;
  try inversion_uacc; eauto using UnsafeAccess.
Qed.

Lemma mstep_none_inherits_uacc : forall m m' t t' ad,
  UnsafeAccess m' t' ad ->
  m / t ==[EF_None]==> m' / t' ->
  UnsafeAccess m  t  ad.
Proof.
  intros. inversion_mstep. induction_step; try inversion_uacc;
  eauto using UnsafeAccess, uacc_subst_call.
Qed.

Lemma todo : forall m t ad T,
  well_typed_memory m ->
  well_typed_references m t ->
  UnsafeAccess m t ad ->
  empty |-- t is (TY_Immut T) ->
  False.
Proof.
  intros * Hwtm Hwtr Huacc Htype.
  generalize dependent T.
  induction Huacc; intros;
  try solve [inversion_type; eauto];
  try solve [inversion_subst_clear Hwtr; inversion_type; eauto].
  - inversion Hwtr; subst.
    inversion Htype; subst.
    assert (ad' < length m) by admit.
    specialize (Hwtm ad').
    do 1 auto_specialize.
    decompose record Hwtm.
    eauto.
  - inversion_subst_clear Hwtr. auto_specialize.
    inversion_subst_clear Htype; eauto.
    eapply IHHuacc.
Abort.

Lemma mstep_read_inherits_access' : forall m m' t t' ad ad' v,
  access m' t' ad ->
  m / t ==[EF_Read ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros * ? ?. inversion_mstep. induction_step;
  try inversion_access; eauto using access.
  eapply access_load. 
  destruct (Nat.eq_dec ad' ad); subst.
  - eapply access_ref.
  - eapply access_mem. eauto. eauto.
Qed.

Lemma mstep_read_inherits_uacc : forall m m' t t' ad ad' v,
  UnsafeAccess m' t' ad' ->
  m / t ==[EF_Read ad v]==> m' / t' ->
  UnsafeAccess m  t  ad'.
Proof.
  intros * ? ?. inversion_mstep. induction_step;
  try inversion_uacc; try (destruct (Nat.eq_dec ad' ad); subst);
  eauto using UnsafeAccess.
  eapply uacc_load.
  assert (exists T', empty |-- <{ & ad :: T }> is T') as [T' Htype] by admit.
  inversion Htype; subst.
  + eapply uacc_ref.
  + eapply uacc_mem. admit.
Abort.

(* ------------------------------------------------------------------------- *)
(* sms1 preservation                                                         *)
(* ------------------------------------------------------------------------- *)

Local Lemma length_tid : forall m m' t' ths tid eff,
  m / ths[tid] ==[eff]==> m' / t' ->
  tid < length ths.
Proof.
  intros * Hmstep.
  decompose sum (lt_eq_lt_dec tid (length ths)); subst; trivial;
  rewrite (get_default TM_Unit) in Hmstep; try lia;
  inversion_mstep; inversion_step.
Qed.

Local Lemma none_sms1_preservation : forall m m' ths t' tid,
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  forall_threads ths (well_typed_references m) ->
  well_typed_memory m ->
  sms1 m ths ->
  m / ths[tid] ==[EF_None]==> m' / t' ->
  sms1 m' ths[tid <- t'].
Proof.
  intros * Htype ? ? Hsms1 Hmstep tid1 tid2 ad Hneq ? ?.
  destruct (Htype tid1).
  specialize (Hsms1 _ _ ad Hneq) as ?.
  specialize (Hsms1 _ _ ad (not_eq_sym Hneq)) as ?.
  assert (tid < length ths) by eauto using length_tid.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  try lia; do 3 rewrite_term_array;
  eauto using mstep_none_inherits_access.
  assert (access m' ths[tid1] ad) by eauto using mstep_none_inherits_access.
  eapply access_to_sacc; eauto using mstep_type_preservation, not_uacc_sacc,
    mstep_none_inherits_uacc.
Qed.

Local Lemma read_sms1_preservation : forall m m' ths t' tid ad v,
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  forall_threads ths (well_typed_references m) ->
  well_typed_memory m ->
  sms1 m ths ->
  m / ths[tid] ==[EF_Read ad v]==> m' / t' ->
  sms1 m' ths[tid <- t'].
Proof.
  intros * Htype ? ? Hsms1 Hmstep tid1 tid2 ad Hneq ? ?.
  destruct (Htype tid1).
  specialize (Hsms1 _ _ ad Hneq) as ?.
  specialize (Hsms1 _ _ ad (not_eq_sym Hneq)) as ?.
  assert (tid < length ths) by eauto using length_tid.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  try lia; do 3 rewrite_term_array;
  eauto using mstep_read_inherits_access.
  assert (access m' ths[tid1] ad) by eauto using mstep_read_inherits_access.

  do 4 auto_specialize.

  eapply access_to_sacc; eauto using mstep_type_preservation.
  intros F.
  eapply not_uacc_sacc; try (exact F).
    mstep_read_inherits_uacc.
Qed.

(* TODO *)
Local Lemma alloc_sms_preservation : forall m m' ths t' tid ad v,
  forall_threads ths (valid_accesses m) ->
  safe_memory_sharing m ths ->
  tid < length ths ->
  m / ths[tid] ==[EF_Alloc ad v]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * Hva Hsms ? Hmstep tid1 tid2 ad ? Hacc1 Hacc2.
  inversion Hmstep; subst.

  assert (~ access m ths[tid1] (length m)).
  { intros F. specialize (Hva tid1 (length m) F). lia. }
  assert (~ access m ths[tid2] (length m)).
  { intros F. specialize (Hva tid2 (length m) F). lia. }

  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  do 2 rewrite_term_array.
  - contradiction.
  - decompose sum (lt_eq_lt_dec ad (length m)); subst; rewrite_term_array;
    try (assert (ad <> length m) by lia);
    try (assert (Hacc1' : access m ths[tid1] ad)
      by eauto using mstep_alloc_inherits_access).
    + eauto using mem_add_inherits_access.
    + contradict Hacc2. eauto using mem_add_not_access_length.
    + specialize (Hva tid1 ad Hacc1'). lia.
  - decompose sum (lt_eq_lt_dec ad (length m)); subst; rewrite_term_array;
    try (assert (ad <> length m) by lia);
    try (assert (Hacc1' : access m ths[tid1] ad)
      by eauto using mem_add_inherits_access).
    + eauto using mstep_alloc_inherits_access.
    + contradict Hacc1. eauto using mem_add_not_access_length.
    + specialize (Hva tid1 ad Hacc1'). lia.
  - decompose sum (lt_eq_lt_dec ad (length m)); subst; rewrite_term_array;
    try (assert (ad <> length m) by lia);
    try (assert (Hacc1' : access m ths[tid1] ad)
      by eauto using mem_add_inherits_access);
    try (assert (Hacc2' : access m ths[tid2] ad)
      by eauto using mem_add_inherits_access);
    eauto.
    + contradict Hacc1. eauto using mem_add_not_access_length.
    + specialize (Hva tid1 ad Hacc1'). lia.
Qed.

Local Lemma tuburibu : forall m t t' ad v T M,
  well_typed_references m t ->
  empty |-- m[ad] is TY_Immut M ->
  empty |-- t is T ->
  t --[EF_Write ad v]--> t' ->
  False.
Proof.
  intros ? ?. induction t; intros * Hwtr HtypeM HtypeT Hstep;
  try solve [inversion_step];
  inversion Hwtr; subst;
  inversion HtypeT; subst;
  inversion Hstep; subst;
  eauto.
  do 15 auto_specialize.
  inversion H4; subst.
  inversion H1; subst.
  apply_deterministic_typing.
Abort.

Local Lemma write_sms_preservation : forall m m' ths t' tid ad v,
  safe_memory_sharing m ths ->
  tid < length ths ->
  m / ths[tid] ==[EF_Write ad v]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * Hsms ? Hmstep tid1 tid2 ad' ? Hacc1 Hacc2.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  do 2 rewrite_term_array.
  - contradiction.
  - destruct (Nat.eq_dec ad' ad); subst.
    + assert (Hacc1' : access m ths[tid1] ad)
        by eauto using mstep_write_address_access.
      assert (access m ths[tid2] ad \/ ~ access m ths[tid2] ad)
        as [Hacc2' | ?] by eauto using access_dec.
        * specialize (Hsms tid1 tid2 ad H0 Hacc1' Hacc2') as [? ?].
          eexists.
          assert (well_typed_references m ths[tid1]) by admit.
          assert (ad < length m) by admit.
          assert (exists TH, empty |-- ths[tid1] is TH) as [? ?] by admit.
          eapply mstep_memory_preservation; eauto.
        * contradict Hacc2. eauto using inaccessible_address_set_2.
    + rewrite_term_array.
      assert (Hacc1' : access m ths[tid1] ad')
        by eauto using mstep_write_inherits_access.
      eapply (Hsms tid1 tid2 ad' H0 Hacc1').
      assert (access m ths[tid2] ad \/ ~ access m ths[tid2] ad)
        as [Hacc2' | Hnacc2'] by eauto using access_dec;
      eauto using inaccessible_address_set_1.
      assert (Hacc1'' : access m ths[tid1] ad)
        by eauto using mstep_write_address_access.
      specialize (Hsms tid1 tid2 ad H0 Hacc1'' Hacc2') as [? ?].


  - admit.
  - admit.

  eauto 8 using mstep_write_address_access,
                mstep_write_inherits_access,
                mstep_write_preserves_not_access,
                inaccessible_address_set_1,
                inaccessible_address_set_2.
Qed.

Local Lemma mstep_sms_preservation : forall m m' ths t' tid eff,
  (forall tid, valid_accesses m ths[tid]) ->
  disjoint_memory m ths ->
  tid < length ths ->
  m / ths[tid] ==[eff]==> m' / t' ->
  disjoint_memory m' ths[tid <- t'].
Proof.
  intros * ? ? ? Hmstep. inversion Hmstep; subst;
  eauto using none_disjoint_memory_preservation,
              alloc_disjoint_memory_preservation,
              read_disjoint_memory_preservation,
              write_disjoint_memory_preservation.
Qed.

Theorem safe_memory_sharing_preservation : forall m m' ths ths' tid eff,
  forall_threads SafeSpawns ths ->
  forall_threads (valid_accesses m) ths ->
  safe_memory_sharing m ths ->
  tid < length ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  safe_memory_sharing m' ths'.
Proof.
  intros. inversion_cstep;
  eauto using mstep_disjoint_memory_preservation.
  intros tid1 tid2 ad Hacc Hneq.
  decompose sum (lt_eq_lt_dec (length ths) tid2); subst.
  - rewrite (get_add_gt TM_Unit);
    try solve [rewrite set_preserves_length; trivial].
    intros ?. inversion_access.
  - erewrite <- set_preserves_length.
    rewrite (get_add_eq TM_Unit).
    eauto using safe_for_block. (* safe_then_not_access *)
    admit.
  - rewrite (get_add_lt TM_Unit);
    try solve [rewrite set_preserves_length; trivial].
    decompose sum (lt_eq_lt_dec (length ths) tid1); subst.
    + rewrite (get_add_gt TM_Unit) in Hacc;
      try solve [rewrite set_preserves_length; trivial].
      inversion_access.
    + erewrite <- set_preserves_length in Hacc.
      rewrite (get_add_eq TM_Unit) in Hacc.
      (*
      assert (~ access m' block ad) by 
        eauto using safe_for_block, safe_then_not_access.
      *)
      eauto.
      admit.
    + rewrite (get_add_lt TM_Unit) in Hacc;
      try solve [rewrite set_preserves_length; trivial].
      destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto;
      do 2 rewrite_term_array;
      eauto using step_spawn_inherits_access, step_spawn_preserves_not_access.
Abort.

