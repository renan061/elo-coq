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

Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access m ths[tid1] ad ->
  access m ths[tid2] ad ->
  (SafeAccess m ths[tid1] ad /\
   SafeAccess m ths[tid2] ad /\
   exists T, empty |-- m[ad] is TY_Immut T).

Local Lemma none_sms_preservation : forall m m' ths t' tid,
  safe_memory_sharing m ths ->
  tid < length ths ->
  m / ths[tid] ==[EF_None]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * Hsms ? Hmstep tid1 tid2 ? ? ? ?. inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; try lia;
  do 3 (rewrite_array TM_Unit).
  - assert (access m' ths[tid1] ad) by eauto using mstep_none_inherits_access.
    specialize (Hsms tid1 tid2 ad). do 3 auto_specialize. decompose record Hsms.
    split; try split; eauto; try rewrite_array TM_Unit.
    (* TODO: fazer a preservação de SafeAccess. Isso é verdade? *)
    admit.
  - admit.
  - admit.
Qed.

Local Lemma read_sms_preservation : forall m m' ths t' tid ad v,
  safe_memory_sharing m ths ->
  tid < length ths ->
  m / ths[tid] ==[EF_Read ad v]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * ? ? Hmstep tid1 tid2 ? ? ?. inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto;
  do 2 (rewrite_array TM_Unit); eauto using mstep_read_inherits_access.
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
  do 2 (rewrite_array TM_Unit).
  - contradiction.
  - decompose sum (lt_eq_lt_dec ad (length m)); subst; rewrite_array TM_Unit;
    try (assert (ad <> length m) by lia);
    try (assert (Hacc1' : access m ths[tid1] ad)
      by eauto using mstep_alloc_inherits_access).
    + eauto using mem_add_inherits_access.
    + contradict Hacc2. eauto using mem_add_not_access_length.
    + specialize (Hva tid1 ad Hacc1'). lia.
  - decompose sum (lt_eq_lt_dec ad (length m)); subst; rewrite_array TM_Unit;
    try (assert (ad <> length m) by lia);
    try (assert (Hacc1' : access m ths[tid1] ad)
      by eauto using mem_add_inherits_access).
    + eauto using mstep_alloc_inherits_access.
    + contradict Hacc1. eauto using mem_add_not_access_length.
    + specialize (Hva tid1 ad Hacc1'). lia.
  - decompose sum (lt_eq_lt_dec ad (length m)); subst; rewrite_array TM_Unit;
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
  do 2 (rewrite_array TM_Unit).
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
    + rewrite_array TM_Unit.
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
      do 2 (rewrite_array TM_Unit);
      eauto using step_spawn_inherits_access, step_spawn_preserves_not_access.
Abort.

