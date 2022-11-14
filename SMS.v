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

Local Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access m ths[tid1] ad ->
  access m ths[tid2] ad ->
  SafeAccess m ths[tid1] ad.

(* ------------------------------------------------------------------------- *)
(* SafeAccess Lemmas                                                         *)
(* ------------------------------------------------------------------------- *)

Hint Unfold decidable.

Lemma sacc_subst1 : forall m t tx ad x,
  ~ access m tx ad ->
  SafeAccess m t ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * ? Hsacc. induction Hsacc; simpl;
  eauto using SafeAccess, not_access_subst.
  destruct String.string_dec; subst; eauto using SafeAccess.
Qed.

Lemma sacc_subst2 : forall m t tx ad x,
  ~ access m t ad ->
  access m ([x := tx] t) ad ->
  SafeAccess m tx ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * Hnacc ? ?. induction t; simpl in *;
  try (destruct String.string_dec);
  try inversion_access; inversion_not_access Hnacc;
  eauto using SafeAccess; try contradiction;
  match goal with
  | _ : not_access m (_ ?t1 ?t2) _, _ : access m ([_ := _] ?t1) _ |- _ =>
    assert (decidable (access m ([x := tx] t2) ad)) as [? | ?]
  | _ : not_access m (_ ?t1 ?t2) _, _ : access m ([_ := _] ?t2) _ |- _ =>
    assert (decidable (access m ([x := tx] t1) ad)) as [? | ?]
  end;
  eauto using access_dec, SafeAccess.
Qed.

Lemma sacc_subst3 : forall m t tx ad x,
  SafeAccess m t ad ->
  SafeAccess m tx ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * Hsacc ?.
  induction Hsacc; simpl; try (destruct String.string_dec);
  eauto using SafeAccess;
  match goal with
  | _ : SafeAccess _ ?t1 _, _ : ~ access _ ?t2 _ |- _ =>
    assert (decidable (SafeAccess m ([x := tx] t2) ad)) as [? | ?];
    assert (decidable (access m ([x := tx] t2) ad)) as [? | ?]
  | _ : SafeAccess _ ?t2 _, _ : ~ access _ ?t1 _ |- _ =>
    assert (decidable (SafeAccess m ([x := tx] t1) ad)) as [? | ?];
    assert (decidable (access m ([x := tx] t1) ad)) as [? | ?]
  end;
  eauto using classic_decidable, access_dec, sacc_subst2, SafeAccess.
Qed.

Corollary sacc_subst_call : forall m x Tx t tx ad,
  access m ([x := tx] t) ad ->
  ~ access m <{ fn x Tx --> t }> ad ->
  SafeAccess m tx ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * ? Hnacc ?. inversion_not_access Hnacc. eauto using sacc_subst2.
Qed.

Local Lemma mem_add_preserves_sacc : forall Gamma m t ad v T,
  well_typed_memory m ->
  Gamma |-- t is T ->
  ~ access m t (length m) ->
  SafeAccess m t ad ->
  SafeAccess (m +++ v) t ad.
Proof.
  intros * Hwtm Htype Hnacc Hsacc.
  generalize dependent Gamma. generalize dependent T.
  induction Hsacc; intros;
  inversion_type; inversion_not_access Hnacc; eauto using SafeAccess;
  eauto using SafeAccess, mem_add_nacc_lt.
  - eapply sacc_memI; trivial.
    decompose sum (lt_eq_lt_dec ad' (length m)); subst; try lia;
    rewrite_term_array.
    + eauto using mem_add_preserves_access.
    + exfalso. rewrite get_default in H0; try lia. inversion H0.
  - eapply sacc_memM; trivial.
    decompose sum (lt_eq_lt_dec ad' (length m)); subst; try lia;
    rewrite_term_array.
    + destruct (Hwtm ad') as [[? ?] _]; eauto.
    + exfalso. rewrite get_default in Hsacc. 2: lia. inversion Hsacc.
Qed.

Lemma mstep_none_preserves_sacc : forall m m' t t' ad,
  SafeAccess m t ad ->
  m / t ==[EF_None]==> m' / t' ->
  access m' t' ad ->
  SafeAccess m' t' ad.
Proof.
  intros * Hsacc ? Hacc. inversion_mstep. rename m' into m.
  induction_step; inversion_sacc; try inversion_access;
  eauto using sacc_subst_call, step_none_preserves_not_access, SafeAccess;
  solve
    [ match goal with
      | IH : _ -> access _ ?t _ -> _ -> _ |- _ =>
        assert (decidable (access m t ad)) as [? | ?];
        eauto using access_dec, SafeAccess
      end
    | exfalso; eauto
    | inversion_sacc; eauto using sacc_subst1, sacc_subst3
    ].
Qed.

Lemma mstep_alloc_preserves_sacc : forall m t t' ad v T,
  well_typed_memory m ->
  valid_accesses m t ->
  empty |-- t is T ->
  SafeAccess m t ad ->
  t --[EF_Alloc (length m) v]--> t' ->
  SafeAccess (m +++ v) t' ad.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_va.
  - inversion_type; inversion_sacc; eauto using SafeAccess.
  - inversion_type; inversion_sacc.
    + eapply sacc_memM.
      destruct (Nat.eq_dec ad (length m)); subst; eauto using SafeAccess.
      * exfalso. eapply va_nacc_length; eauto using sacc_then_access.
      * rewrite_term_array.
        eapply mem_add_preserves_sacc; eauto using va_nacc_length.
    + destruct (Nat.eq_dec ad (length m)); subst; eauto using SafeAccess.
      eapply sacc_memI; trivial.
      rewrite_term_array.
      eauto using mem_add_preserves_access, sacc_then_access.
  - inversion_type; inversion_sacc; eauto using SafeAccess.
  - inversion_type; inversion_sacc.
    + eauto using mem_add_preserves_sacc, va_nacc_length, SafeAccess.
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H7. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_nacc_lt, va_nacc_length, SafeAccess.
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H7. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_preserves_sacc, step_alloc_preserves_nacc,
          va_nacc_length, SafeAccess. 
  - inversion_type; inversion_sacc.
    + eauto using mem_add_preserves_sacc, va_nacc_length, SafeAccess.
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H8. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_preserves_sacc, step_alloc_preserves_nacc,
          va_nacc_length, SafeAccess. 
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H8. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_nacc_lt, va_nacc_length, SafeAccess.
  - inversion_type; inversion_sacc.
    + eauto using mem_add_preserves_sacc, va_nacc_length, SafeAccess.
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H7. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_nacc_lt, va_nacc_length, SafeAccess.
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H7. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_preserves_sacc, step_alloc_preserves_nacc,
          va_nacc_length, SafeAccess. 
  - inversion_type; inversion_sacc.
    + eauto using mem_add_preserves_sacc, va_nacc_length, SafeAccess.
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H8. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_preserves_sacc, step_alloc_preserves_nacc,
          va_nacc_length, SafeAccess. 
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H8. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_nacc_lt, va_nacc_length, SafeAccess.

  - inversion_type; inversion_sacc.
    + eauto using mem_add_preserves_sacc, va_nacc_length, SafeAccess.
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H7. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_nacc_lt, va_nacc_length, SafeAccess.
    + destruct (Nat.eq_dec ad (length m)); subst.
      * contradict H7. intros F. eapply sacc_then_access in F.
        eapply va_nacc_length. 2: exact F. trivial.
      * eauto using mem_add_preserves_sacc, step_alloc_preserves_nacc,
          va_nacc_length, SafeAccess. 
Qed.

Lemma mstep_read_preserves_sacc : forall m m' t t' ad ad' v,
  forall_memory m value ->
  well_typed_references m t ->
  SafeAccess m t ad ->
  m / t ==[EF_Read ad' v]==> m' / t' ->
  access m' t' ad ->
  SafeAccess m' t' ad.
Proof.
  intros. inversion_mstep. rename m' into m.
  induction_step; inversion_wtr m; inversion_sacc; try inversion_access;
  eauto using SafeAccess, step_read_preserves_not_access;
  solve
    [ match goal with
      | IH : _ -> _ -> access _ ?t _ -> _ -> _ |- _ =>
        assert (decidable (access m t ad)) as [? | ?];
        eauto using access_dec, SafeAccess
      end
    | exfalso; eauto
    | inversion_wtr m; inversion_sacc; eauto using sacc_strong_transitivity 
    ].
Qed.

(* ------------------------------------------------------------------------- *)
(* safe-memory-sharing preservation                                          *)
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

Local Lemma mstep_none_sms_preservation : forall m m' ths t' tid,
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  forall_threads ths (well_typed_references m) ->
  well_typed_memory m ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[EF_None]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * Htype ? ? Hsms Hmstep tid1 tid2 ad Hneq ? ?.
  destruct (Htype tid1).
  specialize (Hsms _ _ ad Hneq) as ?.
  specialize (Hsms _ _ ad (not_eq_sym Hneq)) as ?.
  assert (tid < length ths) by eauto using length_tid.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  try lia; do 3 rewrite_term_array;
  eauto using mstep_none_inherits_access.
  assert (access m' ths[tid1] ad) by eauto using mstep_none_inherits_access.
  eauto using mstep_none_preserves_sacc.
Qed.

Local Lemma mstep_read_sms_preservation : forall m m' ths t' tid ad v,
  forall_memory m value ->
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  forall_threads ths (well_typed_references m) ->
  well_typed_memory m ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[EF_Read ad v]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * ? Htype ? ? Hsms Hmstep tid1 tid2 ad Hneq ? ?.
  destruct (Htype tid1).
  specialize (Hsms _ _ ad Hneq) as ?.
  specialize (Hsms _ _ ad (not_eq_sym Hneq)) as ?.
  assert (tid < length ths) by eauto using length_tid.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  try lia; do 3 rewrite_term_array;
  eauto using mstep_read_inherits_access.
  assert (access m' ths[tid1] ad) by eauto using mstep_read_inherits_access.
  eauto using mstep_read_preserves_sacc.
Qed.

Local Lemma mstep_alloc_sms_preservation : forall m m' ths t' tid ad v,
  well_typed_memory m ->
  forall_threads ths (valid_accesses m) ->
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  safe_memory_sharing m ths ->
  m / ths[tid] ==[EF_Alloc ad v]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
Proof.
  intros * ? ? Htype Hsms Hmstep tid1 tid2 ad Hneq Hacc1 Hacc2.
  specialize (Hsms _ _ ad Hneq) as ?.
  specialize (Hsms _ _ ad (not_eq_sym Hneq)) as ?.
  assert (tid < length ths) by eauto using length_tid.
  inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst;
  try lia; do 3 rewrite_term_array.
  
  - destruct (Htype tid1).
    destruct (Nat.eq_dec ad (length m)); subst.
    + eapply mem_add_inherits_access in Hacc2; eauto using va_nacc_length.
      contradict Hacc2. eauto using va_nacc_length. 
    + assert (access m ths[tid1] ad); 
      assert (access m ths[tid2] ad);
      eauto using mstep_alloc_inherits_acc,
        va_nacc_length, mem_add_inherits_access.
      eauto using mstep_alloc_preserves_sacc.
  - destruct (Htype tid1).
    destruct (Nat.eq_dec ad (length m)); subst.
    + eapply mem_add_inherits_access in Hacc1; eauto using va_nacc_length.
      contradict Hacc1. eauto using va_nacc_length. 
    + assert (access m ths[tid1] ad); 
      assert (access m ths[tid2] ad);
      eauto using mstep_alloc_inherits_acc,
        va_nacc_length, mem_add_inherits_access.
      eauto using va_nacc_length, mem_add_preserves_sacc.
  - destruct (Htype tid1).
    destruct (Nat.eq_dec ad (length m)); subst.
    + eapply mem_add_inherits_access in Hacc1; eauto using va_nacc_length.
      contradict Hacc1. eauto using va_nacc_length. 
    + assert (access m ths[tid1] ad); 
      assert (access m ths[tid2] ad);
      eauto using mstep_alloc_inherits_acc,
        va_nacc_length, mem_add_inherits_access.
      eauto using va_nacc_length, mem_add_preserves_sacc.
Qed.

Local Lemma mstep_write_sms_preservation : forall m m' ths t' tid ad v,
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
  safe_memory_sharing m ths ->
  m / ths[tid] ==[eff]==> m' / t' ->
  safe_memory_sharing m' ths[tid <- t'].
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

