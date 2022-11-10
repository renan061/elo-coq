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
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Hint Unfold decidable.

Lemma sacc_subst1 : forall m t tx ad x,
  ~ access m tx ad ->
  SafeAccess m t ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * ? Hsacc. induction Hsacc; simpl;
  eauto using SafeAccess, not_access_subst.
  destruct String.string_dec; subst; eauto  using SafeAccess.
Qed.

Lemma sacc_subst2 : forall m t tx ad x,
  access m ([x := tx] t) ad ->
  ~ access m t ad ->
  HasVar x t ->
  SafeAccess m tx ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * Hacc Hnacc Hhv Hsacc. induction t; simpl in *;
  inversion_not_access Hnacc; inversion Hhv; subst;
  try solve [inversion_access; eauto using SafeAccess];
  eauto using SafeAccess.

  - inversion Hacc; subst.
    + assert (decidable (access m ([x := tx] t2) ad)) as [? | ?];
      assert (decidable (HasVar x t2)) as [? | ?]; 
      eauto using SafeAccess, access_dec, hasvar_dec.
      match goal with
      | H : ~ HasVar _ ?t |- _ =>
        replace ([x := tx] t) with t in *;
        eauto using SafeAccess, hasvar_subst, eq_sym
      end.
    + assert (decidable (access m ([x := tx] t1) ad)) as [? | ?];
      assert (decidable (HasVar x t2)) as [? | ?];
      eauto using SafeAccess, access_dec, hasvar_dec;
      do 2 auto_specialize.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
        exfalso. eauto.

  - inversion Hacc; subst.
    + assert (decidable (access m ([x := tx] t2) ad)) as [? | ?];
      assert (decidable (HasVar x t1)) as [? | ?]; 
      eauto using SafeAccess, access_dec, hasvar_dec;
      do 2 auto_specialize.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
        exfalso. eauto.
    + assert (decidable (access m ([x := tx] t1) ad)) as [? | ?];
      assert (decidable (HasVar x t1)) as [? | ?];
      eauto using SafeAccess, access_dec, hasvar_dec;
      do 2 auto_specialize.
      match goal with
      | H : ~ HasVar _ ?t |- _ =>
        replace ([x := tx] t) with t in *;
        eauto using SafeAccess, hasvar_subst, eq_sym
      end.

  - destruct String.string_dec; eauto. contradiction.

  - destruct String.string_dec; eauto; try contradiction.
    inversion Hacc; subst;
    eauto using SafeAccess.

  - inversion Hacc; subst.
    + assert (decidable (access m ([x := tx] t2) ad)) as [? | ?];
      assert (decidable (HasVar x t2)) as [? | ?]; 
      eauto using SafeAccess, access_dec, hasvar_dec.
      match goal with
      | H : ~ HasVar _ ?t |- _ =>
        replace ([x := tx] t) with t in *;
        eauto using SafeAccess, hasvar_subst, eq_sym
      end.
    + assert (decidable (access m ([x := tx] t1) ad)) as [? | ?];
      assert (decidable (HasVar x t2)) as [? | ?];
      eauto using SafeAccess, access_dec, hasvar_dec;
      do 2 auto_specialize.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
        exfalso. eauto.

  - inversion Hacc; subst.
    + assert (decidable (access m ([x := tx] t2) ad)) as [? | ?];
      assert (decidable (HasVar x t1)) as [? | ?]; 
      eauto using SafeAccess, access_dec, hasvar_dec;
      do 2 auto_specialize.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
        exfalso. eauto.
    + assert (decidable (access m ([x := tx] t1) ad)) as [? | ?];
      assert (decidable (HasVar x t1)) as [? | ?];
      eauto using SafeAccess, access_dec, hasvar_dec;
      do 2 auto_specialize.
      match goal with
      | H : ~ HasVar _ ?t |- _ =>
        replace ([x := tx] t) with t in *;
        eauto using SafeAccess, hasvar_subst, eq_sym
      end.

  - inversion Hacc; subst.
    + assert (decidable (access m ([x := tx] t2) ad)) as [? | ?];
      assert (decidable (HasVar x t2)) as [? | ?]; 
      eauto using SafeAccess, access_dec, hasvar_dec.
      match goal with
      | H : ~ HasVar _ ?t |- _ =>
        replace ([x := tx] t) with t in *;
        eauto using SafeAccess, hasvar_subst, eq_sym
      end.
    + assert (decidable (access m ([x := tx] t1) ad)) as [? | ?];
      assert (decidable (HasVar x t2)) as [? | ?];
      eauto using SafeAccess, access_dec, hasvar_dec;
      do 2 auto_specialize.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
        exfalso. eauto.

  - inversion Hacc; subst.
    + assert (decidable (access m ([x := tx] t2) ad)) as [? | ?];
      assert (decidable (HasVar x t1)) as [? | ?]; 
      eauto using SafeAccess, access_dec, hasvar_dec;
      do 2 auto_specialize.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
      * match goal with
        | H : ~ HasVar _ ?t |- _ =>
          replace ([x := tx] t) with t in *;
          eauto using SafeAccess, hasvar_subst, eq_sym
        end.
        exfalso. eauto.
    + assert (decidable (access m ([x := tx] t1) ad)) as [? | ?];
      assert (decidable (HasVar x t1)) as [? | ?];
      eauto using SafeAccess, access_dec, hasvar_dec;
      do 2 auto_specialize.
      match goal with
      | H : ~ HasVar _ ?t |- _ =>
        replace ([x := tx] t) with t in *;
        eauto using SafeAccess, hasvar_subst, eq_sym
      end.
Qed.

Lemma sacc_subst3 : forall m t tx ad x,
  SafeAccess m t ad ->
  SafeAccess m tx ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * Hsacc ?.
  induction Hsacc; simpl; eauto using SafeAccess.
  - assert (decidable (SafeAccess m ([x := tx] t2) ad)) as [? | ?];
    eauto using classic_decidable, SafeAccess.
    assert (decidable (access m ([x := tx] t2) ad)) as [? | ?];
    eauto using access_dec, SafeAccess.
    assert (decidable (HasVar x t2)) as [? | ?];
    eauto using hasvar_dec.
    + eauto using SafeAccess, sacc_subst2.
    + rewrite (hasvar_subst _ t2) in *; eauto. contradiction.
  - assert (decidable (SafeAccess m ([x := tx] t1) ad)) as [? | ?];
    eauto using classic_decidable, SafeAccess.
    assert (decidable (access m ([x := tx] t1) ad)) as [? | ?];
    eauto using access_dec, SafeAccess.
    assert (decidable (HasVar x t1)) as [? | ?];
    eauto using hasvar_dec.
    + eauto using SafeAccess, sacc_subst2.
    + rewrite (hasvar_subst _ t1) in *; eauto. contradiction.
  - destruct String.string_dec; eauto using SafeAccess.
  - assert (decidable (SafeAccess m ([x := tx] t2) ad)) as [? | ?];
    eauto using classic_decidable, SafeAccess.
    assert (decidable (access m ([x := tx] t2) ad)) as [? | ?];
    eauto using access_dec, SafeAccess.
    assert (decidable (HasVar x t2)) as [? | ?];
    eauto using hasvar_dec.
    + eauto using SafeAccess, sacc_subst2.
    + rewrite (hasvar_subst _ t2) in *; eauto. contradiction.
  - assert (decidable (SafeAccess m ([x := tx] t1) ad)) as [? | ?];
    eauto using classic_decidable, SafeAccess.
    assert (decidable (access m ([x := tx] t1) ad)) as [? | ?];
    eauto using access_dec, SafeAccess.
    assert (decidable (HasVar x t1)) as [? | ?];
    eauto using hasvar_dec.
    + eauto using SafeAccess, sacc_subst2.
    + rewrite (hasvar_subst _ t1) in *; eauto. contradiction.
  - assert (decidable (SafeAccess m ([x := tx] t2) ad)) as [? | ?];
    eauto using classic_decidable, SafeAccess.
    assert (decidable (access m ([x := tx] t2) ad)) as [? | ?];
    eauto using access_dec, SafeAccess.
    assert (decidable (HasVar x t2)) as [? | ?];
    eauto using hasvar_dec.
    + eauto using SafeAccess, sacc_subst2.
    + rewrite (hasvar_subst _ t2) in *; eauto. contradiction.
  - assert (decidable (SafeAccess m ([x := tx] t1) ad)) as [? | ?];
    eauto using classic_decidable, SafeAccess.
    assert (decidable (access m ([x := tx] t1) ad)) as [? | ?];
    eauto using access_dec, SafeAccess.
    assert (decidable (HasVar x t1)) as [? | ?];
    eauto using hasvar_dec.
    + eauto using SafeAccess, sacc_subst2.
    + rewrite (hasvar_subst _ t1) in *; eauto. contradiction.
Qed.

Lemma sacc_subst_call : forall m x Tx t t' ad,
  SafeAccess m ([x := t'] t) ad ->
  SafeAccess m <{ call <{ fn x Tx --> t }> t' }> ad.
Proof.
  (*
  intros * Hsacc. induction t;
  try solve [inversion Hsacc].
  - inversion Hsacc; subst.


  eauto using SafeAccess; simpl in *.
  try (destruct String.string_dec; eauto using SafeAccess).
  inversion_sacc; auto_specialize; inversion_sacc;
  try inversion_sacc; eauto using SafeAccess.
  *)
Abort.


Lemma mstep_none_preserves_sacc : forall m m' t t' ad,
  SafeAccess m t ad ->
  m / t ==[EF_None]==> m' / t' ->
  access m' t' ad ->
  SafeAccess m' t' ad.
Proof.
  intros * Hsacc ? Hacc. inversion_mstep.
  remember m' as m; clear Heqm. (* TODO *)
  induction_step; inversion_sacc; eauto;
  try solve [inversion_access; eauto using SafeAccess];
  try solve [
    inversion_access;
    eauto using SafeAccess, step_none_preserves_not_access;
    try solve [
      match goal with
      | IH : _ -> access _ ?t _ -> _ -> _ |- _ =>
        assert (decidable (access m t ad)) as [? | ?];
        eauto using SafeAccess, access_dec
      end
    ];
    try solve [
      exfalso; eauto using not_access_then_not_sacc
    ]
  ].
  - inversion_sacc. eauto using sacc_subst3.
  - inversion_sacc. eauto using sacc_subst1.
  - inversion_not_access H4; clear H4.
    assert (decidable (HasVar x t)) as [? | ?] by eauto using hasvar_dec.
    + eauto using sacc_subst2.
    + replace ([x := v] t) with t in *; eauto using hasvar_subst, eq_sym.
      exfalso. eauto.
  - exfalso. eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* safe_memory_sharing preservation                                          *)
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

Local Lemma none_sms_preservation : forall m m' ths t' tid,
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

Local Lemma read_sms_preservation : forall m m' ths t' tid ad v,
  forall_threads ths (fun t => exists T, empty |-- t is T) ->
  forall_threads ths (well_typed_references m) ->
  well_typed_memory m ->
  sms m ths ->
  m / ths[tid] ==[EF_Read ad v]==> m' / t' ->
  sms m' ths[tid <- t'].
Proof.
  intros * Htype ? ? Hsms Hmstep tid1 tid2 ad Hneq ? ?.
  destruct (Htype tid1).
  specialize (Hsms _ _ ad Hneq) as ?.
  specialize (Hsms _ _ ad (not_eq_sym Hneq)) as ?.
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

