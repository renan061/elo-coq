From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import Compat.

(* ------------------------------------------------------------------------- *)
(* Mem                                                                       *)
(* ------------------------------------------------------------------------- *)

Module Mem.
  Module Add.
    Lemma preserves_access : forall m t ad v,
      access m t ad ->
      access (m +++ v) t ad.
    Proof.
      intros * Hacc. induction Hacc; eauto using access.
      destruct (Nat.eq_dec ad ad'); subst; eauto using access.
      eapply access_mem; trivial.
      decompose sum (lt_eq_lt_dec ad' (length m)); subst.
      - rewrite_array TM_Unit; trivial.
      - rewrite (get_default TM_Unit) in IHHacc; try lia. inversion_access.
      - rewrite (get_default TM_Unit) in IHHacc; try lia. inversion_access.
    Qed.
  End Add.

  Module Set_.
    Lemma preserves_access : forall m t ad ad' v,
      ~ access m v ad ->
      access m[ad' <- v] t ad ->
      access m t ad.
    Proof.
      intros * Hnacc Hacc. remember (m[ad' <- v]) as m'.
      induction Hacc; inversion Heqm'; subst; eauto using access.
      match goal with 
        IH : ~ _ -> access _ _[?ad1 <- _][?ad2] ?ad3 |- _ =>
          destruct (Nat.eq_dec ad1 ad2); subst;
          try solve [rewrite (get_set_neq TM_Unit) in IH; eauto using access];
          destruct (Nat.eq_dec ad2 ad3); subst; eauto using access
      end.
      exfalso. rewrite (get_set_eq TM_Unit) in IHHacc; eauto.
      eapply not_le. intros ?. rewrite (get_default TM_Unit) in Hacc.
      - inversion_access.
      - rewrite set_preserves_length. trivial.
    Qed.

    Local Lemma preserves_not_access : forall m t ad ad' v,
      ~ access m t ad ->
      ~ access m v ad ->
      ~ access m[ad' <- v] t ad.
    Proof.
      assert (ge_iff_le : forall m n, m >= n <-> n <= m). {
        intros. split; destruct n; eauto.
      }
      assert (forall m ad ad' v,
        access (set m ad' v) m[ad' <- v][ad'] ad ->
        ad' < length m). {
        intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
        rewrite (get_set_invalid TM_Unit) in H; trivial. inversion H.
      }
      intros * HnaccT HnaccV F.
      remember (m[ad' <- v]) as m'.
      induction F; inversion Heqm'; subst; eauto using access.
      match goal with _ : ~ access _ <{ & ?ad :: _ }> _ |- _ => 
        destruct (Nat.eq_dec ad' ad) as [? | Hneq]; subst;
        try (assert (ad < length m) by eauto)
      end;
      do 2 (rewrite_array TM_Unit); eauto using access.
    Qed.
  End Set_.
End Mem.

(* ------------------------------------------------------------------------- *)
(* Step                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma alloc_step_access_t'_ad : forall m t t' ad v,
  t --[EF_Alloc ad v]--> t' ->
  access m t' ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma write_step_access_t_ad : forall m t t' ad ad' v,
  access m v ad ->
  t --[EF_Write ad' v]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma write_step_not_access_v : forall m t t' ad ad' v,
  ~ access m t ad ->
  t --[EF_Write ad' v]--> t' ->
  ~ access m v ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma step_spawn_inherits_access : forall m t t' ad block,
  access m t' ad ->
  t --[EF_Spawn block]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; try inversion_access; eauto using access.
Qed.

Lemma step_spawn_preserves_not_access : forall m t t' ad block,
  ~ access m t ad ->
  t --[EF_Spawn block]--> t' ->
  ~ access m t' ad.
Proof.
  intros * Hnacc ?. induction_step;
  eapply not_access_iff; eapply not_access_iff in Hnacc;
  inversion_clear Hnacc; eauto using not_access.
Qed.

(* ------------------------------------------------------------------------- *)
(* MStep -- None                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma mstep_none_inherits_access : forall m m' t t' ad,
  access m' t' ad ->
  m / t ==[EF_None]==> m' / t' ->
  access m t ad.
Proof.
  intros. inversion_mstep. induction_step;
  try inversion_access; eauto using access, access_subst.
Qed.

Lemma mstep_none_preserves_not_access : forall m m' t t' ad,
  ~ access m t ad ->
  m / t ==[EF_None]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc ?. inversion_mstep.
  induction_step; inversion_not_access Hnacc;
  eapply not_access_iff; eauto using not_access.
  eapply not_access_iff. eauto using not_access_subst.
Qed.

(* ------------------------------------------------------------------------- *)
(* MStep -- Alloc                                                            *)
(* ------------------------------------------------------------------------- *)

Local Lemma mstep_alloc_address_access: forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros. inversion_mstep. eauto using alloc_step_access_t'_ad.
Qed.

Lemma mstep_alloc_grants_access : forall m m' t t' ad v,
  valid_accesses m t ->
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  ~ access m t ad /\ access m' t' ad.
Proof.
  intros * Hva ?. split; eauto using mstep_alloc_address_access.
  inversion_mstep. intros F. eapply Hva in F. lia.
Qed.

Lemma mstep_alloc_inherits_access : forall m m' t t' ad ad' v,
  valid_accesses m t ->
  ad <> ad' ->
  access m' t' ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros * Hva ? ? Hmstep. inversion_mstep. induction_step;
  inversion_va; try inversion_access; eauto using access; try lia.
  - rewrite (get_add_eq TM_Unit) in *.
    eapply access_new; eapply inaccessible_address_add_1; eauto. intros F.
    specialize (Hva (length m) F). lia.
  - eapply access_asg2; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
  - eapply access_asg1; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
  - eapply access_call2; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
  - eapply access_call1; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
  - eapply access_seq2; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
Qed.

Lemma mstep_alloc_preserves_access : forall m m' t t' ad ad' v,
  access m t ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros. inversion_mstep. induction_step; inversion_access;
  eauto using access, Mem.Add.preserves_access.
  destruct (Nat.eq_dec ad (length m)); subst; eauto using access.
  eapply access_mem; trivial. rewrite (get_add_eq TM_Unit).
  eauto using Mem.Add.preserves_access.
Qed.

Lemma mstep_alloc_preserves_not_access : forall m m' t t' ad ad' v,
  valid_accesses m t ->
  ad <> ad' ->
  ~ access m t ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hva ? Hnacc ?. inversion_mstep.
  induction_step; inversion_va;
  eapply not_access_iff; inversion_not_access Hnacc;
  eauto using access, not_access. 
  - eapply not_access_ref; eauto.
    rewrite_array TM_Unit.
    eapply inaccessible_address_add_2; eauto. intros F.
    specialize (Hva (length m) F). lia.
  - eapply not_access_asg; eauto. eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
  - eapply not_access_asg; eauto. eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
  - eapply not_access_call; eauto. eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
  - eapply not_access_call; eauto. eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
  - eapply not_access_seq; eauto; eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hva : valid_accesses m ?t |- _ =>
      specialize (Hva (length m) F); lia
    end.
Qed.

(* ------------------------------------------------------------------------- *)
(* MStep -- Read                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma mstep_read_address_access: forall m m' t t' ad v,
  m / t ==[EF_Read ad v]==> m' / t' ->
  access m t ad.
Proof.
  intros. inversion_mstep. induction_step; eauto using access.
Qed.

Lemma mstep_read_inherits_access : forall m m' t t' ad ad' v,
  access m' t' ad ->
  m / t ==[EF_Read ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros * ? ?. inversion_mstep. induction_step;
  try inversion_access; eauto using access.
  destruct (Nat.eq_dec ad' ad); subst; eauto using access.
Qed.

Lemma mstep_read_preserves_access : forall m m' t t' ad ad' v,
  ad <> ad' ->
  access m t ad ->
  m / t ==[EF_Read ad' v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros * Hneq Hacc Hmstep. inversion_mstep. induction_step;
  inversion_access; eauto using access.
  inversion_access; subst; trivial. exfalso. eauto.
Qed.

Lemma mstep_read_preserves_not_access : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Read ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc ?. inversion_mstep. induction_step; inversion_not_access Hnacc;
  try solve [eapply not_access_iff; eauto using not_access].
  match goal with
  | H : ~ access _ _ _ |- _ => inversion_not_access H 
  end.
Qed.

(* ------------------------------------------------------------------------- *)
(* MStep -- Write                                                            *)
(* ------------------------------------------------------------------------- *)

Lemma mstep_write_address_access: forall m m' t t' ad v,
  m / t ==[EF_Write ad v]==> m' / t' ->
  access m t ad.
Proof.
  intros * ?. inversion_mstep. induction_step; eauto using access.
Qed.

Lemma mstep_write_inherits_access : forall m m' t t' ad ad' v,
  access m' t' ad ->
  m / t ==[EF_Write ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros. inversion_mstep. induction_step;
  try inversion_access; eauto using access;
  destruct (access_dec m v ad);
  eauto using access, write_step_access_t_ad, Mem.Set_.preserves_access.
Qed.

Lemma mstep_write_preserves_not_access : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Write ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc ?. inversion_mstep. induction_step;
  inversion_not_access Hnacc; eapply not_access_iff; eauto using not_access.
  - eapply not_access_asg; eauto using not_access,
      Mem.Set_.preserves_not_access, write_step_not_access_v. 
  - eapply not_access_asg; eauto using not_access,
      Mem.Set_.preserves_not_access, write_step_not_access_v. 
  - eapply not_access_call; eauto using not_access,
      Mem.Set_.preserves_not_access, write_step_not_access_v. 
  - eapply not_access_call; eauto using not_access,
      Mem.Set_.preserves_not_access, write_step_not_access_v. 
  - eapply not_access_seq; eauto using not_access,
      Mem.Set_.preserves_not_access, write_step_not_access_v. 
Qed.

