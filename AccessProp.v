From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import Compat.
From Elo Require Import WBA.

(* -------------------------------------------------------------------------- *)
(* Mem ---------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

Module Mem.
  Module Add.
    Lemma preserves_access : forall m t ad v,
      access m t ad ->
      access (add m v) t ad.
    Proof.
      intros * Hacc. induction Hacc; eauto using access.
      eapply access_mem.
      destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]. 
      - rewrite (get_add_lt TM_Unit); trivial.
      - subst. rewrite (get_default TM_Unit) in IHHacc; try lia.
        inversion_access.
      - rewrite (get_default TM_Unit) in IHHacc; try lia.
        inversion_access.
    Qed.
  End Add.

  Module Set_.
    Lemma preserves_access : forall m t ad ad' v,
      ~ access m v ad ->
      access (set m ad' v) t ad ->
      access m t ad.
    Proof.
      intros * Hnacc Hacc. remember (set m ad' v) as m'.
      induction Hacc; inversion Heqm'; subst; eauto using access.
      match goal with 
        IH : ~ _ -> access _ (getTM (set _ ?ad1 _) ?ad2) ?ad3 |- _ =>
          destruct (Nat.eq_dec ad1 ad2); subst;
          try solve [rewrite (get_set_neq TM_Unit) in IH; eauto using access];
          destruct (Nat.eq_dec ad2 ad3); subst; eauto using access
      end.
      exfalso. rewrite (get_set_eq TM_Unit) in IHHacc; eauto.
      eapply not_le. intros F. rewrite (get_default TM_Unit) in Hacc.
      - inversion_access.
      - rewrite set_preserves_length. trivial.
    Qed.

    Local Lemma preserves_not_access : forall m t ad ad' v,
      ~ access m t ad ->
      ~ access m v ad ->
      ~ access (set m ad' v) t ad.
    Proof.
      assert (ge_iff_le : forall m n, m >= n <-> n <= m). {
        intros. split; destruct n; eauto.
      }
      assert (forall m ad ad' v,
        access (set m ad' v) (getTM (set m ad' v) ad') ad ->
        ad' < length m). {
        intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
        rewrite (get_set_invalid TM_Unit) in H; trivial. inversion H.
      }
      intros * HnaccT HnaccV F.
      remember (set m ad' v) as m'.
      induction F; inversion Heqm'; subst; eauto using access.
      match goal with H : ~ access _ (TM_Loc ?ad) _ |- _ => 
        destruct (Nat.eq_dec ad' ad) as [? | Hneq]; subst
      end. 
      - match goal with H : ~ access _ (TM_Loc ?ad) _ |- _ => 
          assert (ad < length m); eauto
        end. 
        rewrite (get_set_eq TM_Unit) in F;
        rewrite (get_set_eq TM_Unit) in IHF; eauto.
      - eapply not_eq_sym in Hneq.
        rewrite (get_set_neq TM_Unit) in *; eauto using access.
    Qed.
  End Set_.
End Mem.

(*****************************************************************************)
(* Step **********************************************************************)
(*****************************************************************************)

Lemma step_alloc_address_access2 : forall m t t' ad v,
  t --[EF_Alloc ad v]--> t' ->
  access m t' ad.
Proof.
  intros. induction_step; eauto using access.
Qed. 

Lemma step_store_value_access : forall m t t' ad ad' v,
  access m v ad ->
  t --[EF_Store ad' v]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; eauto using access.
Qed.

Lemma step_store_value_not_access : forall m t t' ad ad' v,
  ~ access m t ad ->
  t --[EF_Store ad' v]--> t' ->
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
  intros. induction_step; inversion_not_access;
  eauto using not_access_load, not_access_asg, not_access_call, not_access_seq.
Qed.

(*****************************************************************************)
(* MStep *********************************************************************)
(*****************************************************************************)

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
  intros. inversion_mstep. induction_step; inversion_not_access;
  eauto using not_access_load, not_access_asg, not_access_call, not_access_seq.
  inversion_not_access. eauto using not_access_subst.
Qed.

Local Lemma mstep_alloc_address_access: forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros. inversion_mstep. eauto using step_alloc_address_access2.
Qed.

Lemma mstep_alloc_grants_access : forall m m' t t' ad v,
  well_behaved_access m t ->
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  ~ access m t ad /\ access m' t' ad.
Proof.
  intros * Hwba ?. split; eauto using mstep_alloc_address_access.
  inversion_mstep. intros F. eapply Hwba in F. lia.
Qed.

Lemma mstep_alloc_inherits_access : forall m m' t t' ad ad' v,
  well_behaved_access m t ->
  ad <> ad' ->
  access m' t' ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros * Hwba ? ? Hmstep. inversion_mstep. induction_step;
  WBA.destruct_wba; try inversion_access; eauto using access; try lia.
  - rewrite (get_add_eq TM_Unit) in *.
    eapply access_new; eapply inaccessible_address_add_1; eauto. intros F.
    specialize (Hwba (length m) F). lia.
  - eapply access_asg2; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
  - eapply access_asg1; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
  - eapply access_call2; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
  - eapply access_call1; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
  - eapply access_seq2; eapply inaccessible_address_add_1; eauto. intros F.
    match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
Qed.

Lemma mstep_alloc_preserves_access : forall m m' t t' ad ad' v,
  access m t ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros. inversion_mstep. induction_step; inversion_access;
  eauto using access, Mem.Add.preserves_access.
  eapply access_mem. rewrite (get_add_eq TM_Unit).
  eauto using Mem.Add.preserves_access.
Qed.

Lemma mstep_alloc_preserves_not_access : forall m m' t t' ad ad' v,
  well_behaved_access m t ->
  ad <> ad' ->
  ~ access m t ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hwba ? ? ?. inversion_mstep.
  induction_step; WBA.destruct_wba; inversion_not_access;
  eauto using access, not_access_load. 
  - intros ?. inversion_access; eauto.
    rewrite (get_add_eq TM_Unit) in *.
    eapply inaccessible_address_add_2; eauto. intros F.
    specialize (Hwba (length m) F). lia.
  - eapply not_access_asg; eauto. eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
  - eapply not_access_asg; eauto; eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
  - eapply not_access_call; eauto; eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
  - eapply not_access_call; eauto; eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
  - eapply not_access_seq; eauto; eapply inaccessible_address_add_2; eauto.
    intros F. match goal with Hwba : well_behaved_access m ?t |- _ =>
      specialize (Hwba (length m) F); lia
    end.
Qed.

Lemma mstep_load_address_access: forall m m' t t' ad v,
  m / t ==[EF_Load ad v]==> m' / t' ->
  access m t ad.
Proof.
  intros. inversion_mstep. induction_step; eauto using access.
Qed.

Lemma mstep_load_inherits_access : forall m m' t t' ad ad' v,
  access m' t' ad ->
  m / t ==[EF_Load ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros * ? ?. inversion_mstep. induction_step;
  try inversion_access; eauto using access.
Qed.

Lemma mstep_load_preserves_access : forall m m' t t' ad ad' v,
  ad <> ad' ->
  access m t ad ->
  m / t ==[EF_Load ad' v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros * Hneq Hacc Hmstep. inversion_mstep. induction_step;
  inversion_access; eauto using access.
  inversion_access; subst; trivial. exfalso. eauto.
Qed.

Lemma mstep_load_preserves_not_access : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Load ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * ? ?. inversion_mstep. induction_step;
  eauto using access; inversion_not_access;
  eauto using not_access_load, not_access_asg, not_access_call, not_access_seq.
Qed.

Lemma mstep_store_address_access: forall m m' t t' ad v,
  m / t ==[EF_Store ad v]==> m' / t' ->
  access m t ad.
Proof.
  intros * ?. inversion_mstep. induction_step; eauto using access.
Qed.

Lemma mstep_store_inherits_access : forall m m' t t' ad ad' v,
  access m' t' ad ->
  m / t ==[EF_Store ad' v]==> m' / t' ->
  access m t ad.
Proof.
  intros. inversion_mstep. induction_step;
  try inversion_access; eauto using access;
  destruct (access_dec m v ad);
  eauto using access, step_store_value_access, Mem.Set_.preserves_access.
Qed.

Lemma mstep_store_preserves_not_access : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Store ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc ?. inversion_mstep. induction_step; inversion_not_access;
  eauto using not_access_load, not_access_asg, not_access_call, not_access_seq,
              Mem.Set_.preserves_not_access, step_store_value_not_access.
Qed.
