From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Coq Require Logic.ClassicalFacts.

From Elo Require Import Array.
From Elo Require Import Core0.

Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_mem : forall ad ad',
    access m (getTM m ad') ad ->
    access m (TM_Loc ad') ad

  | access_loc : forall ad,
    access m (TM_Loc ad) ad

  | access_new : forall t ad,
    access m t ad ->
    access m (TM_New t) ad

  | access_load : forall t ad,
    access m t ad ->
    access m (TM_Load t) ad

  | access_asg1 : forall l r ad,
    access m l ad ->
    access m (TM_Asg l r) ad

  | access_asg2 : forall l r ad,
    access m r ad ->
    access m (TM_Asg l r) ad

  | access_seq1 : forall t1 t2 ad,
    access m t1 ad ->
    access m (TM_Seq t1 t2) ad

  | access_seq2 : forall t1 t2 ad,
    access m t2 ad ->
    access m (TM_Seq t1 t2) ad
  .

(* strong access_mem *)
Theorem access_get_trans : forall m t ad ad',
  access m t ad' ->
  access m (getTM m ad') ad ->
  access m t ad.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access.
Qed.

Definition well_behaved_access m t :=
  forall ad, access m t ad -> ad < length m.

Local Axiom excluded_middle : ClassicalFacts.excluded_middle.

Lemma access_dec : forall m t ad,
  (access m t ad) \/ (~ access m t ad).
Proof.
  eauto using excluded_middle.
Qed.

Ltac inversion_access :=
  match goal with
    | H : access _ TM_Nil       _ |- _ => inversion H; clear H
    | H : access _ (TM_Num _)   _ |- _ => inversion H; clear H
    | H : access _ (TM_Loc _)   _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_New _)   _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_Load _)  _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_Asg _ _) _ |- _ => inversion H; subst; clear H
    | H : access _ (TM_Seq _ _) _ |- _ => inversion H; subst; clear H
  end.

Lemma inversion_not_access_loc : forall m ad ad',
  ~ access m (TM_Loc ad) ad' ->
  ~ access m (getTM m ad) ad'.
Proof.
  intros * ? F. inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_new : forall m t ad,
  ~ access m (TM_New t) ad ->
  ~ access m t ad.
Proof.
  intros * ? F. inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_load : forall m t ad,
  ~ access m (TM_Load t) ad ->
  ~ access m t ad.
Proof.
  intros * ? F. inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_asg : forall m l r ad,
  ~ access m (TM_Asg l r) ad ->
  ~ access m l ad /\ ~ access m r ad.
Proof.
  intros * ?. split; intros F; inversion F; subst; eauto using access.
Qed.

Lemma inversion_not_access_seq : forall m t1 t2 ad,
  ~ access m (TM_Seq t1 t2) ad ->
  ~ access m t1 ad /\ ~ access m t2 ad.
Proof.
  intros * ?. split; intros F; inversion F; subst; eauto using access.
Qed.

Ltac inversion_not_access :=
  match goal with
    | H : _ |- ~ access _ TM_Nil _   =>
        intros F; inversion F 
    | H : _ |- ~ access _ (TM_Num _) _   =>
        intros F; inversion F 
    | H : ~ access _ (TM_Loc _) _   |- _ =>
        eapply inversion_not_access_loc in H
    | H : ~ access _ (TM_New _) _   |- _ =>
        eapply inversion_not_access_new in H
    | H : ~ access _ (TM_Load _) _  |- _ =>
        eapply inversion_not_access_load in H
    | H : ~ access _ (TM_Asg _ _) _ |- _ =>
        eapply inversion_not_access_asg in H as [? ?]
    | H : ~ access _ (TM_Seq _ _) _ |- _ =>
        eapply inversion_not_access_seq in H as [? ?]
  end.

Lemma not_access_new : forall m t ad,
  ~ access m t ad ->
  ~ access m (TM_New t) ad.
Proof.
  intros * ? ?. inversion_access. eauto.
Qed.

Lemma not_access_load : forall m t ad,
  ~ access m t ad ->
  ~ access m (TM_Load t) ad.
Proof.
  intros * ? ?. inversion_access. eauto.
Qed.

Lemma not_access_asg : forall m l r ad,
  ~ access m l ad ->
  ~ access m r ad ->
  ~ access m (TM_Asg l r) ad.
Proof.
  intros * ? ? ?. inversion_access; eauto.
Qed.

Lemma not_access_seq : forall m t1 t2 ad,
  ~ access m t1 ad ->
  ~ access m t2 ad ->
  ~ access m (TM_Seq t1 t2) ad.
Proof.
  intros * ? ? ?. inversion_access; eauto.
Qed.

(*****************************************************************************)
(* Compat ********************************************************************)
(*****************************************************************************)

Module Compat.
  Definition compat m m' t := forall ad,
    access m t ad ->
    getTM m ad = getTM m' ad.

  Lemma refl : forall m t, 
    compat m m t.
  Proof.
    intros. unfold compat. trivial.
  Qed.

  Lemma sym : forall m m' t, 
    compat m  m' t ->
    compat m' m  t. 
  Proof.
    intros * Hcompat ad Hacc. unfold compat in *.
    induction Hacc; eauto using access;
    try solve [symmetry; eauto using access].
    eapply IHHacc. intros ? ?.
    eapply Hcompat. eapply access_mem.
    rewrite (Hcompat _ (access_loc _ _)).
    trivial.
  Qed.

  Lemma acc : forall m m' t ad,
    compat m m' t ->
    access m  t ad ->
    access m' t ad.
  Proof.
    intros * Hcompat Hacc. unfold compat in *.
    induction Hacc; eauto using access.
    eapply access_mem.
    rewrite <- (Hcompat _ (access_loc _ _)).
    eapply IHHacc. intros ? ?.
    eapply Hcompat. eauto using access.
  Qed.

  Lemma acc_not : forall m m' t ad,
    compat m m' t ->
    ~ access m  t ad ->
    ~ access m' t ad.
  Proof.
    intros * ? ? ?. eauto using acc, sym.
  Qed.

  Corollary access_iff : forall m m' t ad,
    compat m m' t ->
    access m t ad <-> access m' t ad.
  Proof.
    intros * ?. split; eauto using acc, sym.
  Qed.

  Lemma inaccessible_address_set : forall m m' t ad v,
    compat m m' t ->
    ~ access m t ad ->
    compat m (set m' ad v) t.
  Proof.
    intros * Hcompat Hnacc ad Hacc. unfold compat in *.
    induction Hacc; try solve [inversion_not_access; eauto using access].
    match goal with H : ~ access _ _ ?ad' |- _ => 
      destruct (Nat.eq_dec ad ad'); subst
    end.
    - exfalso. eauto using access.
    - rewrite (get_set_neq TM_Nil); eauto using access.
  Qed.

  Lemma inaccessible_address_add : forall m m' t v,
    compat m m' t ->
    ~ access m t (length m') ->
    compat m (add m' v) t.
  Proof.
    intros * Hcompat Hnacc ad Hacc. unfold compat in *.
    induction Hacc; try solve [inversion_not_access; eauto using access].
    destruct (Nat.eq_dec ad (length m')); subst.
    + exfalso. eauto using access.
    + destruct (not_eq ad (length m')); trivial.
      * rewrite (get_add_lt TM_Nil); eauto using access.
      * specialize (Hcompat ad (access_loc m ad)).
        rewrite (get_default TM_Nil m') in Hcompat; try lia.
        rewrite (get_add_gt TM_Nil); trivial.
  Qed.
End Compat.

Corollary inaccessible_address_set_1 : forall m t ad ad' v,
  ~ access m t ad' ->
  access (set m ad' v) t ad ->
  access m t ad.
Proof.
  intros * ? ?.
  eauto using Compat.refl,
              Compat.sym,
              Compat.inaccessible_address_set,
              Compat.acc.
Qed.

Corollary inaccessible_address_set_2  : forall m t ad ad' v,
  ~ access m t ad' ->
  ~ access m t ad ->
  ~ access (set m ad' v) t ad.
Proof.
  intros * ? ?.
  eauto using Compat.refl, Compat.inaccessible_address_set, Compat.acc_not.
Qed.

Corollary inaccessible_address_add_1 : forall m t ad v,
  ~ access m t (length m) ->
  access (add m v) t ad ->
  access m t ad.
Proof.
  intros * ? ?.
  eauto using Compat.refl,
              Compat.sym,
              Compat.inaccessible_address_add,
              Compat.acc.
Qed.

Corollary inaccessible_address_add_2 : forall m t ad v,
  ~ access m t (length m) ->
  ~ access m t ad ->
  ~ access (add m v) t ad.
Proof.
  intros * ? ?.
  eauto using Compat.refl, Compat.inaccessible_address_add, Compat.acc_not.
Qed.

(*****************************************************************************)
(* WBA ***********************************************************************)
(*****************************************************************************)

Module WBA.
  Lemma destruct_new : forall m t,
    well_behaved_access m (TM_New t) ->
    well_behaved_access m t.
  Proof.
    intros * ? ?; eauto using access.
  Qed.

  Lemma destruct_load : forall m t,
    well_behaved_access m (TM_Load t) ->
    well_behaved_access m t.
  Proof.
    intros * ? ?; eauto using access.
  Qed.

  Lemma destruct_asg : forall m l r,
    well_behaved_access m (TM_Asg l r) ->
    well_behaved_access m l /\ well_behaved_access m r.
  Proof.
    intros * ?. split; intros ?; eauto using access.
  Qed.

  Lemma destruct_seq : forall m t1 t2,
    well_behaved_access m (TM_Seq t1 t2) ->
    well_behaved_access m t1 /\ well_behaved_access m t2.
  Proof.
    intros * ?. split; intros ?; eauto using access.
  Qed.

  Ltac destruct_wba :=
    match goal with
      | H : well_behaved_access _ (TM_New _)   |- _ =>
          eapply destruct_new in H
      | H : well_behaved_access _ (TM_Load _)  |- _ =>
          eapply destruct_load in H
      | H : well_behaved_access _ (TM_Asg _ _) |- _ => 
          eapply destruct_asg in H as [? ?]
      | H : well_behaved_access _ (TM_Seq _ _) |- _ => 
          eapply destruct_seq in H as [? ?]
    end.

  Local Lemma wba_load : forall m t,
    well_behaved_access m t ->
    well_behaved_access m (TM_Load t).
  Proof.
    intros * ? ? ?. inversion_access. eauto.
  Qed.

  Local Lemma wba_asg : forall m l r,
    well_behaved_access m l ->
    well_behaved_access m r ->
    well_behaved_access m (TM_Asg l r).
  Proof.
    intros * ? ? ? ?. inversion_access; eauto.
  Qed.

  Local Lemma wba_seq : forall m t1 t2,
    well_behaved_access m t1 ->
    well_behaved_access m t2 ->
    well_behaved_access m (TM_Seq t1 t2).
  Proof.
    intros * ? ? ? ?. inversion_access; eauto.
  Qed.

  Local Lemma wba_added_value : forall m v,
    well_behaved_access (add m v) v ->
    well_behaved_access (add m v) (TM_Loc (length m)).
  Proof.
    intros * ? ? Hacc.
    remember (add m v) as m'.
    remember (TM_Loc (length m)) as t'.
    induction Hacc; inversion Heqt'; subst.
    - rewrite (get_add_eq TM_Nil) in *; eauto using access.
    - rewrite add_increments_length. lia.
  Qed.

  Local Lemma wba_stored_value : forall m t t' ad v,
    well_behaved_access m t ->
    t --[EF_Store ad v]--> t' ->
    well_behaved_access m v.
  Proof.
    intros. intros ? ?.
    remember (EF_Store ad v) as eff.
    induction_step; try inversion Heqeff; subst;
    destruct_wba; eauto using access. 
  Qed.

  Lemma mem_add: forall m t v,
    well_behaved_access m t ->
    well_behaved_access (add m v) t.
  Proof.
    intros * Hwba ? Hacc. remember (add m v) as m'.
    induction Hacc; subst; try destruct_wba; eauto.
    - eapply IHHacc. intros ad'' Hacc''.
      destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]; subst.
      + rewrite (get_add_lt TM_Nil) in *; eauto using access.
      + specialize (Hwba (length m) (access_loc m (length m))). lia.
      + rewrite (get_add_gt TM_Nil) in *; eauto. inversion_access.
    - rewrite add_increments_length. eauto using access, Nat.lt_lt_succ_r.
  Qed.

  Lemma mem_set: forall m t ad v,
    well_behaved_access m t ->
    well_behaved_access m v ->
    well_behaved_access (set m ad v) t.
  Proof.
    intros * ? ? ? Hacc.
    rewrite set_preserves_length.
    remember (set m ad v) as m'.
    induction Hacc; subst; try destruct_wba; eauto using access.
    eapply IHHacc. destruct (Nat.eq_dec ad ad'); subst.
    - rewrite (get_set_eq TM_Nil); eauto using access.
    - rewrite (get_set_neq TM_Nil) in *; eauto.
      intros ? ?. eauto using access.
  Qed.

  Local Lemma none_preservation : forall m t t',
    well_behaved_access m t ->
    t --[EF_None]--> t' ->
    well_behaved_access m t'.
  Proof.
    intros. remember (EF_None) as eff.
    induction_step; inversion Heqeff; subst;
    destruct_wba; eauto using wba_load, wba_asg, wba_seq. 
  Qed.

  Local Lemma alloc_preservation : forall m t t' v,
    well_behaved_access m t ->
    t --[EF_Alloc (length m) v]--> t' ->
    well_behaved_access (add m v) t'.
  Proof.
    intros. remember (EF_Alloc (length m) v) as eff.
    induction_step; inversion Heqeff; subst;
    destruct_wba;
    eauto using wba_load, wba_asg, wba_seq, mem_add, wba_added_value. 
  Qed.

  Local Lemma load_preservation : forall m t t' ad,
    well_behaved_access m t ->
    t --[EF_Load ad (get TM_Nil m ad)]--> t' ->
    well_behaved_access m t'.
  Proof.
    intros. remember (EF_Load ad (get TM_Nil m ad)) as eff.
    induction_step; inversion Heqeff; subst;
    destruct_wba; eauto using wba_load, wba_asg, wba_seq.
    intros ? ?. eauto using access.
  Qed.

  Local Lemma store_preservation : forall m t t' ad v,
    well_behaved_access m t ->
    t --[EF_Store ad v]--> t' ->
    well_behaved_access (set m ad v) t'.
  Proof.
    intros.
    assert (well_behaved_access m v); eauto using wba_stored_value.
    remember (EF_Store ad v) as eff.
    induction_step; inversion Heqeff; subst;
    destruct_wba; eauto using wba_load, wba_asg, wba_seq, mem_set.
    intros ? ?. inversion_access.
  Qed.

  Lemma preservation : forall m m' t t' eff,
    well_behaved_access m t ->
    m / t ==[eff]==> m' / t' ->
    well_behaved_access m' t'.
  Proof.
    intros * ? ?. inversion_mstep;
    eauto using none_preservation, 
      alloc_preservation,
      load_preservation,
      store_preservation.
  Qed.
End WBA.

(*****************************************************************************)
(* Mem ***********************************************************************)
(*****************************************************************************)

Module Mem.
  Module Add.
    Lemma preserves_access : forall m t ad v,
      access m t ad ->
      access (add m v) t ad.
    Proof.
      intros * Hacc. induction Hacc; eauto using access.
      eapply access_mem.
      destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]. 
      - rewrite (get_add_lt TM_Nil); trivial.
      - subst. rewrite (get_default TM_Nil) in IHHacc; try lia.
        inversion_access.
      - rewrite (get_default TM_Nil) in IHHacc; try lia.
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
          try solve [rewrite (get_set_neq TM_Nil) in IH; eauto using access];
          destruct (Nat.eq_dec ad2 ad3); subst; eauto using access
      end.
      exfalso. rewrite (get_set_eq TM_Nil) in IHHacc; eauto.
      eapply not_le. intros F. rewrite (get_default TM_Nil) in Hacc.
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
        rewrite (get_set_invalid TM_Nil) in H; trivial. inversion H.
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
        rewrite (get_set_eq TM_Nil) in F;
        rewrite (get_set_eq TM_Nil) in IHF; eauto.
      - eapply not_eq_sym in Hneq.
        rewrite (get_set_neq TM_Nil) in *; eauto using access.
    Qed.
  End Set_.
End Mem.

(*****************************************************************************)
(* Step **********************************************************************)
(*****************************************************************************)

Module Step.
  Module Alloc.
    Lemma address_access2 : forall m t t' ad v,
      t --[EF_Alloc ad v]--> t' ->
      access m t' ad.
    Proof.
      intros. remember (EF_Alloc ad v) as eff.
      induction_step; inversion Heqeff; subst; eauto using access.
    Qed. 
  End Alloc.

  Module Store.
    Lemma value_access : forall m t t' ad ad' v,
      access m v ad ->
      t --[EF_Store ad' v]--> t' ->
      access m t ad.
    Proof.
      intros * ? ?. remember (EF_Store ad' v) as eff.
      induction_step; inversion Heqeff; subst; eauto using access.
    Qed.

    Lemma value_not_access : forall m t t' ad ad' v,
      ~ access m t ad ->
      t --[EF_Store ad' v]--> t' ->
      ~ access m v ad.
    Proof.
      intros. remember (EF_Store ad' v) as eff.
      induction_step; inversion Heqeff; subst; eauto using access.
    Qed.
  End Store.
End Step.

(*****************************************************************************)
(* MStep *********************************************************************)
(*****************************************************************************)

Module MStep.
  Module None.
    Lemma inherits_access : forall m m' t t' ad,
      access m' t' ad ->
      m / t ==[EF_None]==> m' / t' ->
      access m t ad.
    Proof.
      intros * ? ?. inversion_mstep. remember EF_None as eff.
      induction_step; inversion Heqeff; subst;
      try inversion_access; eauto using access.
    Qed.

    Lemma preserves_not_access : forall m m' t t' ad,
      ~ access m t ad ->
      m / t ==[EF_None]==> m' / t' ->
      ~ access m' t' ad.
    Proof.
      intros * ? ?. inversion_mstep. remember EF_None as eff.
      induction_step; inversion Heqeff; subst; inversion_not_access;
      eauto using not_access_load, not_access_asg, not_access_seq.
    Qed.
  End None.

  Module Alloc.
    Local Lemma address_access: forall m m' t t' ad v,
      m / t ==[EF_Alloc ad v]==> m' / t' ->
      access m' t' ad.
    Proof.
      intros * ?. inversion_mstep. eauto using Step.Alloc.address_access2.
    Qed.

    Lemma grants_access : forall m m' t t' ad v,
      well_behaved_access m t ->
      m / t ==[EF_Alloc ad v]==> m' / t' ->
      ~ access m t ad /\ access m' t' ad.
    Proof.
      intros * Hwba ?. split; eauto using address_access.
      inversion_mstep. intros F. eapply Hwba in F. lia.
    Qed.

    Lemma inherits_access : forall m m' t t' ad ad' v,
      well_behaved_access m t ->
      ad <> ad' ->
      access m' t' ad ->
      m / t ==[EF_Alloc ad' v]==> m' / t' ->
      access m t ad.
    Proof.
      intros * Hwba ? ? Hmstep. inversion_mstep.
      remember (EF_Alloc (length m) v) as eff.
      induction_step; inversion Heqeff; subst;
      WBA.destruct_wba; try inversion_access; eauto using access; try lia.
      - rewrite (get_add_eq TM_Nil) in *.
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
      - eapply access_seq2; eapply inaccessible_address_add_1; eauto. intros F.
        match goal with Hwba : well_behaved_access m ?t |- _ =>
          specialize (Hwba (length m) F); lia
        end.
    Qed.

    Lemma preserves_access : forall m m' t t' ad ad' v,
      access m t ad ->
      m / t ==[EF_Alloc ad' v]==> m' / t' ->
      access m' t' ad.
    Proof.
      intros. inversion_mstep. remember (EF_Alloc (length m) v) as eff.
      induction_step; inversion Heqeff; subst;
      inversion_access; eauto using access, Mem.Add.preserves_access.
      eapply access_mem. rewrite (get_add_eq TM_Nil).
      eauto using Mem.Add.preserves_access.
    Qed.

    Lemma preserves_not_access : forall m m' t t' ad ad' v,
      well_behaved_access m t ->
      ad <> ad' ->
      ~ access m t ad ->
      m / t ==[EF_Alloc ad' v]==> m' / t' ->
      ~ access m' t' ad.
    Proof.
      intros * Hwba ? ? ?. inversion_mstep.
      remember (EF_Alloc (length m) v) as eff.
      induction_step; inversion Heqeff; subst; WBA.destruct_wba;
      inversion_not_access; eauto using access, not_access_load. 
      - intros ?. inversion_access; eauto.
        rewrite (get_add_eq TM_Nil) in *.
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
      - eapply not_access_seq; eauto; eapply inaccessible_address_add_2; eauto.
        intros F. match goal with Hwba : well_behaved_access m ?t |- _ =>
          specialize (Hwba (length m) F); lia
        end.
    Qed.
  End Alloc.

  Module Load.
    Lemma inherits_access : forall m m' t t' ad ad' v,
      access m' t' ad ->
      m / t ==[EF_Load ad' v]==> m' / t' ->
      access m t ad.
    Proof.
      intros * ? ?. inversion_mstep.
      remember (EF_Load ad' (getTM m' ad')) as eff. 
      induction_step; inversion Heqeff; subst;
      try inversion_access; eauto using access.
    Qed.

    Lemma preserves_access : forall m m' t t' ad ad' v,
      ad <> ad' ->
      access m t ad ->
      m / t ==[EF_Load ad' v]==> m' / t' ->
      access m' t' ad.
    Proof.
      intros * Hneq Hacc Hmstep. inversion_mstep.
      remember (EF_Load ad' (getTM m' ad')) as eff.
      induction_step; inversion Heqeff; subst;
      inversion_access; eauto using access.
      inversion_access; subst; trivial. exfalso. eauto.
    Qed.

    Lemma preserves_not_access : forall m m' t t' ad ad' v,
      ~ access m t ad ->
      m / t ==[EF_Load ad' v]==> m' / t' ->
      ~ access m' t' ad.
    Proof.
      intros * ? ?. inversion_mstep.
      remember (EF_Load ad' (getTM m' ad')) as eff.
      induction_step; inversion Heqeff; subst;
      eauto using access; inversion_not_access;
      eauto using not_access_load, not_access_asg, not_access_seq.
    Qed.

    Lemma address_access: forall m m' t t' ad v,
      m / t ==[EF_Load ad v]==> m' / t' ->
      access m t ad.
    Proof.
      intros. inversion_mstep. remember (EF_Load ad (getTM m' ad)) as eff.
      induction_step; inversion Heqeff; subst; eauto using access.
    Qed.
  End Load.

  Module Store.
    Lemma address_access: forall m m' t t' ad v,
      m / t ==[EF_Store ad v]==> m' / t' ->
      access m t ad.
    Proof.
      intros * ?. inversion_mstep. remember (EF_Store ad v) as eff.
      induction_step; inversion Heqeff; subst; eauto using access.
    Qed.

    Lemma inherits_access : forall m m' t t' ad ad' v,
      access m' t' ad ->
      m / t ==[EF_Store ad' v]==> m' / t' ->
      access m t ad.
    Proof.
      intros. inversion_mstep. remember (EF_Store ad' v) as eff.
      induction_step; inversion Heqeff; subst;
      try inversion_access; eauto using access;
      destruct (access_dec m v ad);
      eauto using access, Step.Store.value_access, Mem.Set_.preserves_access.
    Qed.

    Lemma preserves_not_access : forall m m' t t' ad ad' v,
      ~ access m t ad ->
      m / t ==[EF_Store ad' v]==> m' / t' ->
      ~ access m' t' ad.
    Proof.
      intros * Hnacc ?. inversion_mstep.
      remember (EF_Store ad' v) as eff.
      induction_step; inversion Heqeff; subst;
      inversion_not_access;
      eauto using not_access_load, not_access_asg, not_access_seq,
                  Mem.Set_.preserves_not_access, Step.Store.value_not_access.
    Qed.
  End Store.
End MStep.

