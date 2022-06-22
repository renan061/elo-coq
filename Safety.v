From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core0.
From Elo Require Import Access.

Reserved Notation "m / t '==[' tc ']==>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Reserved Notation "m / t '~~[' tc ']~~>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Definition trace := list effect.

(* reflexive transitive closure *)
Inductive multistep : mem -> tm -> trace -> mem -> tm -> Prop :=
  | multistep_refl: forall m t,
    m / t ==[nil]==>* m / t

  | multistep_trans : forall m m' m'' t t' t'' tc eff,
    m  / t  ==[tc]==>* m'  / t'  ->
    m' / t' ==[eff]==> m'' / t'' ->
    m  / t  ==[eff :: tc]==>* m'' / t''

  where "m / t '==[' tc ']==>*' m' / t'" := (multistep m t tc m' t').

(* PART 1 *)

Lemma monotonic_nondecreasing_memory_length: forall m m' eff t t',
  m / t ==[eff]==>* m' / t' ->
  length m <= length m'.
Proof.
  assert (forall m m' eff t t',
    m / t ==[eff]==> m' / t' ->
    length m <= length m').
  {
    intros * Hmstep. inversion Hmstep; subst; try lia.
    - rewrite add_increments_length . lia.
    - eauto using Nat.eq_le_incl, set_preserves_length.
  }
  intros * Hmultistep. induction Hmultistep; eauto using Nat.le_trans.
Qed.

Lemma alloc_increments_memory_length : forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  length m' = S (length m).
Proof.
  intros * Hmstep. inversion Hmstep; subst.
  eauto using add_increments_length.
Qed.

Lemma destruct_multistep : forall tc eff m0 mF t0 tF,
  m0 / t0  ==[tc ++ eff :: nil]==>* mF / tF ->
  (exists m t, m0 / t0 ==[eff]==> m / t /\ m / t ==[tc]==>* mF / tF).
Proof.
  intros ?. induction tc as [| eff tc IH];
  intros * Hmultistep; inversion Hmultistep; subst.
  - eexists. eexists. inversion H3; subst. split; eauto using multistep.
  - specialize (IH _ _ _ _ _ H3) as [? [? [? ?]]].
    eexists. eexists. split; eauto using multistep.
Qed.

Theorem duplicate_alloc : forall m m' t t' tc ad v v',
  ~ (m / t ==[EF_Alloc ad v :: tc ++ EF_Alloc ad v' :: nil]==>* m' / t').
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
      eapply destruct_multistep in H as [? [? [? Hmultistep']]]
    end.
    eapply monotonic_nondecreasing_memory_length in Hmultistep'.
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

(* PART 2 *)

Lemma access_if_alloc : forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  access m' t' ad.
Proof.
  assert (forall m t t' ad v, t --[EF_Alloc ad v]--> t' -> access m t' ad). {
    intros ? ?. induction t; intros * Hstep;
    inversion Hstep; subst; eauto using access.
  }
  intros * Hmstep. destruct t'; inversion Hmstep; subst; eauto.
Qed.

Definition well_behaved_access m t :=
  forall ad, access m t ad -> ad < length m.

Lemma alloc_grants_access: forall m m' t t' ad v,
  well_behaved_access m t ->
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  ~ access m t ad /\ access m' t' ad.
Proof.
  intros * Hwba Hmstep. split; eauto using access_if_alloc.
  intros F. eapply Hwba in F.
  inversion Hmstep; subst.
  eapply Nat.lt_irrefl; eauto.
Qed.

(* PART 3 *)

Module wba.

Lemma new : forall m t,
  well_behaved_access m (TM_New t) ->
  well_behaved_access m t.
Proof.
  intros * ? ?; eauto using access.
Qed.

Lemma load : forall m t,
  well_behaved_access m (TM_Load t) ->
  well_behaved_access m t.
Proof.
  intros * ? ?; eauto using access.
Qed.

Local Lemma wba_load' : forall m t,
  well_behaved_access m t ->
  well_behaved_access m (TM_Load t).
Proof.
  intros * ? ? ?. inversion_access. eauto.
Qed.

Lemma asg1 : forall m l r,
  well_behaved_access m (TM_Asg l r) ->
  well_behaved_access m l.
Proof.
  intros * ? ?. eauto using access.
Qed.

Lemma asg2 : forall m l r,
  well_behaved_access m (TM_Asg l r) ->
  well_behaved_access m r.
Proof.
  intros * ? ?. eauto using access.
Qed.

Local Lemma wba_asg' : forall m l r,
  well_behaved_access m l ->
  well_behaved_access m r ->
  well_behaved_access m (TM_Asg l r).
Proof.
  intros * ? ? ? Hacc. inversion_access; eauto.
Qed.

Lemma seq1 : forall m t1 t2,
  well_behaved_access m (TM_Seq t1 t2) ->
  well_behaved_access m t1.
Proof.
  intros * ? ?. eauto using access.
Qed.

Lemma seq2 : forall m t1 t2,
  well_behaved_access m (TM_Seq t1 t2) ->
  well_behaved_access m t2.
Proof.
  intros * ? ?. eauto using access.
Qed.

Local Lemma wba_seq' : forall m t1 t2,
  well_behaved_access m t1 ->
  well_behaved_access m t2 ->
  well_behaved_access m (TM_Seq t1 t2).
Proof.
  intros * ? ? ? Hacc. inversion_access; eauto.
Qed.

Local Lemma wba_added_value : forall m v,
  well_behaved_access (add m v) v ->
  well_behaved_access (add m v) (TM_Loc (length m)).
Proof.
  intros * Hwba ad Hacc.
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
  intros * ? Hstep ? ?.
  remember (EF_Store ad v) as eff.
  induction Hstep; try inversion Heqeff; subst;
  eauto using access, new, load, asg1, asg2, seq1, seq2.
Qed.

Lemma mem_add: forall m t v,
  well_behaved_access m t ->
  well_behaved_access (add m v) t.
Proof.
  intros * Hwba ad Hacc.
  remember (add m v) as m'.
  induction Hacc; subst;
  eauto using new, load, asg1, asg2, seq1, seq2.
  - match goal with IH : _ -> ?x |- ?x => eapply IH end.
    intros ad'' Hacc''.
    destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]; subst.
    + rewrite (get_add_lt TM_Nil) in *; eauto using access.
    + specialize (Hwba (length m) (access_loc m (length m))). lia.
    + rewrite (get_add_gt TM_Nil) in *; eauto. inversion_access.
  - rewrite add_increments_length. eauto using access, Nat.lt_lt_succ_r.
Qed.

Local Lemma wba_mem_set: forall m t ad v,
  well_behaved_access m t ->
  well_behaved_access m v ->
  well_behaved_access (set m ad v) t.
Proof.
  intros * HwbaT HwbaV ad' Hacc'.
  rewrite set_preserves_length.
  remember (set m ad v) as m'.
  induction Hacc'; subst;
  eauto using access, new, load, asg1, asg2, seq1, seq2.
  match goal with IH : _ -> ?x |- ?x => eapply IH; clear IH end.
  destruct (Nat.eqb ad ad') eqn:E.
  - eapply Nat.eqb_eq in E; subst.
    rewrite (get_set_eq TM_Nil); eauto using access.
  - eapply Nat.eqb_neq in E.
    rewrite (get_set_neq TM_Nil) in *; eauto.
    intros ? ?. eauto using access.
Qed.

Local Lemma none_preservation : forall m t t',
  well_behaved_access m t ->
  t --[EF_None]--> t' ->
  well_behaved_access m t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_None) as eff.
  induction Hstep; inversion Heqeff; subst;
  eauto using new, load, wba_load';
  try (eapply wba_asg' || eapply wba_seq');
  eauto using asg1, asg2, seq1, seq2.
Qed.

Local Lemma alloc_preservation : forall m t t' v,
  well_behaved_access m t ->
  t --[EF_Alloc (length m) v]--> t' ->
  well_behaved_access (add m v) t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_Alloc (length m) v) as eff.
  induction Hstep; inversion Heqeff; subst;
  eauto using new, load, wba_load', mem_add, wba_added_value;
  try (eapply wba_asg' || eapply wba_seq');
  eauto using asg1, asg2, seq1, seq2, mem_add.
Qed.

Local Lemma load_preservation : forall m t t' ad,
  well_behaved_access m t ->
  t --[EF_Load ad (get TM_Nil m ad)]--> t' ->
  well_behaved_access m t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_Load ad (get TM_Nil m ad)) as eff.
  induction Hstep; subst; try (inversion Heqeff; subst);
  eauto using new, load, wba_load', asg1, asg2, wba_asg', seq1, seq2, wba_seq';
  eapply load in Hwba; intros ? ?; eauto using access.
Qed.

Local Lemma store_preservation : forall m t t' ad v,
  well_behaved_access m t ->
  t --[EF_Store ad v]--> t' ->
  well_behaved_access (set m ad v) t'.
Proof.
  intros * Hwba Hstep.
  assert (well_behaved_access m v); eauto using wba_stored_value.
  remember (EF_Store ad v) as eff.
  induction Hstep; subst; try (inversion Heqeff; subst);
  eauto using new, load, wba_load';
  try (eapply wba_asg' || eapply wba_seq');
  eauto using asg1, asg2, seq1, seq2, wba_mem_set.
  intros ? ?. inversion_access.
Qed.

Lemma mstep_preservation : forall m m' t t' eff,
  well_behaved_access m t ->
  m / t ==[eff]==> m' / t' ->
  well_behaved_access m' t'.
Proof.
  intros * Hwba Hmstep. inversion Hmstep; subst;
  eauto using none_preservation, 
    alloc_preservation,
    load_preservation,
    store_preservation.
Qed.

End wba.

(* PART 4 *)

Local Lemma access_set : forall m t ad ad' v,
  ~ access m t ad ->
  ~ access m v ad ->
  ~ access (set m ad' v) t ad.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m).
  { intros. split; destruct n; eauto. }

  assert (forall m ad ad' v,
    access (set m ad' v) (get TM_Nil (set m ad' v) ad') ad ->
    ad' < length m). {
    intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
    rewrite get_set_invalid in H; trivial. inversion H.
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
    rewrite (get_set_eq TM_Nil) in F; trivial.
    rewrite (get_set_eq TM_Nil) in IHF; eauto.
  - eapply not_eq_sym in Hneq.
    rewrite (get_set_neq TM_Nil) in *; eauto using access.
Qed.

Local Lemma access_add : forall m t ad v,
  ~ access m t ad ->
  ~ access m v ad ->
  ~ access (add m v) t ad.
Proof.
  intros * HnaccT HnaccV Hacc.
  induction Hacc; eauto using access.
  eapply IHHacc; clear IHHacc; trivial.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst.
  - rewrite (get_add_lt TM_Nil); eauto using access.
  - rewrite (get_add_eq TM_Nil). trivial.
  - rewrite (get_add_gt TM_Nil); trivial. intros ?. inversion_access.
Qed.

Local Lemma not_access_stored_value : forall m t t' ad ad' v, 
  ~ access m t ad ->
  t --[ EF_Store ad' v ]--> t' ->
  ~ access m v ad.
Proof.
  intros * Hnacc Hstep.
  remember (EF_Store ad' v) as eff.
  induction Hstep; inversion Heqeff; subst; eauto using access.
Qed.

Local Lemma not_access_allocated_value : forall m t t' ad ad' v, 
  ~ access m t ad ->
  t --[ EF_Alloc ad' v ]--> t' ->
  ~ access m v ad.
Proof.
  intros * Hnacc Hstep.
  remember (EF_Alloc ad' v) as eff.
  induction Hstep; inversion Heqeff; subst; eauto using access.
Qed.

Lemma none_does_not_grant_access : forall m m' t t' ad,
  ~ access m t ad ->
  m / t ==[EF_None]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc Hmstep. inversion Hmstep; subst; clear Hmstep.
  remember EF_None as eff.
  match goal with Hstep : _ --[_]--> _ |- _ => induction Hstep end;
  inversion Heqeff; subst; eauto using access.
  - inversion_not_access. eapply access_load_inverse; eauto using load_access_inverse.
  - eapply asg_access_inverse in Hnacc as [? ?].
    eauto using access_asg_inverse.
  - eapply asg_access_inverse in Hnacc as [? ?].
    eauto using access_asg_inverse.
  - eapply seq_access_inverse in Hnacc as [? ?].
    eauto using access_seq_inverse.
Qed.

Lemma load_does_not_grant_access : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  m / t ==[EF_Load ad' v]==> m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc Hmstep. inversion Hmstep; subst; clear Hmstep.
  remember (EF_Load ad' (get TM_Nil m' ad')) as eff.
  match goal with Hstep : _ --[_]--> _ |- _ => induction Hstep end;
  inversion Heqeff; subst; eauto using access.
  - eapply access_load_inverse; eauto using load_access_inverse.
  - eapply asg_access_inverse in Hnacc as [? ?].
    eauto using access_asg_inverse.
  - eapply asg_access_inverse in Hnacc as [? ?].
    eauto using access_asg_inverse.
  - eapply seq_access_inverse in Hnacc as [? ?].
    eauto using access_seq_inverse.
Qed.

Lemma access_granted_by_alloc_is_memory_length : forall m t t' ad v,
  ~ access m t ad ->
  t --[ EF_Alloc (length m) v ]--> t' ->
  access (add m v) t' ad ->
  ad = length m.
Proof.
  intros * Hnacc Hstep Hacc.
  remember (EF_Alloc (length m) v) as eff.
  induction Hstep; inversion Heqeff; subst; try (clear Heqeff);
  eauto using access, load_access, load_access_inverse.
  - eapply new_access_inverse in Hnacc.
    inversion Hacc; clear Hacc; subst; trivial.
    match goal with F : access _ _ _ |- _ => contradict F end.
    rewrite get_add_eq. eapply access_add; eauto.
  - eapply asg_access_inverse in Hnacc as [HnaccL ?].
    match goal with IH : _ -> _ -> _ -> ?x |- ?x => eapply IH; eauto end.
    eapply asg_access in Hacc as [? | ?]; eauto.
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

Lemma access_dec : forall m t ad,
  {access m t ad} + {~ access m t ad}.
Proof.
  intros. induction t.
  - right. intros F. inversion F.
  - right. intros F. inversion F.
  - destruct (Nat.eq_dec n ad); subst; try solve [left; eauto using access].
    (* decidable (access m (get TM_Nil m ad') ad) *)
    admit.
  - destruct IHt.
    + left. eauto using access.
    + right. eauto using access_new_inverse.
  - destruct IHt.
    + left. eauto using access.
    + right. eauto using access_load_inverse.
  - destruct IHt1, IHt2; try solve [left; eauto using access].
    right. eauto using access_asg_inverse.
  - destruct IHt1, IHt2; try solve [left; eauto using access].
    right. eauto using access_seq_inverse.
Abort.

Lemma provar_para_tirar_o_axioma : forall m m' t t' eff ad v,
  access m' t' ad ->
  eff <> EF_Alloc ad v ->
  m / t ==[eff]==> m' / t' ->
  access m t ad.
Proof.
  intros * Hacc Hneq Hmstep.
Abort.

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

(*

(* PART 6 *)

Definition ctrace := list (nat * effect).

Inductive cmultistep : mem -> threads -> ctrace -> mem -> threads -> Prop :=
  | cmultistep_refl: forall m ths,
    m / ths ~~[nil]~~>* m / ths

  | cmultistep_trans : forall m m' m'' tid ths ths' ths'' tc eff,
    m  / ths  ~~[tc]~~>* m'  / ths'  ->
    m' / ths' ~~[tid, eff]~~> m'' / ths'' ->
    m  / ths  ~~[(tid, eff) :: tc]~~>* m'' / ths''

  where "m / t '~~[' tc ']~~>*' m' / t'" := (cmultistep m t tc m' t').

Ltac destruct_cstep :=
  match goal with
    | [ H : _ / _ ~~[_, _]~~> _ / _ |- _ ] =>
      inversion H; subst; clear H
  end.

Theorem concurrent_duplicate_alloc :
  forall m m' ths ths' tid tid' tc1 tc2 ad v v',
  ~ (m / ths ~~[tc1 ++ (tid , EF_Alloc ad v ) ::
                tc2 ++ (tid', EF_Alloc ad v') :: nil]~~>* m' / ths').
Proof.
  intros * F. inversion F; subst; clear F.
Abort.

Theorem threads_dont_share_memory :
  forall m m' ths ths' t1 t2 tid tid1 tid2 eff ad,
  m' / ths' ~~[tid, eff]~~> m / ths ->
  t1 = get TM_Nil ths tid1 ->
  access m t1 ad ->
  t2 = get TM_Nil ths tid2 ->
  tid1 <> tid2 ->
  ~ access m t2 ad.
Proof.
  intros * Hcstep Ht1 Hacc1 Hte Hneq.
Abort.

(*

Teorema Final.

m / ths ~~[tc]~~>* m' / ths'

*)

*)












(* BAGUNÇA)

Lemma inverse : forall m ad ad',
  ad <> ad' ->
  access m (TM_Loc ad') ad ->
  access m (get TM_Nil m ad') ad.
Proof.
  intros * Hneq Hacc.
  remember (TM_Loc ad') as t.
  induction Hacc; inversion Heqt; subst; trivial.
  lia.
Qed.

Inductive something :
  | Something_Load
    tid = alguma thread
    m / ths ==> m' / ths' # Load tid 23
    em todas as outras threads que não são tid,
    não pode ter Loc 23

*)
