From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Logic.ClassicalFacts.

From Elo Require Import Array.
From Elo Require Import Core0.

Reserved Notation "m / t '==[' tc ']==>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_trans : forall t ad ad',
    access m t ad ->
    get_tm m ad = TM_Loc ad' ->
    access m t ad'

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
  .

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

Lemma monotonic_nondecreasing_memory_length: forall m m' eff t t',
  m / t ==[eff]==>* m' / t' ->
  length m <= length m'.
Proof.
  assert (forall m m' eff t t',
    m / t ==[eff]==> m' / t' ->
    length m <= length m').
  {
    intros * Hmstep. inversion Hmstep; subst;
    try (erewrite <- Array.set_preserves_length);
    eauto using Nat.lt_le_incl, Array.length_lt_add.
  }
  intros * Hmultistep. induction Hmultistep; eauto using Nat.le_trans.
Qed.

Lemma alloc_increments_memory_length : forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  length m' = S (length m).
Proof.
  intros * Hmstep. inversion Hmstep; subst. eauto using length_add.
Qed.

Lemma destruct_multistep : forall tc eff m0 mF t0 tF,
  m0 / t0  ==[tc ++ eff :: nil]==>* mF / tF ->
  (exists m t, m0 / t0 ==[eff]==> m / t /\ m / t ==[tc]==>* mF / tF).
Proof.
  intros ?. induction tc as [| eff tc IH];
  intros * Hmultistep; inversion Hmultistep; subst.
  - eexists. eexists. inversion H3; subst. split; eauto using multistep.
  - specialize (IH _ _ _ _ _ H3) as [m [t [Hmstep' Hmultistep']]].
    eexists. eexists. split; eauto using multistep.
Qed.

Lemma not_Sn_le_n : forall n,
  ~ (S n <= n).
Proof.
  unfold not. intros * F. induction n.
  - inversion F.
  - eauto using le_S_n.
Qed.

Theorem duplicate_alloc : forall m m' t t' tc ad v v',
  m / t ==[EF_Alloc ad v :: tc ++ EF_Alloc ad v' :: nil]==>* m' / t' ->
  False.
Proof.
  intros * Hmultistep. inversion Hmultistep; subst; clear Hmultistep;
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
    match goal with
    F : length ?x = length (add ?x _) |- _ =>
      rewrite length_add in F; eapply n_Sn in F
    end.
    assumption.
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
    | H1 : length _ = length ?x, H2 : length _ <= length ?x |- _ =>
        rewrite <- H1 in H2; rewrite length_add in H2
    end.
    eapply not_Sn_le_n in Hmultistep'.
    assumption.
Qed.

(*

Lemma :
  ~ access m t ad ->
  t --[eff]--> t' ->
  access m' t' ad ->
  eff = Alloc ad v.


  e depois para ==[]==>

*)



















Theorem duplicate_alloc : forall tc1 tc2 m m' t t' ad v,
  In (EF_Alloc ad v) tc2 ->
  m / t ==[tc2 ++ tc1]==>* m' / t' ->
  ~ (In (EF_Alloc ad v) tc1).
Proof.
  intros * Hin Hmulti.
  inversion Hmulti; subst.
  - admit.
  - destruct tc2 as [| eff2 tc2]; try contradiction.
    inversion H. subst. clear H.
    eapply not_in_cons. split.
    + unfold not. intros. subst. admit.
    + erewrite app_cons in Hmulti. eauto using in_or_app.



  intros ?.
  induction tc1 as [| eff1 tc1 IH]; intros * Hin Hmulti.
  - unfold not, In. trivial.
  - inversion Hmulti; subst.
    + eapply destruct_multistep in H as [? ?]. subst. contradiction.
    + destruct tc2 as [| eff2 tc2]; try contradiction.
      inversion H. subst. clear H.
      eapply not_in_cons. split.
      * unfold not. intros. subst. admit.
      * erewrite app_cons in Hmulti. eauto using in_or_app.
Qed.



inversion Hmulti; subst.
  - unfold not, In. trivial.
  - induction tc as [| eff tc IH].
    + inversion H3.
    + eapply not_in_cons. split.
      * unfold not. intros. subst. admit.
      * eapply IH; clear IH.
        **

Qed.

Lemma alloc_grants_access_single_step : forall m t t' ad v,
  t --[EF_Alloc ad v]--> t' ->
  access m t' ad.
Proof.
  intros ? ?. induction t; intros * Hstep;
  inversion Hstep; subst; eauto using access.
Qed.

Lemma alloc_grants_access_memory_step : forall m m' t t' ad v,
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros * Hmstep. destruct t';
  inversion Hmstep; subst;
  eauto using alloc_grants_access_single_step.
Qed.

Lemma alloc_grants_access_multistep : forall m m' tc t t' ad v,
  m / t ==[EF_Alloc ad v :: tc]==>* m' / t' ->
  access m' t' ad.
Proof.
  intros * Hmulti. destruct t';
  inversion Hmulti; subst;
  eauto using alloc_grants_access_memory_step.
Qed.


(*

Inductive something :
  | Something_Load
    tid = alguma thread
    m / ths ==> m' / ths' # Load tid 23
    em todas as outras threads que não são tid,
    não pode ter Loc 23

*)
