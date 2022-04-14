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
  ~ (m / t ==[EF_Alloc ad v :: tc ++ EF_Alloc ad v' :: nil]==>* m' / t').
Proof.
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
  t ==[eff]==> t' ->
  access m' t' ad ->
  eff = Alloc ad v.


  e depois para ==[]==>

*)

Lemma load_if_access: forall m m' t t' ad v,
  m / t ==[EF_Load ad v]==> m' / t' -> 
  access m t ad.
Proof.
  assert (forall m t t' ad,
    t --[ EF_Load ad (get_tm m ad) ]--> t' ->
    access m t ad). {
      intros * Hstep.
      remember (EF_Load ad (get_tm m ad)) as eff.
      induction Hstep; eauto using access;
      inversion Heqeff; subst. eauto using access.
  }
  intros * Hmstep. inversion Hmstep; subst. eauto.
Qed.

Lemma store_if_access: forall m m' t t' ad v,
  m / t ==[EF_Store ad v]==> m' / t' -> 
  access m t ad.
Proof.
  assert (forall m t t' ad v,
    t --[ EF_Store ad v ]--> t' ->
    access m t ad). {
      intros * Hstep.
      remember (EF_Store ad v) as eff.
      induction Hstep; eauto using access;
      inversion Heqeff; subst. eauto using access.
  }
  intros * Hmstep. inversion Hmstep; subst. eauto.
Qed.

Lemma load_access: forall m t ad,
  access m (TM_Load t) ad -> access m t ad.
Proof.
  intros * Hacc. remember (TM_Load t) as t'.
  induction Hacc; inversion Heqt'; subst; eauto using access.
Qed.

Lemma asg_access: forall m l r ad,
  access m (TM_Asg l r) ad ->
  access m l ad \/ access m r ad.
Proof.
  intros * Hacc. remember (TM_Asg l r) as t.
  induction Hacc; inversion Heqt; subst; eauto.
  destruct (IHHacc eq_refl) as [? | ?]; eauto using access.
Qed.

Lemma auxiliar : forall m t t' ad v,
  t --[ EF_Alloc (length m) v ]--> t' ->
  access (add m v) t' ad ->
  length m <> ad ->
  access m t ad.
Proof.
  intros * Hstep Hacc Hneq. remember (EF_Alloc (length m) v) as eff.
  induction Hstep; subst; eauto using access, load_access;
  try solve [inversion Heqeff].
  - inversion Heqeff; subst. eauto using access. shelve.
  - eapply access_asg1. eapply (IHHstep eq_refl).
    destruct (asg_access _ _ _ _ Hacc) as [L | R]; eauto.
Admitted.

Lemma algumacoisa : forall m m' t t' ad ad' v,
  m / t ==[EF_Alloc ad v]==> m' / t' -> 
  access m' t' ad' ->
  ad <> ad' ->
  access m t ad'.
Proof.
  intros * Hmstep Hacc Hneq. inversion Hmstep; subst.
Admitted.

Lemma coisaprincipal: forall m m' t t' eff ad, 
  ~ (access m t ad) ->
  m / t ==[eff]==> m' / t' ->
  access m' t' ad ->
  exists v, eff = EF_Alloc ad v.
Proof.
  intros * Hnacc Hmstep Hacc. inversion Hmstep; subst.
  - exists v. shelve.
  - exfalso. eapply load_if_access in Hmstep. shelve.
  - exfalso. eapply store_if_access in Hmstep. shelve.
Admitted.

Definition well_behaved_locations m t ad :=
  access m t ad -> ad < length m.

Lemma alloc_grants_access: forall m m' t t' ad v,
  well_behaved_locations m t ad ->
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  ~ access m t ad /\ access m' t' ad.
Proof.
  intros * Hwbl Hmstep. split.
  - intros F. specialize (Hwbl F).
    inversion Hmstep; subst.
    eapply Nat.lt_irrefl; eauto.
  - inversion Hmstep; subst.
    remember (EF_Alloc (length m) v) as eff.
    clear Hwbl. clear Hmstep.
    match goal with
    | Hstep : _ --[_]--> _ |- _ =>    
      induction Hstep; inversion Heqeff; subst; eauto using access
    end.
Qed.

Lemma auxalloc : forall m m' t t' eff ad, 
  well_behaved_locations m t ad ->
  m / t ==[ eff ]==> m' / t' ->
  well_behaved_locations m' t' ad.
Proof.
  intros * Hwbl Hmstep. inversion Hmstep; subst.
  - destruct (lt_eq_lt_dec ad (length m)) as [[E | E] | E].
    + eapply Nat.eqb_eq in E; subst.
      intros ?. eauto using length_lt_add.
    + eapply Nat.eqb_neq in E.
      unfold well_behaved_locations in Hwbl.
      intros Hacc. specialize (Hwbl Hacc).
Qed.

Lemma something: forall m' t t' ad' tc,
  (forall ad, ~ access nil t ad) ->
  nil / t ==[tc]==>* m' / t' ->
  well_behaved_locations m' t' ad'.
Proof.
  intros * Hnacc Hmultistep. induction Hmultistep.
  - intros F. exfalso. eapply Hnacc. eauto. 
  - specialize (IHHmultistep Hnacc).
    inversion H; subst.
    + intros Hacc.
      assert (w)
Qed.

















Lemma access_cannot_be_regained : forall m m' t t' ad tc,
  ~ access m t ad ->
  ad < length m ->
  m / t ==[tc]==>* m' / t' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc Hlen Hmultistep.
  induction Hmultistep; trivial.
  specialize (IHHmultistep Hnacc Hlen).
  inversion H; subst.
  - shelve.
  - shelve. 
  - shelve.
Admitted.

Lemma aux1 : forall m t ad,
  ~ (access m (TM_New t) ad) ->
  ~ (access m t ad).
Proof.
  intros * ?. unfold not. intros. eauto using access.
Qed.

Lemma aux2 : forall m t ad,
  ~ (access m (TM_Load t) ad) ->
  ~ (access m t ad).
Proof.
  intros * ?. unfold not. intros. eauto using access.
Qed.

Lemma access_incremented : forall m t t' ad v,
  ~ access m t ad ->
  t --[ EF_Alloc (length m) v ]--> t' ->
  access (add m v) t' ad ->
  ad = length m.
Proof.
  intros * Hnacc Hstep Hacc. inversion Hstep; subst.
  - shelve.
  - inversion Hacc; subst; trivial.
Admitted.

Lemma lemma : forall m m' t t' eff ad, 
  ~ (access m t ad) ->
  m / t ==[eff]==> m' / t' ->
  access m' t' ad ->
  exists v, eff = EF_Alloc ad v.
Proof.
  intros * Hnacc Hmstep Hacc. inversion Hmstep; subst.
  - exists v. . 
  - shelve.
  - shelve.
(*
  TEM QUE FALAR TBM SOBREA MEMÓRIA!
  A MEMÓRIA TEM QUE SER TAL QUE ad >= length m, OU ALGO DO TIPO.
*)
Admitted.

Lemma lemma1 : forall m t t' ad ad' v, 
  ~ access m t ad ->
  t --[ EF_Alloc ad' v ]--> t' ->
  access m t' ad ->
  ad = ad'.
Proof.
  intros * Hnacc Hstep Hacc.
  induction Hstep.  
  - eauto using aux1.
  - destruct (Nat.eqb ad ad0) eqn:E.
    + eapply Nat.eqb_eq in E; subst.
    +
    eapply aux1 in Hnacc. 
    eexists. inversion Hacc; subst; eauto.
    eapply aux1 in Hnacc.
    shelve.
  - eapply aux2 in Hnacc. eapply IHHstep; eauto.
    inversion Hacc; subst; eauto.
    shelve.
  - shelve.
  - shelve.
  - shelve.
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
