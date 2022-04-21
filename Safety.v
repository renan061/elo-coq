From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core0.

Reserved Notation "m / t '==[' tc ']==>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_mem : forall t ad ad',
    get_tm m ad = TM_Loc ad' ->
    access m t ad ->
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

Lemma new_access : forall m t ad,
  access m (TM_New t) ad ->
  access m t ad.
Proof.
  intros * Hacc. remember (TM_New t) as t'.
  induction Hacc; inversion Heqt'; subst; eauto using access.
Qed.

Lemma load_access : forall m t ad,
  access m (TM_Load t) ad ->
  access m t ad.
Proof.
  intros * Hacc. remember (TM_Load t) as t'.
  induction Hacc; inversion Heqt'; subst; eauto using access.
Qed.

Lemma asg_access : forall m l r ad,
  access m (TM_Asg l r) ad ->
  access m l ad \/ access m r ad.
Proof.
  intros * Hacc. remember (TM_Asg l r) as t.
  induction Hacc; inversion Heqt; subst; eauto.
  destruct (IHHacc eq_refl) as [? | ?]; eauto using access.
Qed.

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
    intros * Hmstep. inversion Hmstep; subst;
    try (rewrite <- Array.set_preserves_length);
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

(* PART 2 *)

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

Lemma outraaqui : forall m t ad,
  well_behaved_access m (TM_Loc ad) ->
  access (add m (TM_Loc ad)) t (length m) ->
  access m t ad.
Proof.
  intros * Hwba Hacc.
  remember (length m) as ad'.
  remember (TM_Loc ad) as v.
  remember (add m v) as m'.
  induction Hacc;
  try solve [subst; eauto using access].
  - eauto using access.
    shelve.
  - unfold well_behaved_access in Hwba.
    subst.
Abort.

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

(* TODO *)

Module wba.

Local Lemma wba_new_iff : forall m t,
  well_behaved_access m (TM_New t) <->
  well_behaved_access m t.
Proof.
  intros. split; intros ? ?; eauto using access, new_access. 
Qed.

Local Lemma wba_load_iff : forall m t,
  well_behaved_access m (TM_Load t) <->
  well_behaved_access m t.
Proof.
  intros. split; intros ? ?; eauto using access, load_access.
Qed.

Local Lemma wba_asg_iff : forall m l r,
  well_behaved_access m (TM_Asg l r) <->
  well_behaved_access m l /\ well_behaved_access m r.
Proof.
  intros. split.
  - intros. split; intros ? ?; eauto using access.
  - intros [? ?] ? Hacc. eapply asg_access in Hacc as [? | ?]; eauto.
Qed.

Local Lemma wba_alloc_value: forall m t t' ad v,
  well_behaved_access m t ->
  t --[EF_Alloc ad v]--> t' ->
  well_behaved_access m v.
Proof.
  intros * Hwba Hstep.
  remember (EF_Alloc ad v) as eff.
  induction Hstep; inversion Heqeff; subst;
  try ( rewrite wba_new_iff in Hwba
     || rewrite wba_load_iff in Hwba
     || eapply wba_asg_iff in Hwba as [? ?]
     );
  eauto.
Qed.

Local Lemma access_add : forall m t ad v,
  well_behaved_access m t ->
  access (add m v) t ad ->
  access m t ad.
Proof.
  intros * Hwba Hacc.
  remember (add m v) as m'.
  induction Hacc; subst;
  try ( rewrite wba_new_iff in Hwba
     || rewrite wba_load_iff in Hwba
     || eapply wba_asg_iff in Hwba as [? ?]
     );
  eauto using access.
  match goal with
    IH : well_behaved_access _ _ -> _, Hget : get_tm _ _ = _ |- _ =>
      destruct (lt_eq_lt_dec ad (length m)) as [[Hlt | Heq] | Hgt];
      try solve [specialize (Hwba _ (IH Hwba)); lia];
      rewrite (get_add_lt TM_Nil) in Hget; eauto using access
  end.
Qed.

Local Lemma wba_add: forall m t v,
  well_behaved_access m t ->
  well_behaved_access (add m v) t.
Proof.
  intros * Hwba ad Hacc.
  destruct (lt_eq_lt_dec (ad) (length m)) as [[? | ?] | ?];
  try solve [rewrite length_add; lia].
  exfalso. eapply access_add in Hacc; eauto. specialize (Hwba ad Hacc). lia.
Qed.

(*
Local Lemma access_add : forall m t ad v,
  well_behaved_access m t ->
  access (add m v) t ad ->
  access m t ad.
*)

Local Lemma loc_access : forall m ad v,
  well_behaved_access m v ->
  access (add m v) (TM_Loc (length m)) ad ->
  access m v ad.
Proof.
  intros * Hwba Hacc.
Admitted.

Local Lemma alloc_preservation : forall m t t' v,
  well_behaved_access m t ->
  t --[ EF_Alloc (length m) v ]--> t' ->
  well_behaved_access (add m v) t'.
Proof.
  intros * Hwba Hstep.
  remember (EF_Alloc (length m) v) as eff.
  induction Hstep; inversion Heqeff; subst.
  - rewrite wba_new_iff in Hwba. eauto.
  - rewrite wba_new_iff in Hwba.
    intros ad Hacc.
    rewrite length_add.
    eapply Nat.lt_lt_succ_r.
    eapply (Hwba ad).
    eauto using loc_access.
  - eapply wba_load_iff. rewrite wba_load_iff in Hwba. eauto.
  - eapply wba_asg_iff in Hwba as [? ?].
    eapply wba_asg_iff.
    split; eauto using wba_add.
  - eapply wba_asg_iff in Hwba as [? ?].
    eapply wba_asg_iff.
    split; eauto using wba_add.
Qed.

Lemma preservation : forall m m' t t' eff, 
  well_behaved_access m t ->
  m / t ==[eff]==> m' / t' ->
  well_behaved_access m' t'.
Proof.
  intros * Hwba Hmstep. inversion Hmstep; subst.
  - eauto using alloc_preservation.
  - shelve.
  - shelve.
Admitted.

End wba.









(* BAGUNÇA *)

Lemma aux12 : forall m ad v,
  access (add m v) (TM_Loc (length m)) ad ->
  ad <> length m ->
  access m v ad.
Proof.
  intros * Hacc.
  remember (add m v) as m'.
  remember (TM_Loc (length m)) as t'.
  induction Hacc; intros Hlen;
  inversion Heqm'; subst;
  try (inversion Heqt'; subst).
  - specialize (IHHacc eq_refl).
    shelve.
  - exfalso. eauto.
Admitted.

Lemma aux11 : forall m ad n,
  access (add m (TM_Num n)) (TM_Loc (length m)) ad ->
  ad = length m.
Proof.
  intros * Hacc.
  remember (add m TM_Nil) as m'.
  remember (TM_Loc (length m)) as t'.
  induction Hacc;
  inversion Heqm'; subst;
  try (inversion Heqt'; subst); trivial.
  specialize (IHHacc eq_refl); subst.
  exfalso.
  rewrite (get_add_last TM_Nil) in H.
  inversion H.
Qed.

Lemma aux10 : forall m ad,
  access (add m TM_Nil) (TM_Loc (length m)) ad ->
  ad = length m.
Proof.
  intros * Hacc.
  remember (add m TM_Nil) as m'.
  remember (TM_Loc (length m)) as t'.
  induction Hacc;
  inversion Heqm'; subst; try (inversion Heqt'; subst); trivial.
(*
  specialize (IHHacc eq_refl). subst.
  exfalso.
  rewrite (get_add_last TM_Nil) in H.
  inversion H.
*)
Admitted.

Lemma aux9 : forall m t ad ad',
  ~ access m t ad ->
  access m t ad' ->
  get_tm m ad' <> TM_Loc ad.
Proof.
  intros * ? Hacc. inversion Hacc; subst; eauto using access.
Qed.

Lemma aux8 : forall m t ad ad',
  ~ access m t ad ->
  get_tm m ad' = TM_Loc ad ->
  ~ access m t ad'.
Proof.
  intros * Hget Hnacc Hacc. eauto using access. 
Qed.

Lemma aux5 : forall m t ad,
  ~ access m (TM_New t) ad ->
  ~ access m t ad.
Proof.
  intros * Hnacc F. eauto using access.
Qed.

Lemma aux4 : forall m t ad v,
  access (add m v) t ad ->
  ~ access m v ad ->
  ad <> length m ->
  access m t ad.
Proof.
  intros * Hacc Hnacc Hlen. remember (add m v) as m'.
  induction Hacc; inversion Heqm'; subst; eauto using access.
  destruct (lt_eq_lt_dec ad (length m)) as [[Hlt | Heq] | Hgt].
  (*
  - rewrite (get_add_lt TM_Nil _ _ _ Hlt) in H.
    eauto using Nat.lt_neq, access. shelve.
  - subst; clear H0.
    rewrite (get_add_last TM_Nil) in H.
    destruct v eqn:E; inversion H.
    shelve.
  - rewrite (get_add_gt TM_Nil _ _ _ Hgt) in H. inversion H.
  *)
Admitted.

Lemma aux3 : forall m l r ad,
  ~ access m (TM_Asg l r) ad ->
  ~ access m l ad /\ ~ access m r ad.
Proof.
  intros * Hnacc. split; intros F; eauto using access.
Qed.

Lemma aux2 : forall m t ad,
  ~ access m (TM_Load t) ad ->
  ~ access m t ad.
Proof.
  intros * Hnacc F. eauto using access.
Qed.

Lemma aux1 : forall m m' t t' ad ad' v,
  ~ access m t ad ->
  ~ access m v ad ->
  m / t ==[EF_Alloc ad' v]==> m' / t' ->
  ad <> ad' ->
  ~ access m' t' ad.
Proof.
  intros * Hnacc1 Hnacc2 Hmstep Hneq.
  inversion Hmstep; subst. clear Hmstep.
  remember (EF_Alloc (length m) v) as eff.
  induction H5; inversion Heqeff; subst; eauto using access.
  - intros F. destruct H; eauto using aux10, aux11.
    eapply aux5 in Hnacc1.
    eapply aux12 in F; eauto.
  - eapply aux2 in Hnacc1.
    specialize (IHstep Hnacc1 eq_refl).
    intros F. eapply load_access in F. eauto.
  - eapply aux3 in Hnacc1 as [HnaccL HnaccR].
    specialize (IHstep HnaccL eq_refl).
    intros F. eapply asg_access in F as [F | F].
    + eapply IHstep in F. assumption.
    + eapply HnaccR. eauto using aux4.
  - eapply aux3 in Hnacc1 as [HnaccL HnaccR].
    specialize (IHstep HnaccR eq_refl).
    intros F. eapply asg_access in F as [F | F].
    + eauto using aux4.
    + eapply IHstep in F. assumption.
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



(*
Lemma monotonic_nondecreasing_memory_length: forall m m' eff t t',
  m / t ==[eff]==>* m' / t' ->
  length m <= length m'.
Proof.
*)

Lemma aux1 : forall t ad ad' v,
  t --[ EF_Alloc ad v ]--> TM_Loc ad' ->
  ad = ad'.
Proof.
  intros * Hstep.
  remember (EF_Alloc ad v) as eff.
  remember (TM_Loc ad') as t'.
  induction Hstep;
  inversion Heqeff; subst;
  try (inversion Heqt'; subst); eauto.
Qed.




  - remember (EF_Alloc (length m) v) as eff.
    induction H; try (inversion Heqeff; subst);
    subst; eauto using access, load_access.
    + inversion Hacc; subst.
      * rewrite length_add. eapply Nat.lt_lt_succ_r. eapply Hwba.
        shelve.
      * eauto using length_lt_add.
    + inversion Hacc; subst.
      * shelve.
      *
      *

        
      
      eapply access_new.


    induction Hacc.
    + shelve.
    + eapply aux1 in H. subst. eapply length_lt_add.
    + eapply IHHacc; eauto.
      * 
      *
      *

  - destruct (lt_eq_lt_dec ad (length m)) as [[Hlt | Heq] | Hgt].
    + rewrite length_add. eauto using Nat.lt_lt_succ_r.
    + subst. eauto using length_lt_add.
    + exfalso.
      assert (TODO: forall n m, n < m -> ~ m < n). shelve.
      specialize (TODO _ _ Hgt). eapply TODO. eapply Hwba.
      clear Hwba; clear TODO; clear Hmstep.
      remember (EF_Alloc (length m) v) as eff.
      generalize dependent Hacc.
      induction H; eauto using access, load_access.
      * inversion Heqeff; subst. intros Hacc; inversion Hacc; subst.
        ** eauto using access. shelve.
        ** contradict Hgt. eauto using Nat.lt_irrefl.
      * inversion Heqeff.
      * subst.
Admitted.

Lemma something: forall m m' t t' ad' tc,
  (forall ad, ~ access m t ad) ->
  m / t ==[tc]==>* m' / t' ->
  well_behaved_access m' t' ad'.
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
