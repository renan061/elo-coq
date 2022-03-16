From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Logic.ClassicalFacts.

From Elo Require Export Core0.

Reserved Notation "m / t '==[' tc ']==>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Definition trace := list effect.

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

Inductive multistep : mem -> tm -> trace -> mem -> tm -> Prop :=
  | multistep_refl : forall m t tc,
    m / t ==[tc]==>* m / t

  | multistep_step : forall m m' m'' t t' t'' tc eff,
    m  / t  ==[tc       ]==>* m'  / t'  ->
    m' / t' ==[eff      ]==>  m'' / t'' ->
    m  / t  ==[eff :: tc]==>* m'' / t''

  where "m / t '==[' tc ']==>*' m' / t'" := (multistep m t tc m' t').

Lemma alloc_grants_access_1 : forall m m' t t' ad v,
  ~ (access m t ad) ->
  t --[EF_Alloc ad v]--> t' ->
  access m' t' ad.
Proof.
  intros ? ? ?. induction t; intros * Hacc Hstep;
  inversion Hstep; eauto using access.
  - eapply access_load; eauto using access.
  - eapply access_asg1; eauto using access.
  - eapply access_asg2; eauto using access.
Qed.

Lemma alloc_grants_access_2 : forall m m' t t' ad v,
  ~ (access m t ad) ->
  m / t ==[EF_Alloc ad v]==> m' / t' ->
  access m' t' ad.
Proof.
  intros * Hacc Hmstep. destruct t';
  inversion Hmstep; subst; eauto using alloc_grants_access_1.
Qed.

Lemma alloc_grants_access_3 : forall m m' tc t t' ad v,
  ~ (access m t ad) ->
  m / t ==[EF_Alloc ad v :: tc]==>* m' / t' ->
  access m' t' ad.
Proof.
  intros * Hacc Hmultistep. inversion Hmultistep; subst.
  -
  - inversion Hmultistep; subst.
    + inversion Hmultistep.
  inversion Hmultistep; subst; eauto using alloc_grants_access_2.
Qed.



Lemma eff_eq_dec : forall (x y : effect),
  {x = y} + {x <> y}.
Proof.
Admitted.

Definition NotIn {A} (a : A) l := ~ (In a l).

Lemma duplicate_alloc' : forall {m m' t t'} tc {ad v},
  m / t / tc ==>* m' / t' / (EF_Alloc ad v :: tc) ->
  NotIn (EF_Alloc ad v) tc.
Proof.
  unfold NotIn. intros * Hmstep. induction Hmstep; eauto using in_nil.
Qed.

Lemma duplicate_alloc : forall m m' t t' tc tc' ad v,
  m / t / tc ==>* m' / t' / (EF_Alloc ad v :: tc') ->
  ~ (In (EF_Alloc ad v) tc').
Proof.
  intros * Hmstep. destruct tc' as [| x xs].
  - eauto using in_nil.
  - destruct (eff_eq_dec (EF_Alloc ad v) x).
    + subst. destruct (list_eq_dec eff_eq_dec xs tc).
      * subst. exfalso. eapply (duplicate_alloc'). eapply Hmstep.
      * 
Qed.

Lemma aux1 : forall {A} l1 l2 (a : A), 
  (~ (In a (l1 ++ l2))) = ~ (In a l1) /\ ~ (In a l2).
Proof.
Admitted.

Lemma duplicate_alloc : forall m m' t t' tc tc' ad v,
  m / t / tc ==>* m' / t' / (EF_Alloc ad v :: tc') ->
  ~ (In (EF_Alloc ad v) tc').
Proof.
  intros * Hmstep.
  assert (exists x, tc' = x ++ tc) as [x Htc]. { shelve. } subst.
  erewrite aux1. split.
  - destruct x as [| x xs].
    + eauto using in_nil.
    + destruct (eq_dec_eff (EF_Alloc ad v) x).
      * shelve.
      * eapply not_in_cons. split; auto.
        inversion Hmstep; subst.
        inversion H6; subst.
        ** erewrite app_nil_r in H8. subst. eauto using in_nil.
        ** induction xs.
          *** shelve.
          ***
  - eauto using duplicate_alloc'.
Qed.





Lemma aux1 : forall m m' t t' tc tc' tc'' eff,
  m' / t' / tc' ==>* m / t / (eff :: tc) ->
  m' / t' / tc' ==>* m / t / ((eff :: tc'') ++ tc').
Proof.
Admitted.

Lemma in_dec_eff : forall (eff : effect) (l : list effect),
  {In eff l} + {~ In eff l}.
Proof.
  intros *. eauto using in_dec, eq_dec_eff.
Qed.

Theorem todo : forall m m' t t' tc tc' ad v,
  m' / t' / tc' ==>* m / t / (EF_Load ad v :: tc) ->
  In (EF_Alloc ad v) tc.
Proof.
  intros * Hmstep.
  assert (In1 : {In (EF_Alloc ad v) tc} + {~ In (EF_Alloc ad v) tc}).
  eauto using in_dec_eff. destruct In1 as [In1 | NIn1].
  - auto.
  - assert (In2 : {In (EF_Alloc ad v) tc'} + {~ In (EF_Alloc ad v) tc'}).
    eauto using in_dec_eff. destruct In2 as [In2 | NIn2].
    + auto.
    +


  induction tc_ as [| ceff tc' IH].
  - inversion Hmstep; subst.
  - destruct (ceff_eq_dec ceff (EF_Alloc ad v)); subst.
    + eapply in_eq.
    + eapply in_cons. clear H.
      inversion Hmstep; subst.
      inversion H6; subst.
      * shelve.
      *


      inversion Hmstep. subst. clear Hmstep.
      induction H7.
      * inversion H8. subst.
      eapply IH. clear IH.

Qed.





(*

Inductive something : 
  | Something_Load
    tid = alguma thread
    m / ths ==> m' / ths' # Load tid 23
    em todas as outras threads que não são tid,
    não pode ter Loc 23
    
*)