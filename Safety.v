From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Logic.ClassicalFacts.

From Elo Require Export Core0.

Reserved Notation "m / t / tc '==>*' m' / t' / tc'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Definition trace := list effect.

Inductive has_access (m : mem) : tm -> addr -> Prop :=
  | has_access_trans : forall t ad ad',
    get_tm m ad = TM_Loc ad' ->
    has_access m t ad ->
    has_access m t ad'

  | has_access_loc : forall ad,
    has_access m (TM_Loc ad) ad

  | has_access_new : forall t ad,
    has_access m t ad ->
    has_access m (TM_New t) ad

  | has_access_load : forall t ad,
    has_access m t ad ->
    has_access m (TM_Load t) ad

  | has_access_asg1 : forall l r ad,
    has_access m l ad ->
    has_access m (TM_Asg l r) ad

  | has_access_asg2 : forall l r ad,
    has_access m r ad ->
    has_access m (TM_Asg l r) ad
  .

Theorem aux1 : forall m t t' ad v,
  t' --[EF_Alloc ad v]--> t ->
  has_access m t ad.
Proof.
  intros ? ? ?. generalize dependent t.
  induction t'; intros * Hstep;
  inversion Hstep; eauto using has_access.
Qed.

Inductive multistep : mem -> tm -> trace -> mem -> tm -> trace -> Prop :=
  | multistep_first : forall main ad,
    ~ (has_access nil main ad) ->
    nil / TM_Nil / nil ==>* nil / main / (EF_None :: nil)

  | multistep_step : forall m m' m'' t t' t'' tc tc' ceff,
    m  / t / tc ==>* m' / t' / tc' ->
    m' / t' ==[ceff]==> m'' / t'' ->
    m  / t / tc ==>* m'' / t'' / (ceff :: tc')

  where "m / t / tc '==>*' m' / t' / tc'" := (multistep m t tc m' t' tc').










Lemma ceff_eq_dec : forall (x y : ceffect),
  x = y \/ x <> y.
Admitted.

Theorem todo : forall m_ m ths_ ths tc_ tc tid ad v,
  m_ / ths_ / tc_ ==>* m / ths / (CEF_Load tid ad v :: tc) ->
  In (CEF_Alloc tid ad v) tc.
Proof.
  intros * Hmstep.
  inversion Hmstep. subst.




induction tc as [| ceff tc' IH].
  - inversion Hmstep; subst. inversion H6.
  - destruct (ceff_eq_dec ceff (CEF_Alloc tid ad v)); subst.
    + eapply in_eq.
    + eapply in_cons. clear H.
      inversion Hmstep. subst.
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