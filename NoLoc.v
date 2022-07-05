From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core0.
From Elo Require Import Access.

Inductive NoLoc : tm -> Prop :=
  | noloc_nil :
      NoLoc TM_Nil

  | noloc_num : forall n,
      NoLoc (TM_Num n)

  | noloc_new : forall t,
      NoLoc t ->
      NoLoc (TM_New t)

  | noloc_load : forall t,
      NoLoc t ->
      NoLoc (TM_Load t)

  | noloc_asg : forall l r,
      NoLoc l ->
      NoLoc r ->
      NoLoc (TM_Asg l r)

  | noloc_seq : forall t1 t2,
      NoLoc t1 ->
      NoLoc t2 ->
      NoLoc (TM_Seq t1 t2)

  | noloc_spawn : forall block,
      NoLoc block ->
      NoLoc (TM_Spawn block)
  .

Inductive SpawnNoLoc : tm -> Prop :=
  | spawn_noloc_nil :
      SpawnNoLoc TM_Nil

  | spawn_noloc_num : forall n,
      SpawnNoLoc (TM_Num n)

  | spawn_noloc_loc : forall ad,
      SpawnNoLoc (TM_Loc ad)

  | spawn_noloc_new : forall t,
      SpawnNoLoc t ->
      SpawnNoLoc (TM_New t)

  | spawn_noloc_load : forall t,
      SpawnNoLoc t ->
      SpawnNoLoc (TM_Load t)

  | spawn_noloc_asg : forall l r,
      SpawnNoLoc l ->
      SpawnNoLoc r ->
      SpawnNoLoc (TM_Asg l r)

  | spawn_noloc_seq : forall t1 t2,
      SpawnNoLoc t1 ->
      SpawnNoLoc t2 ->
      SpawnNoLoc (TM_Seq t1 t2)

  | spawn_noloc_spawn : forall block,
      NoLoc block ->
      SpawnNoLoc (TM_Spawn block)
  .

Definition memory_has_values (m : mem) :=
  forall ad, value (getTM m ad).

Lemma memory_has_values_preservation : forall m m' t t' eff,
  memory_has_values m ->
  m / t ==[eff]==> m' / t' ->
  memory_has_values m'.
Proof.
  intros. inversion_mstep; trivial.
  - remember (EF_Alloc _ _) as eff.
    induction_step; inversion Heqeff; subst; eauto. intros ad.
    decompose sum (lt_eq_lt_dec ad (length m)); subst.
    + rewrite (get_add_lt TM_Nil); trivial.
    + rewrite (get_add_eq TM_Nil); trivial.
    + rewrite (get_add_gt TM_Nil); eauto using value.
  - remember (EF_Store _ _) as eff.
    induction_step; inversion Heqeff; subst; eauto. intros ad'.
    decompose sum (lt_eq_lt_dec ad' ad); subst.
    + rewrite (get_set_lt TM_Nil); trivial.
    + rewrite (get_set_eq TM_Nil); trivial.
    + rewrite (get_set_gt TM_Nil); trivial.
Qed.

Theorem mstep_spawn_noloc_preservation : forall m m' t t' eff,
  memory_has_values m ->
  SpawnNoLoc t ->
  m / t ==[eff]==> m' / t' ->
  SpawnNoLoc t'.
Proof.
  intros * ? Hsnl Hmstep. inversion Hmstep; subst.
  - clear Hmstep. remember EF_None as eff.
    induction_step; inversion Heqeff; subst;
    inversion Hsnl; subst; eauto using SpawnNoLoc.
  - clear Hmstep. remember (EF_Alloc (length m) v) as eff.
    induction_step; inversion Heqeff; subst;
    inversion Hsnl; subst; eauto using SpawnNoLoc.
  - assert (Hvalue : value (getTM m' ad))
      by eauto using memory_has_values_preservation.
    clear Hmstep. remember (EF_Load ad (getTM m' ad)) as eff.
    induction_step; inversion Heqeff; subst;
    inversion Hsnl; subst; eauto using SpawnNoLoc.
    destruct Hvalue; eauto using SpawnNoLoc.
  - clear Hmstep. remember (EF_Store ad v) as eff.
    induction_step; inversion Heqeff; subst;
    inversion Hsnl; subst; eauto using SpawnNoLoc.
Qed.

Local Lemma spawn_noloc_for_block : forall t t' block,
  SpawnNoLoc t ->
  t --[EF_Spawn block]--> t' ->
  SpawnNoLoc block.
Proof.
  intros * Hsnl Hstep. remember (EF_Spawn _) as eff.
  induction_step; inversion Heqeff; subst;
  inversion Hsnl; subst; eauto. clear Hsnl.
  match goal with H : NoLoc _ |- _ => induction H; eauto using SpawnNoLoc end.
Qed.

Theorem spawn_noloc_preservation : forall m m' ths ths' tid eff,
  memory_has_values m ->
  (forall tid, SpawnNoLoc (getTM ths tid)) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  (forall tid, SpawnNoLoc (getTM ths' tid)).
Proof.
  intros * ? Hsnl Hcstep. inversion_cstep.
  - intros tid'. destruct (Nat.eq_dec tid tid'); subst.
    + rewrite (get_set_eq TM_Nil); eauto using mstep_spawn_noloc_preservation.
    + rewrite (get_set_neq TM_Nil); trivial. lia.
  - intros tid'.
    decompose sum (lt_eq_lt_dec tid (length ths)); subst; try lia.
    destruct (Nat.eq_dec tid tid'); subst.
    + rewrite (get_add_lt TM_Nil).
      * rewrite (get_set_eq TM_Nil); trivial.
        specialize (Hsnl tid').
        remember (EF_Spawn _) as eff.
        induction_step; inversion Heqeff; subst;
        inversion Hsnl; subst; eauto using SpawnNoLoc.
      * rewrite set_preserves_length. trivial.
    + decompose sum (lt_eq_lt_dec tid' (length ths)); subst.
      * rewrite (get_add_lt TM_Nil).
        ** rewrite (get_set_neq TM_Nil); trivial. lia.
        ** rewrite set_preserves_length; trivial.
      * erewrite <- set_preserves_length.
        rewrite (get_add_eq TM_Nil).
        eauto using spawn_noloc_for_block.
      * rewrite (get_add_gt TM_Nil).
        ** eauto using SpawnNoLoc.
        ** rewrite set_preserves_length; trivial.
Qed.

Lemma noloc_for_block : forall t t' block,
  SpawnNoLoc t ->
  t --[EF_Spawn block]--> t' ->
  NoLoc block.
Proof.
  intros * Hsnl ?. remember (EF_Spawn _) as eff.
  induction_step; inversion Heqeff; subst;
  inversion Hsnl; subst; eauto.
Qed.

Lemma noloc_then_not_access : forall m t ad,
  NoLoc t ->
  ~ access m t ad.
Proof.
  intros * Hnl. induction t; inversion Hnl; subst;
  eauto using not_access_new, not_access_load, not_access_asg, not_access_seq;
  intros ?; inversion_access.
Qed.


(*

  SpawnNoLoc -> NoLoc -> ~ access -> disjoint 

*)
