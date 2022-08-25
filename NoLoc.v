From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.

Inductive NoLoc : tm -> Prop :=
  | noloc_unit :
      NoLoc TM_Unit

  | noloc_num : forall n,
      NoLoc (TM_Num n)

  | noloc_new : forall t,
      NoLoc t ->
      NoLoc (TM_New t)

  | noloc_load : forall t,
      NoLoc t ->
      NoLoc (TM_Load t)

  | noloc_asg : forall t1 t2,
      NoLoc t1 ->
      NoLoc t2 ->
      NoLoc (TM_Asg t1 t2)

  | noloc_fun : forall x X t,
      NoLoc t ->
      NoLoc (TM_Fun x X t)

  | noloc_call : forall t1 t2,
      NoLoc t1 ->
      NoLoc t2 ->
      NoLoc (TM_Call t1 t2)

  | noloc_seq : forall t1 t2,
      NoLoc t1 ->
      NoLoc t2 ->
      NoLoc (TM_Seq t1 t2)

  | noloc_spawn : forall t,
      NoLoc t ->
      NoLoc (TM_Spawn t)
  .

Inductive SpawnNoLoc : tm -> Prop :=
  | spawn_noloc_unit :
      SpawnNoLoc TM_Unit

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

  | spawn_noloc_asg : forall t1 t2,
      SpawnNoLoc t1 ->
      SpawnNoLoc t2 ->
      SpawnNoLoc (TM_Asg t1 t2)

  | spawn_noloc_fun : forall x X t,
      SpawnNoLoc t ->
      SpawnNoLoc (TM_Fun x X t)

  | spawn_noloc_call : forall t1 t2,
      SpawnNoLoc t1 ->
      SpawnNoLoc t2 ->
      SpawnNoLoc (TM_Call t1 t2)

  | spawn_noloc_seq : forall t1 t2,
      SpawnNoLoc t1 ->
      SpawnNoLoc t2 ->
      SpawnNoLoc (TM_Seq t1 t2)

  | spawn_noloc_spawn : forall t,
      NoLoc t ->
      SpawnNoLoc (TM_Spawn t)
  .

Local Ltac inversion_spawn_noloc :=
  match goal with
  | H : SpawnNoLoc TM_Unit        |- _ => inversion H; subst; clear H
  | H : SpawnNoLoc (TM_Num _)     |- _ => inversion H; subst; clear H
  | H : SpawnNoLoc (TM_Loc _)     |- _ => inversion H; subst; clear H
  | H : SpawnNoLoc (TM_New _)     |- _ => inversion H; subst; clear H
  | H : SpawnNoLoc (TM_Load _)    |- _ => inversion H; subst; clear H
  | H : SpawnNoLoc (TM_Asg _ _)   |- _ => inversion H; subst; clear H
  | H : SpawnNoLoc (TM_Fun _ _ _) |- _ => inversion H; subst; clear H
  | H : SpawnNoLoc (TM_Call _ _)  |- _ => inversion H; subst; clear H
  | H : SpawnNoLoc (TM_Seq _ _)   |- _ => inversion H; subst; clear H
  | H : SpawnNoLoc (TM_Spawn _)   |- _ => inversion H; subst; clear H
  end.

Local Lemma spawn_noloc_subst : forall x X t t',
  SpawnNoLoc (TM_Fun x X t) ->
  SpawnNoLoc t' ->
  SpawnNoLoc ([x := t'] t).
Proof.
  intros * H ?. inversion H; clear H; subst.
  induction t; eauto using SpawnNoLoc; simpl; 
  try (destruct String.eqb; trivial);
  inversion_spawn_noloc; eauto using SpawnNoLoc.
Qed.

Local Lemma spawn_noloc_alloc : forall m t t' v,
  SpawnNoLoc t ->
  memory_property SpawnNoLoc m ->
  t --[EF_Alloc (length m) v]--> t' ->
  memory_property SpawnNoLoc (add m v).
Proof.
  intros. assert (SpawnNoLoc v).
  { induction_step; inversion_spawn_noloc; eauto. }
  unfold memory_property. eauto using property_add, SpawnNoLoc.
Qed.

Local Lemma spawn_noloc_store : forall m t t' ad v,
  memory_property SpawnNoLoc m ->
  SpawnNoLoc t ->
  t --[EF_Store ad v]--> t' ->
  memory_property SpawnNoLoc (set m ad v).
Proof.
  intros. assert (SpawnNoLoc v).
  { induction_step; inversion_spawn_noloc; eauto. }
  unfold memory_property. eauto using property_set, SpawnNoLoc.
Qed.

Local Lemma mstep_mem_spawn_noloc_preservation : forall (m m' : mem) t t' eff,
  memory_property SpawnNoLoc m ->
  SpawnNoLoc t ->
  m / t ==[eff]==> m' / t' ->
  memory_property SpawnNoLoc m'.
Proof.
  intros. inversion_mstep; eauto using spawn_noloc_alloc, spawn_noloc_store.
Qed.

Local Lemma mstep_tm_spawn_noloc_preservation : forall m m' t t' eff,
  memory_property SpawnNoLoc m ->
  SpawnNoLoc t ->
  m / t ==[eff]==> m' / t' ->
  SpawnNoLoc t'.
Proof.
  intros. inversion_mstep; induction_step; inversion_spawn_noloc;
  eauto using SpawnNoLoc, spawn_noloc_subst.
Qed.

Local Lemma noloc_then_spawn_noloc : forall t,
  NoLoc t ->
  SpawnNoLoc t.
Proof.
  intros. induction t;
  match goal with
  | H : NoLoc _ |- _ =>
    induction H; eauto using SpawnNoLoc
  end.
Qed.

Local Lemma spawn_noloc_for_block : forall t t' block,
  SpawnNoLoc t ->
  t --[EF_Spawn block]--> t' ->
  SpawnNoLoc block.
Proof.
  intros. induction_step; inversion_spawn_noloc;
  eauto using SpawnNoLoc, noloc_then_spawn_noloc.
Qed.

Local Lemma step_spawn_noloc_preservation : forall t t' block,
  SpawnNoLoc t ->
  t --[EF_Spawn block]--> t' ->
  SpawnNoLoc t'.
Proof.
  intros. induction_step; inversion_spawn_noloc;
  eauto using SpawnNoLoc, noloc_then_spawn_noloc.
Qed.

Theorem spawn_noloc_preservation : forall m m' ths ths' tid eff,
  memory_property SpawnNoLoc m ->
  threads_property SpawnNoLoc ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  (memory_property SpawnNoLoc m' /\ threads_property SpawnNoLoc ths').
Proof.
  intros. split; inversion_cstep;
  eauto using mstep_mem_spawn_noloc_preservation.
  - eapply property_set; eauto using SpawnNoLoc.
    eauto using mstep_tm_spawn_noloc_preservation. (* performance *)
  - eapply property_add; eauto using SpawnNoLoc, spawn_noloc_for_block.
    eapply property_set; eauto using SpawnNoLoc, step_spawn_noloc_preservation.
Qed.

Lemma noloc_for_block : forall t t' block,
  SpawnNoLoc t ->
  t --[EF_Spawn block]--> t' ->
  NoLoc block.
Proof.
  intros. induction_step; inversion_spawn_noloc; eauto.
Qed.

Lemma noloc_then_not_access : forall m t ad,
  NoLoc t ->
  ~ access m t ad.
Proof.
  intros * Hnl. induction t; inversion Hnl; subst;
  eauto using not_access_new, not_access_load, not_access_asg, not_access_fun,
    not_access_call, not_access_seq;
  intros ?; inversion_access.
Qed.

