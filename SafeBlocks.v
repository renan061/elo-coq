From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import UnsafeAccess.

Reserved Notation " t 'contains_block' t' " (at level 30, no associativity).

Inductive ContainsBlock (t' : tm) : tm -> Prop :=
  | contains_block_new : forall t T,
    t contains_block t' ->
    <{ new T t }> contains_block t'

  | contains_block_load : forall t,
    t contains_block t' ->
    <{ *t }> contains_block t'

  | contains_block_asg1 : forall t1 t2,
    t1 contains_block t' ->
    <{ t1 = t2 }> contains_block t'

  | contains_block_asg2 : forall t1 t2,
    t2 contains_block t' ->
    <{ t1 = t2 }> contains_block t'

  | contains_block_fun : forall t x Tx,
    t contains_block t' ->
    <{ fn x Tx --> t }> contains_block t'

  | contains_block_call1 : forall t1 t2,
    t1 contains_block t' ->
    <{ call t1 t2 }> contains_block t'

  | contains_block_call2 : forall t1 t2,
    t2 contains_block t' ->
    <{ call t1 t2 }> contains_block t'

  | contains_block_seq1 : forall t1 t2,
    t1 contains_block t' ->
    <{ t1; t2 }> contains_block t'

  | contains_block_seq2 : forall t1 t2,
    t2 contains_block t' ->
    <{ t1; t2 }> contains_block t'

  | contains_block_spawn : forall t,
    t contains_block t' ->
    <{ spawn t }> contains_block t'

  | contains_block_eq : forall block,
    block = t' ->
    <{ spawn block }> contains_block t'

  where "t 'contains_block' t'" := (ContainsBlock t' t).

Lemma contains_block_trans : forall t1 t2 t3,
  t1 contains_block t2 ->
  t2 contains_block t3 ->
  t1 contains_block t3.
Proof.
  intros * Hcon ?. induction Hcon; subst; eauto using ContainsBlock.
Qed.

Lemma step_spawn_contains_block : forall t t' block,
  t --[EF_Spawn block]--> t' ->
  t contains_block block.
Proof.
  intros. induction_step; eauto using ContainsBlock.
Qed.

(* -------------------------------------------------------------------------- *)
(* safe-blocks                                                                *)
(* -------------------------------------------------------------------------- *)

Definition SafeBlocks (m : mem) (t : tm) := forall block ad,
  access m t ad ->
  t contains_block block ->
  access m block ad ->
  ~ UnsafeAccess m t ad.

