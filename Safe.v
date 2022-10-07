From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.

(* A term is NoMut if it has no mutable references. *)
Inductive NoMut : tm -> Prop :=
  | nomut_unit :
    NoMut <{ unit }>

  | nomut_num : forall n,
    NoMut <{ N n }>

  | nomut_refI : forall ad T,
    NoMut <{ &ad :: i&T }>

  | nomut_new : forall T t,
    NoMut t ->
    NoMut <{ new T t }>

  | nomut_load : forall t,
    NoMut t ->
    NoMut <{ *t }>

  | nomut_asg : forall t1 t2,
    NoMut t1 ->
    NoMut t2 ->
    NoMut <{ t1 = t2 }>

  | nomut_id : forall x,
    NoMut <{ ID x }>

  | nomut_fun : forall x Tx t,
    NoMut t ->
    NoMut <{ fn x Tx --> t }>

  | nomut_call : forall t1 t2,
    NoMut t1 ->
    NoMut t2 ->
    NoMut <{ call t1 t2 }>

  | nomut_seq : forall t1 t2,
    NoMut t1 ->
    NoMut t2 ->
    NoMut <{ t1; t2 }>

  | nomut_spawn : forall t,
    NoMut t ->
    NoMut <{ spawn t }>
  .

(* A term has safe spawns if all its spawns have no mutable references. *)
Inductive SafeSpawns : tm -> Prop :=
  | safe_spawns_unit :
      SafeSpawns <{ unit }>

  | safe_spawns_num : forall n,
      SafeSpawns <{ N n }>

  | safe_spawns_ref : forall ad T,
      SafeSpawns <{ &ad :: T }>

  | safe_spawns_new : forall T t,
      SafeSpawns t ->
      SafeSpawns <{ new T t }>

  | safe_spawns_load : forall t,
      SafeSpawns t ->
      SafeSpawns <{ *t }>

  | safe_spawns_asg : forall t1 t2,
      SafeSpawns t1 ->
      SafeSpawns t2 ->
      SafeSpawns <{ t1 = t2 }>

  | safe_spawns_id : forall x,
      SafeSpawns <{ ID x }>

  | safe_spawns_fun : forall x Tx t,
      SafeSpawns t ->
      SafeSpawns <{ fn x Tx --> t }>

  | safe_spawns_call : forall t1 t2,
      SafeSpawns t1 ->
      SafeSpawns t2 ->
      SafeSpawns <{ call t1 t2 }>

  | safe_spawns_seq : forall t1 t2,
      SafeSpawns t1 ->
      SafeSpawns t2 ->
      SafeSpawns <{ t1; t2 }>

  | safe_spawns_spawn : forall t,
      NoMut t ->
      SafeSpawns <{ spawn t }>
  .

Local Ltac inversion_safe_spawns :=
  match goal with
  | H : SafeSpawns TM_Unit   |- _ => inversion H; subst; clear H
  | H : SafeSpawns (_ _)     |- _ => inversion H; subst; clear H
  | H : SafeSpawns (_ _ _)   |- _ => inversion H; subst; clear H
  | H : SafeSpawns (_ _ _ _) |- _ => inversion H; subst; clear H
  end.

Local Lemma equivalent_safe : forall Gamma1 Gamma2,
  equivalent Gamma1 Gamma2 ->
  equivalent (safe Gamma1) (safe Gamma2).
Proof.
  unfold equivalent, safe. intros * Heq k.
  specialize (Heq k). rewrite Heq. trivial.
Qed.

Local Lemma equivalent_wtt : forall Gamma1 Gamma2 t T,
  equivalent Gamma1 Gamma2 ->
  Gamma1 |-- t is T ->
  Gamma2 |-- t is T.
Proof.
  intros * Heq Htype.
  generalize dependent Gamma2.
  induction Htype; intros;
  eauto using well_typed_term, equivalent_lookup, equivalent_update,
    equivalent_safe.
Qed.

Local Lemma safe_spawns_subst : forall x t t',
  (*
  Gamma[x <== Tx] |-- t is T ->
  Gamma |-- t' is Tx ->
  SafeSpawns <{ fn x Tx --> t }> ->
  *)
  SafeSpawns t ->
  SafeSpawns t' ->
  SafeSpawns ([x := t'] t).
Proof.
  intros * ? ?.
  induction t; simpl;
  try (destruct String.string_dec);
  inversion_safe_spawns; eauto using SafeSpawns.
  eapply safe_spawns_spawn.


  intros * HtypeT HtypeTx Hsst Hsst'.
  remember (Gamma[x <== Tx]) as Gamma'.
  generalize dependent Gamma. generalize dependent Gamma'.
  generalize dependent T. generalize dependent Tx.
  induction t; intros * ? ? ? ?; simpl; try (destruct String.string_dec);
  try inversion_type; inversion_safe_spawns; eauto using SafeSpawns.
  - eapply safe_spawns_fun.
    eapply (equivalent_wtt _ (Gamma[i <== t][x <== Tx])) in H4;
    eauto using equivalent_update_permutation.
    specialize (IHt H0 Tx T0).


    eauto using equivalent_wtt, equivalent_update_permutation,
      equivalent_update_overwrite.
    eapply IHt; eauto. 

  intros * ? ? H ?. inversion_clear H.
  generalize dependent t'. generalize dependent Gamma.
  generalize dependent T. generalize dependent Tx.
  induction t; intros;
  simpl; try (destruct String.string_dec); try inversion_type;
  inversion_safe_spawns; eauto using SafeSpawns.
  - eapply safe_spawns_fun.
    eapply IHt; eauto.
    admit.
  - eapply safe_spawns_spawn; eauto.
    admit.
Qed.

Local Lemma safe_spawns_alloc : forall m t t' v,
  SafeSpawns t ->
  memory_property SafeSpawns m ->
  t --[EF_Alloc (length m) v]--> t' ->
  memory_property SafeSpawns (m +++ v).
Proof.
  intros. assert (SafeSpawns v).
  { induction_step; inversion_safe_spawns; eauto. }
  unfold memory_property. eauto using property_add, SafeSpawns.
Qed.

Local Lemma safe_spawns_store : forall m t t' ad v,
  memory_property SafeSpawns m ->
  SafeSpawns t ->
  t --[EF_Write ad v]--> t' ->
  memory_property SafeSpawns m[ad <- v].
Proof.
  intros. assert (SafeSpawns v).
  { induction_step; inversion_safe_spawns; eauto. }
  unfold memory_property. eauto using property_set, SafeSpawns.
Qed.

Local Lemma mstep_mem_safe_spawns_preservation : forall (m m' : mem) t t' eff,
  memory_property SafeSpawns m ->
  SafeSpawns t ->
  m / t ==[eff]==> m' / t' ->
  memory_property SafeSpawns m'.
Proof.
  intros. inversion_mstep; eauto using safe_spawns_alloc, safe_spawns_store.
Qed.

Local Lemma mstep_tm_safe_spawns_preservation : forall m m' t t' eff,
  memory_property SafeSpawns m ->
  SafeSpawns t ->
  m / t ==[eff]==> m' / t' ->
  SafeSpawns t'.
Proof.
  intros. inversion_mstep; induction_step; inversion_safe_spawns;
  eauto using SafeSpawns, safe_spawns_subst.
Qed.

Local Lemma safe_then_safe_spawns : forall t,
  Safe t ->
  SafeSpawns t.
Proof.
  intros. induction t;
  match goal with
  | H : Safe _ |- _ =>
    induction H; eauto using SafeSpawns
  end.
Qed.

Local Lemma safe_spawns_for_block : forall t t' block,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  SafeSpawns block.
Proof.
  intros. induction_step; inversion_safe_spawns;
  eauto using SafeSpawns, safe_then_safe_spawns.
Qed.

Local Lemma step_safe_spawns_preservation : forall t t' block,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  SafeSpawns t'.
Proof.
  intros. induction_step; inversion_safe_spawns;
  eauto using SafeSpawns, safe_then_safe_spawns.
Qed.

Theorem safe_spawns_preservation : forall m m' ths ths' tid eff,
  memory_property SafeSpawns m ->
  threads_property SafeSpawns ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  (memory_property SafeSpawns m' /\ threads_property SafeSpawns ths').
Proof.
  intros. split; inversion_cstep;
  eauto using mstep_mem_safe_spawns_preservation.
  - eapply property_set; eauto using SafeSpawns.
    eauto using mstep_tm_safe_spawns_preservation. (* performance *)
  - eapply property_add; eauto using SafeSpawns, safe_spawns_for_block.
    eapply property_set; eauto using SafeSpawns, step_safe_spawns_preservation.
Qed.

Lemma safe_for_block : forall t t' block,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  Safe block.
Proof.
  intros. induction_step; inversion_safe_spawns; eauto.
Qed.

Lemma safe_then_not_access : forall m t ad,
  Safe t ->
  ~ access m t ad.
Proof.
  intros * Hsafe. induction t; inversion Hsafe; subst;
  eapply not_access_iff; eauto using not_access.
  eapply not_access_iff.
  intros ?; inversion_access.
Abort.

