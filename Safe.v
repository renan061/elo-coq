From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import Soundness.

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

Local Ltac inversion_nomut :=
  match goal with
  | H : NoMut TM_Unit   |- _ => inversion H; subst; clear H
  | H : NoMut (_ _)     |- _ => inversion H; subst; clear H
  | H : NoMut (_ _ _)   |- _ => inversion H; subst; clear H
  | H : NoMut (_ _ _ _) |- _ => inversion H; subst; clear H
  end.

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

(* A term has safe substitutions if... *)
Inductive SafeSubsts : tm -> Prop :=
  | safe_substs_unit :
      SafeSubsts <{ unit }>

  | safe_substs_num : forall n,
      SafeSubsts <{ N n }>

  | safe_substs_ref : forall ad T,
      SafeSubsts <{ &ad :: T }>

  | safe_substs_new : forall T t,
      SafeSubsts t ->
      SafeSubsts <{ new T t }>

  | safe_substs_load : forall t,
      SafeSubsts t ->
      SafeSubsts <{ *t }>

  | safe_substs_asg : forall t1 t2,
      SafeSubsts t1 ->
      SafeSubsts t2 ->
      SafeSubsts <{ t1 = t2 }>

  | safe_substs_id : forall x,
      SafeSubsts <{ ID x }>

  | safe_substs_fun : forall x Tx t,
      SafeSubsts t ->
      SafeSubsts <{ fn x Tx --> t }>

  | safe_substs_call : forall t1 t2 T,
      empty |-- t2 is (TY_Immut T) ->
      SafeSubsts t1 ->
      SafeSubsts t2 ->
      SafeSubsts <{ call t1 t2 }>

  | safe_substs_seq : forall t1 t2,
      SafeSubsts t1 ->
      SafeSubsts t2 ->
      SafeSubsts <{ t1; t2 }>

  | safe_substs_spawn : forall t,
      SafeSubsts t ->
      SafeSubsts <{ spawn t }>
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

Lemma safe_preserves_inclusion : forall Gamma Gamma',
  Gamma includes Gamma' ->
  (safe Gamma) includes (safe Gamma').
Proof.
  unfold includes', safe. intros * H *.
  destruct (Gamma k) eqn:E1; destruct (Gamma' k) eqn:E2;
  solve [ intros F; inversion F
        | eapply H in E2; rewrite E1 in E2; inversion E2; subst; trivial
        ].
Qed.

Local Lemma includes_wtt : forall Gamma1 Gamma2 t T,
  Gamma1 includes Gamma2 ->
  Gamma2 |-- t is T ->
  Gamma1 |-- t is T.
Proof.
  intros * Hinc Htype. generalize dependent Gamma1.
  induction Htype; intros;
  try inversion_type; eauto using well_typed_term, inclusion_update,
    safe_preserves_inclusion.
Qed.

Local Lemma gamma_includes_safe_gamma : forall Gamma,
  Gamma includes (safe Gamma).
Proof.
  unfold safe, includes'. intros ? ? ? H.
  destruct (Gamma k) as [T' | _]; subst; try solve [inversion H].
  destruct T'; subst; inversion H; subst. trivial.
Qed.

Lemma well_typed_gamma_from_safe_gamma : forall Gamma t T,
  safe Gamma |-- t is T ->
  Gamma |-- t is T.
Proof.
  intros. eauto using includes_wtt, gamma_includes_safe_gamma.
Qed.

(* unused *)
Local Lemma safe_gamma_includes_update : forall Gamma x T,
 (safe Gamma)[x <== T] includes (safe Gamma[x <== T]).
Proof.
  unfold includes'. intros * H.
  destruct (String.string_dec x k); subst; unfold safe in H.
  - rewrite lookup_update_eq in *.
    destruct T; subst; trivial;
    inversion H; subst.
  - rewrite lookup_update_neq in *; trivial.
Qed.

Local Lemma nomut_subst : forall x t t',
  NoMut t ->
  NoMut t' ->
  NoMut ([x := t'] t).
Proof.
  intros * ? ?. induction t; intros; simpl;
  inversion_nomut; try (destruct String.string_dec); subst; eauto using NoMut.
Qed.

Local Lemma todo3 : forall k T,
  equivalent empty (safe empty [k <== <{{ & T }}>]).
Proof.
  unfold equivalent, safe. intros ? ? k'.
  destruct (String.string_dec k k'); subst;
  try (rewrite lookup_update_eq || rewrite lookup_update_neq); eauto.
Qed.

Local Lemma todo4 : forall Gamma k T,
  (safe Gamma) includes (safe Gamma [k <== <{{ & T }}>]).
Proof.
  unfold includes', safe. intros ? ? ? k' v.
  destruct (String.string_dec k k'); subst.
  - rewrite lookup_update_eq. discriminate.
  - rewrite lookup_update_neq; trivial.
Qed.

Local Lemma todo11 : forall Gamma k T,
  (safe Gamma) includes (safe Gamma[k <== <{{ & T }}>]).
Proof.
Admitted.

Local Lemma todo13 : forall x T,
  equivalent (safe empty[x <== TY_Immut T]) empty[x <== TY_Immut T].
Proof.
  unfold equivalent, safe. intros. destruct (String.string_dec x k); subst;
  try (rewrite lookup_update_eq || rewrite lookup_update_neq); trivial.
Qed.

Local Lemma todo12 : forall Gamma x T,
  equivalent (safe Gamma)[x <== TY_Immut T] (safe Gamma[x <== TY_Immut T]).
Proof.
  unfold equivalent, safe. intros. destruct (String.string_dec x k); subst.
  - do 2 (rewrite lookup_update_eq). trivial.
  - do 2 (rewrite lookup_update_neq; trivial).
Qed.

Local Lemma todo2 : forall Gamma2 x t v T Tx,
  value v ->
  SafeSpawns v ->
  Gamma2 |-- v is Tx ->
  safe empty[x <== Tx] |-- t is T ->
  (* precisa de algo do tipo (exists T, Tx = TY_Immut T) *)
  NoMut t ->
  NoMut ([x := v] t).
Proof.
  intros * Hvalue ? HtypeV ? Hnomut.
  generalize dependent T. generalize dependent Tx.
  induction Hnomut; intros; simpl;
  inversion_type; subst;
  eauto using NoMut.
  - destruct String.string_dec; subst; eauto using NoMut.
    unfold safe in *.
    rewrite lookup_update_eq in H3. destruct Tx; inversion H3; subst.
    destruct Hvalue; inversion_type; eauto using NoMut.
  - destruct String.string_dec; subst; eauto using NoMut.
    eapply nomut_fun.
    eapply IHHnomut; clear IHHnomut;
    eauto.
Abort.

Local Lemma todododo : forall Gamma t v x T Tx,
  empty |-- v is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  Gamma[x <== Tx] |-- ([x := v] t) is T.
Proof.
  intros * H1 H2. generalize dependent Gamma. generalize dependent T.
  induction t; intros;
  try solve [inversion_type; eauto using well_typed_term].
  - simpl. destruct String.string_dec; subst; trivial.
    inversion_type.
    rewrite lookup_update_eq in H3. inversion H3; subst.
    eauto using context_weakening_empty.
  - simpl. destruct String.string_dec; subst; trivial.
    inversion_type.
    eapply T_Fun.
    eauto 6 using equivalent_wtt, equivalent_update_permutation.
  - simpl. inversion_type. eapply T_Spawn.
    assert (Hx : (safe Gamma)[x <== Tx] |-- t is T0) by
      eauto using includes_wtt, safe_gamma_includes_update.
    destruct Tx.
    + specialize (IHt T0 (safe Gamma) Hx).
      eapply equivalent_wtt; eauto using todo12.
    + specialize (IHt T0).
      eapply includes_wtt in H3; eauto using todo11.


Qed.

Local Lemma safe_spawns_subst : forall Gamma1 Gamma2 x t v T Tx,
  value v ->
  Gamma1[x <== Tx] |-- t is T ->
  Gamma2|-- v is Tx ->
  SafeSpawns t ->
  SafeSpawns v ->
  SafeSpawns ([x := v] t).
Proof.
  intros * Hvalue HtypeT HtypeV Hsst Hssv.
  generalize dependent Gamma1. generalize dependent T. generalize dependent Tx. 
  induction Hsst; intros; inversion_type;
  simpl; try (destruct String.string_dec);
  eauto using SafeSpawns, equivalent_wtt, equivalent_update_permutation.
  eapply safe_spawns_spawn.
  eapply nomut_subst; trivial.
  inversion Hvalue; subst; eauto using NoMut.
  - inversion HtypeV; subst; eauto using NoMut.
  - inversion Hvalue; subst; inversion HtypeV; subst. admit.
  - admit.
Abort.

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

Local Lemma mstep_tm_safe_spawns_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  memory_property SafeSpawns m ->
  SafeSpawns t ->
  m / t ==[eff]==> m' / t' ->
  SafeSpawns t'.
Proof.
  intros. generalize dependent T.
  inversion_mstep; induction_step; intros;
  try solve [inversion_type; inversion_safe_spawns; eauto using SafeSpawns].
  inversion_safe_spawns.
  inversion_safe_spawns.
  inversion_type.
  inversion_type.
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

