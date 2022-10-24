From Coq Require Logic.ClassicalFacts.
From Coq Require Import Arith.Arith.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import Soundness.

(* ------------------------------------------------------------------------- *)
(* NotMut                                                                    *)
(* ------------------------------------------------------------------------- *)

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

Local Ltac inversion_nomut := inversion_over_term_predicate NoMut.

(* ------------------------------------------------------------------------- *)
(* SafeSpawns                                                                *)
(* ------------------------------------------------------------------------- *)

(* A term has safe spawns if all of its spawns have no mutable references. *)
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

Local Ltac inversion_safe_spawns := inversion_over_term_predicate SafeSpawns.

(* ------------------------------------------------------------------------- *)
(* HasVar                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive HasVar (x : id) : tm  -> Prop :=
  | has_var_new : forall T t,
      HasVar x t ->
      HasVar x <{ new T t }>

  | has_var_load : forall t,
      HasVar x t ->
      HasVar x <{ *t }>

  | has_var_asg1 : forall t1 t2,
      HasVar x t1 ->
      HasVar x <{ t1 = t2 }>

  | has_var_asg2 : forall t1 t2,
      HasVar x t2 ->
      HasVar x <{ t1 = t2 }>

  | has_var_id :
      HasVar x <{ ID x }>

  | has_var_fun : forall x' Tx t,
      x <> x' ->
      HasVar x t ->
      HasVar x <{ fn x' Tx --> t }>

  | has_var_call1 : forall t1 t2,
      HasVar x t1 ->
      HasVar x <{ call t1 t2 }>

  | has_var_call2 : forall t1 t2,
      HasVar x t2 ->
      HasVar x <{ call t1 t2 }>

  | has_var_seq1 : forall t1 t2,
      HasVar x t1 ->
      HasVar x <{ t1; t2 }>

  | has_var_seq2 : forall t1 t2,
      HasVar x t2 ->
      HasVar x <{ t1; t2 }>

  | has_var_spawn : forall t,
      HasVar x t ->
      HasVar x <{ spawn t }>
  .

Inductive NotHasVar (x : id) : tm  -> Prop :=
  | not_has_var_unit :
      NotHasVar x <{ unit }>

  | not_has_var_num : forall n,
      NotHasVar x <{ N n }>

  | not_has_var_ref : forall ad T,
      NotHasVar x <{ &ad :: T }>

  | not_has_var_new : forall T t,
      ~ (HasVar x t) ->
      NotHasVar x <{ new T t }>

  | not_has_var_load : forall t,
      ~ (HasVar x t) ->
      NotHasVar x <{ *t }>

  | not_has_var_asg : forall t1 t2,
      ~ (HasVar x t1) ->
      ~ (HasVar x t2) ->
      NotHasVar x <{ t1 = t2 }>

  | not_has_var_id : forall x',
      x <> x' ->
      NotHasVar x <{ ID x' }>

  | not_has_var_fun1 : forall x' Tx t,
      x <> x' ->
      ~ (HasVar x t) ->
      NotHasVar x <{ fn x' Tx --> t }>

  | not_has_var_fun2 : forall Tx t,
      NotHasVar x <{ fn x Tx --> t }>

  | not_has_var_call : forall t1 t2,
      ~ (HasVar x t1) ->
      ~ (HasVar x t2) ->
      NotHasVar x <{ call t1 t2 }>

  | not_has_var_seq : forall t1 t2,
      ~ (HasVar x t1) ->
      ~ (HasVar x t2) ->
      NotHasVar x <{ t1; t2 }>

  | not_has_var_spawn : forall t,
      ~ (HasVar x t) ->
      NotHasVar x <{ spawn t }>
  .

Lemma hasvar_dec : forall x t,
  (HasVar x t) \/ (~ HasVar x t).
Proof. eauto using excluded_middle. Qed.

Local Ltac inversion_has_var x :=
  inversion_over_term_predicate (HasVar x).

Local Ltac inversion_not_has_var x :=
  inversion_over_term_predicate (NotHasVar x).

(* TODO: make it pretty *)
Local Ltac solve_stuff :=
  match goal with
  | |- ~ (HasVar _ ?t) => intros F; induction t; eauto using HasVar
  end.

(* TODO: make it pretty *)
Theorem not_hasvar_iff : forall x t,
  ~ (HasVar x t) <-> NotHasVar x t.
Proof.
  intros. split; intros H; destruct t;
  eauto using HasVar, NotHasVar;
  try solve [intros F; inversion_clear F;
             inversion_not_has_var x; contradiction];
  try (eapply not_has_var_ref
    || eapply not_has_var_asg
    || eapply not_has_var_call
    || eapply not_has_var_seq);
  eauto using HasVar, NotHasVar.
  - destruct (String.string_dec x i); subst.
    + contradict H. eauto using HasVar.
    + eauto using NotHasVar.
  - destruct (String.string_dec x i); subst.
    + eapply not_has_var_fun2.
    + eapply not_has_var_fun1; eauto. solve_stuff.
  - intros F. inversion F; subst. inversion H. contradiction.
Qed.

(* TODO: make it pretty *)
Local Lemma hasvar_subst : forall x t tx,
  ~ (HasVar x t) -> ([x := tx] t) = t.
Proof.
  intros * H. eapply not_hasvar_iff in H.
  induction t; simpl; trivial; inversion_not_has_var x;
  try solve
    [ rewrite IHt; trivial; eapply not_hasvar_iff; trivial
    | rewrite IHt1; trivial; try (rewrite IHt2); trivial;
      do 2 (eapply not_hasvar_iff; trivial)
    ];
  destruct String.string_dec; subst; trivial; try contradiction.
  rewrite IHt; trivial. eapply not_hasvar_iff; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* Equivalence                                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma equivalence_safe : forall Gamma1 Gamma2,
  Gamma1 === Gamma2 ->
  safe Gamma1 === safe Gamma2.
Proof.
  unfold map_equivalence, safe. intros * Heq k.
  specialize (Heq k). rewrite Heq. trivial.
Qed.

Local Lemma equivalence_typing : forall Gamma1 Gamma2 t T,
  Gamma1 === Gamma2 ->
  Gamma1 |-- t is T ->
  Gamma2 |-- t is T.
Proof.
  intros. generalize dependent Gamma2. induction_type; intros;
  eauto using well_typed_term, equivalence_safe,
    MapEquivalence.lookup, MapEquivalence.update_equivalence.
Qed.

Local Lemma safe_gamma_only_has_immutables : forall Gamma,
  (Gamma === safe Gamma) <->
  (forall x T, Gamma x = Some T -> (exists T', T = TY_Immut T')).
Proof.
  unfold safe, map_equivalence. split.
  - intros H1 ? ? H2. specialize (H1 x). rewrite H2 in H1.
    destruct T; eauto; inversion H1.
  - intros H1 ?. specialize (H1 k). destruct (Gamma k); trivial.
    specialize (H1 _ eq_refl) as [? ?]; subst. trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* Inclusion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Lemma inclusion_safe : forall Gamma Gamma',
  Gamma includes Gamma' ->
  (safe Gamma) includes (safe Gamma').
Proof.
  unfold inclusion, safe. intros * H *.
  destruct (Gamma k) eqn:E1; destruct (Gamma' k) eqn:E2;
  solve [ intros F; inversion F
        | eapply H in E2; rewrite E1 in E2; inversion_clear E2; trivial
        ].
Qed.

Local Lemma inclusion_typing : forall Gamma Gamma' t T,
  Gamma includes Gamma' ->
  Gamma' |-- t is T ->
  Gamma  |-- t is T.
Proof.
  intros. generalize dependent Gamma. induction_type; intros;
  try inversion_type; eauto using well_typed_term, inclusion_safe,
    MapInclusion.update_inclusion.
Qed.

Local Lemma gamma_includes_safe_gamma : forall Gamma,
  Gamma includes (safe Gamma).
Proof.
  unfold safe, inclusion. intros ? ? ? H.
  destruct (Gamma k) as [T' | _]; subst; try solve [inversion H].
  destruct T'; subst; inversion H; subst. trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODOs                                                                     *)
(* ------------------------------------------------------------------------- *)

Local Lemma well_typed_gamma_from_safe_gamma : forall Gamma t T,
  safe Gamma |-- t is T ->
  Gamma |-- t is T.
Proof.
  intros. eauto using inclusion_typing, gamma_includes_safe_gamma.
Qed.

Local Lemma safe_gamma_includes_update : forall Gamma x T,
 (safe Gamma)[x <== T] includes (safe Gamma[x <== T]).
Proof.
  unfold inclusion. intros * H.
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

Local Lemma todo11 : forall k T,
  empty === (safe empty[k <== <{{ & T }}>]).
Proof.
  unfold map_equivalence, safe. intros ? ? k'.
  destruct (String.string_dec k k'); subst;
  try (rewrite lookup_update_eq || rewrite lookup_update_neq); eauto.
Qed.

Local Lemma todo12 : forall Gamma k T,
  (safe Gamma) includes (safe Gamma[k <== <{{ & T }}>]).
Proof.
  unfold inclusion, safe. intros ? ? ? k' v.
  destruct (String.string_dec k k'); subst.
  - rewrite lookup_update_eq. discriminate.
  - rewrite lookup_update_neq; trivial.
Qed.

Local Lemma todo13 : forall x T,
  (safe empty[x <== TY_Immut T]) === empty[x <== TY_Immut T].
Proof.
  unfold map_equivalence, safe. intros. destruct (String.string_dec x k); subst;
  try (rewrite lookup_update_eq || rewrite lookup_update_neq); trivial.
Qed.

Local Lemma todo14 : forall Gamma x T,
  (safe Gamma)[x <== TY_Immut T] === (safe Gamma[x <== TY_Immut T]).
Proof.
  unfold map_equivalence, safe. intros. destruct (String.string_dec x k); subst.
  - do 2 (rewrite lookup_update_eq). trivial.
  - do 2 (rewrite lookup_update_neq; trivial).
Qed.

Local Lemma todo1 : forall x t v T Tx,
  (* precisa de algo do tipo (exists T, Tx = TY_Immut T) *)
  value v ->
  SafeSpawns v ->
  SafeSpawns t ->
  empty |-- v is Tx ->
  empty[x <== Tx] |-- t is T ->
  NoMut ([x := v] t).
Proof.
Abort.

Local Lemma todo2 : forall Gamma t v x T Tx,
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
    eauto 6 using equivalence_typing, MapEquivalence.update_permutation.
  - simpl. inversion_type. eapply T_Spawn.
    assert (Hx : (safe Gamma)[x <== Tx] |-- t is T0) by
      eauto using inclusion_typing, safe_gamma_includes_update.
    destruct Tx.
    + specialize (IHt T0 (safe Gamma) Hx).
      eapply equivalence_typing; eauto using todo14.
    + specialize (IHt T0).
      eapply equivalence_typing in H3.
Abort.

(* ------------------------------------------------------------------------- *)
(* SafeSpawns mstep preservation                                             *)
(* ------------------------------------------------------------------------- *)

Local Lemma safe_spawns_subst : forall Gamma x t v T Tx,
  value v ->
  empty |-- v is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  SafeSpawns v ->
  SafeSpawns t ->
  SafeSpawns ([x := v] t).
Proof.
  intros * Hvalue HtypeV HtypeT Hssv Hsst.
  generalize dependent Gamma. generalize dependent T. generalize dependent Tx. 
  induction Hsst; intros; inversion_type;
  simpl; try (destruct String.string_dec);
  eauto using SafeSpawns, equivalence_typing, MapEquivalence.update_permutation.
  eapply safe_spawns_spawn.
  destruct (hasvar_dec x t).
  - eapply nomut_subst; trivial.
    inversion Hvalue; subst; eauto using NoMut.
    + inversion HtypeV; subst; eauto using NoMut.
      (* H2 não vai tipar por conta de H0. contradiction! *)
      admit.
    + inversion Hvalue; subst; inversion HtypeV; subst.
      (* H2 não vai tipar por conta de H0. contradiction! *)
      admit.
  - erewrite hasvar_subst; eauto.
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
  do 2 inversion_safe_spawns. do 2 inversion_type.
  eauto using safe_spawns_subst.
Qed.

(* ------------------------------------------------------------------------- *)
(* Memory SafeSpawns mstep preservation                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma mem_safe_spawns_alloc : forall m t t' v,
  memory_property SafeSpawns m ->
  SafeSpawns t ->
  t --[EF_Alloc (length m) v]--> t' ->
  memory_property SafeSpawns (m +++ v).
Proof.
  intros. assert (SafeSpawns v).
  { induction_step; inversion_safe_spawns; eauto. }
  unfold memory_property. eauto using property_add, SafeSpawns.
Qed.

Local Lemma mem_safe_spawns_store : forall m t t' ad v,
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
  intros. inversion_mstep;
  eauto using mem_safe_spawns_alloc, mem_safe_spawns_store.
Qed.

(* ------------------------------------------------------------------------- *)
(* SafeSpawns cstep preservation                                             *)
(* ------------------------------------------------------------------------- *)

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

