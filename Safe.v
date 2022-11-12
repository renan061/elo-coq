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

  | nomut_var : forall x,
    NoMut <{ var x }>

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

Ltac inversion_nomut :=
  inversion_term_predicate NoMut.

Ltac inversion_clear_nomut :=
  inversion_clear_term_predicate NoMut.

Local Lemma nomut_subst : forall x t t',
  NoMut t ->
  NoMut t' ->
  NoMut ([x := t'] t).
Proof.
  intros. induction t; intros;
  inversion_nomut; eauto using NoMut;
  simpl; destruct String.string_dec; subst; eauto using NoMut. 
Qed.

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

  | safe_spawns_var : forall x,
      SafeSpawns <{ var x }>

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

Ltac inversion_safe_spawns :=
  inversion_term_predicate SafeSpawns.

Ltac inversion_clear_safe_spawns :=
  inversion_clear_term_predicate SafeSpawns.

(* ------------------------------------------------------------------------- *)
(* HasVar                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive HasVar (x : id) : tm  -> Prop :=
  | hasvar_new : forall T t,
      HasVar x t ->
      HasVar x <{ new T t }>

  | hasvar_load : forall t,
      HasVar x t ->
      HasVar x <{ *t }>

  | hasvar_asg1 : forall t1 t2,
      HasVar x t1 ->
      HasVar x <{ t1 = t2 }>

  | hasvar_asg2 : forall t1 t2,
      HasVar x t2 ->
      HasVar x <{ t1 = t2 }>

  | hasvar_var :
      HasVar x <{ var x }>

  | hasvar_fun : forall x' Tx t,
      x <> x' ->
      HasVar x t ->
      HasVar x <{ fn x' Tx --> t }>

  | hasvar_call1 : forall t1 t2,
      HasVar x t1 ->
      HasVar x <{ call t1 t2 }>

  | hasvar_call2 : forall t1 t2,
      HasVar x t2 ->
      HasVar x <{ call t1 t2 }>

  | hasvar_seq1 : forall t1 t2,
      HasVar x t1 ->
      HasVar x <{ t1; t2 }>

  | hasvar_seq2 : forall t1 t2,
      HasVar x t2 ->
      HasVar x <{ t1; t2 }>

  | hasvar_spawn : forall t,
      HasVar x t ->
      HasVar x <{ spawn t }>
  .

Ltac inversion_hasvar x :=
  inversion_term_predicate (HasVar x).

Ltac inversion_clear_hasvar x :=
  inversion_clear_term_predicate (HasVar x).

Lemma hasvar_dec : forall x t,
  decidable (HasVar x t).
Proof.
  unfold decidable. intros. induction t;
  try (destruct IHt); try (destruct IHt1); try (destruct IHt2);
  try match goal with
    | x : id, x' : id |- _ =>
      destruct (String.string_dec x x'); subst
  end;
  solve
    [ left; eauto using HasVar
    | right; intros F; inversion_subst_clear F; eauto; contradiction
    ].
Qed.

Local Ltac solve_not_hasvar :=
  intros; match goal with
  | |- (~ HasVar _ ?t) => induction t; eauto using HasVar
  end.

Lemma not_hv_new : forall x t T,
  ~ HasVar x <{ new T t }> -> ~ HasVar x t.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_load : forall x t,
  ~ HasVar x <{ *t }> -> ~ HasVar x t.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_asg1 : forall x t1 t2,
  ~ HasVar x <{ t1 = t2 }> -> ~ HasVar x t1.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_asg2 : forall x t1 t2,
  ~ HasVar x <{ t1 = t2 }> -> ~ HasVar x t2.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_fun : forall x x' t Tx,
  x <> x' -> ~ HasVar x <{ fn x' Tx --> t }> -> ~ HasVar x t.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_call1 : forall x t1 t2,
  ~ HasVar x <{ call t1 t2 }> -> ~ HasVar x t1.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_call2 : forall x t1 t2,
  ~ HasVar x <{ call t1 t2 }> -> ~ HasVar x t2.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_seq1 : forall x t1 t2,
  ~ HasVar x <{ t1; t2 }> -> ~ HasVar x t1.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_seq2 : forall x t1 t2,
  ~ HasVar x <{ t1; t2 }> -> ~ HasVar x t2.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_spawn : forall x t,
  ~ HasVar x <{ spawn t }> -> ~ HasVar x t.
Proof. solve_not_hasvar. Qed.

Lemma hasvar_subst : forall x t tx,
  ~ (HasVar x t) -> ([x := tx] t) = t.
Proof.
  intros. induction t; simpl; trivial;
  try (destruct String.string_dec; subst; trivial);
  try solve
    [ rewrite IHt; eauto using not_hv_new, not_hv_load, not_hv_spawn, not_hv_fun
    | rewrite IHt1; eauto using not_hv_asg1, not_hv_call1, not_hv_seq1;
      rewrite IHt2; eauto using not_hv_asg2, not_hv_call2, not_hv_seq2
    ].
  exfalso. eauto using HasVar.
Qed.

Lemma hasvar_typing : forall Gamma x t T,
  HasVar x t ->
  Gamma x = None ->
  ~ (Gamma |-- t is T).
Proof.
  assert (forall Gamma x, Gamma x = None -> (safe Gamma) x = None).
  { unfold safe. intros * H. rewrite H. reflexivity. }
  intros * ? HGamma F. induction_type; inversion_hasvar x; eauto.
  - rewrite HGamma in *. discriminate.
  - rewrite lookup_update_neq in IHF; eauto.
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
  assert (H1 : forall Gamma x T,
    (safe Gamma[x <== <{{ &T }}>]) x = None);
  assert (H2 : forall Gamma x T T',
    (safe Gamma[x <== <{{ T --> T' }}>]) x = None);
  try solve [unfold safe; intros; rewrite lookup_update_eq; reflexivity].
  (* main proof *)
  intros * Hvalue HtypeV HtypeT Hssv Hsst.
  generalize dependent Gamma. generalize dependent T. generalize dependent Tx.
  induction Hsst; intros; inversion_type;
  simpl; try (destruct String.string_dec);
  eauto using SafeSpawns, equivalence_typing, MapEquivalence.update_permutation.
  eapply safe_spawns_spawn. destruct (hasvar_dec x t).
  - eapply nomut_subst; trivial.
    inversion Hvalue; subst; eauto using NoMut.
    + inversion HtypeV; subst; eauto using NoMut.
      exfalso. eapply hasvar_typing; eauto using H1.
    + inversion_clear Hvalue. inversion HtypeV; subst.
      exfalso. eapply hasvar_typing; eauto using H2. 
  - erewrite hasvar_subst; eauto.
Qed.

Local Lemma mstep_tm_safe_spawns_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  forall_memory m SafeSpawns ->
  SafeSpawns t ->
  m / t ==[eff]==> m' / t' ->
  SafeSpawns t'.
Proof.
  intros. generalize dependent T.
  inversion_mstep; induction_step; intros;
  try solve [inversion_type; inversion_safe_spawns; eauto using SafeSpawns].
  do 2 (inversion_safe_spawns; inversion_type).
  eauto using safe_spawns_subst.
Qed.

Local Lemma mem_safe_spawns_alloc : forall m t t' v,
  forall_memory m SafeSpawns ->
  SafeSpawns t ->
  t --[EF_Alloc (length m) v]--> t' ->
  forall_memory (m +++ v) SafeSpawns.
Proof.
  intros. assert (SafeSpawns v).
  { induction_step; inversion_safe_spawns; eauto. }
  unfold forall_memory. eauto using property_add, SafeSpawns.
Qed.

Local Lemma mem_safe_spawns_store : forall m t t' ad v,
  forall_memory m SafeSpawns ->
  SafeSpawns t ->
  t --[EF_Write ad v]--> t' ->
  forall_memory m[ad <- v] SafeSpawns.
Proof.
  intros. assert (SafeSpawns v).
  { induction_step; inversion_safe_spawns; eauto. }
  unfold forall_memory. eauto using property_set, SafeSpawns.
Qed.

Local Lemma mstep_mem_safe_spawns_preservation : forall (m m' : mem) t t' eff,
  forall_memory m SafeSpawns ->
  SafeSpawns t ->
  m / t ==[eff]==> m' / t' ->
  forall_memory m' SafeSpawns.
Proof.
  intros. inversion_mstep;
  eauto using mem_safe_spawns_alloc, mem_safe_spawns_store.
Qed.

(* ------------------------------------------------------------------------- *)
(* SafeSpawns cstep preservation                                             *)
(* ------------------------------------------------------------------------- *)

Local Lemma nomut_then_safe_spawns : forall t,
  NoMut t ->
  SafeSpawns t.
Proof.
  intros * H. induction t; induction H; eauto using SafeSpawns.
Qed.

Local Lemma safe_spawns_for_block : forall t t' block,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  SafeSpawns block.
Proof.
  intros. induction_step; inversion_safe_spawns;
  eauto using SafeSpawns, nomut_then_safe_spawns.
Qed.

Local Lemma step_safe_spawns_preservation : forall t t' block,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  SafeSpawns t'.
Proof.
  intros. induction_step; inversion_safe_spawns;
  eauto using SafeSpawns, nomut_then_safe_spawns.
Qed.

Theorem safe_spawns_preservation : forall m m' ths ths' tid eff,
  forall_threads ths WellTypedThread ->
  forall_memory m SafeSpawns ->
  forall_threads ths SafeSpawns ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  (forall_memory m' SafeSpawns /\ forall_threads ths' SafeSpawns).
Proof.
  intros * H; intros. split; inversion_cstep;
  eauto using mstep_mem_safe_spawns_preservation.
  - eapply property_set; eauto using SafeSpawns. specialize (H tid) as [? ?].
    eauto using mstep_tm_safe_spawns_preservation. (* performance *)
  - eapply property_add; eauto using SafeSpawns, safe_spawns_for_block.
    eapply property_set; eauto using SafeSpawns, step_safe_spawns_preservation.
Qed.

Lemma safe_for_block : forall t t' block,
  SafeSpawns t ->
  t --[EF_Spawn block]--> t' ->
  NoMut block.
Proof.
  intros. induction_step; inversion_safe_spawns; eauto.
Qed.

