From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Strings.String.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import References.

Local Lemma safe_preserves_inclusion : forall Gamma Gamma',
  Gamma includes Gamma' ->
  (safe Gamma) includes (safe Gamma').
Proof.
  unfold inclusion, safe. intros * H *.
  destruct (Gamma k) eqn:E1; destruct (Gamma' k) eqn:E2;
  solve [ intros F; inversion F
        | eapply H in E2; rewrite E1 in E2; inversion E2; subst; trivial
        ].
Qed.

Local Lemma update_safe_includes_safe_update : forall Gamma k T,
  (safe Gamma)[k <== T] includes (safe Gamma[k <== T]).
Proof.
  intros ? ? ? k' ? H. unfold safe in H. 
  destruct (String.string_dec k k'); subst.
  - rewrite lookup_update_eq in *. destruct T; inversion H; subst; trivial.
  - rewrite lookup_update_neq in *; trivial.
Qed.

Lemma context_weakening : forall Gamma Gamma' t T,
  Gamma' |-- t is T ->
  Gamma includes Gamma' ->
  Gamma  |-- t is T.
Proof.
  intros. generalize dependent Gamma.
  induction_type; intros;
  eauto using well_typed_term, safe_preserves_inclusion,
    MapInclusion.update_inclusion.
Qed.

Lemma context_weakening_empty : forall Gamma t T,
  empty |-- t is T ->
  Gamma |-- t is T.
Proof.
  intros. eapply (context_weakening _ empty); trivial. discriminate.
Qed.

Local Lemma type_preservation_subst : forall t tx T Tx Tx' Gamma x,
  Gamma |-- (TM_Fun x Tx t) is (TY_Fun Tx' T) ->
  empty |-- tx is Tx' ->
  Gamma |-- [x := tx] t is T.
Proof.
  assert (forall t tx T Tx Gamma x,
    Gamma[x <== Tx] |-- t is T ->
    empty |-- tx is Tx ->
    Gamma |-- ([x := tx] t) is T
  ). {
    unfold subst. intros ?.
    induction t; intros * Htype ?; 
    try (destruct String.string_dec); try inversion_type;
    eauto using well_typed_term, context_weakening, context_weakening_empty,
      MapInclusion.update_overwrite, MapInclusion.update_permutation,
      update_safe_includes_safe_update;
    match goal with
    | H : _[_ <== _] _ = _ |- _ =>
      try (erewrite lookup_update_eq in H || erewrite lookup_update_neq in H);
      inversion H; subst;
      eauto using context_weakening_empty, well_typed_term
    end.
  }
  intros * ?. inversion_type. intros. eauto.
Qed.

(* TODO step_type_preservation *)
Theorem step_read_type_preservation : forall m t t' ad T,
  well_typed_references m t ->
  empty |-- t is T ->
  t --[EF_Read ad m[ad]]--> t' ->
  empty |-- t' is T.
Proof.
  intros * Hwtr ? ?.
  remember empty as Gamma. generalize dependent t'.
  induction_type; intros; inversion_subst_clear Hwtr; inversion_step;
  eauto using well_typed_term, type_preservation_subst;
  match goal with
  | Hwtr : well_typed_references _ _ |- _ =>
    inversion_type; inversion_subst_clear Hwtr; trivial
  end;
  eauto using context_weakening_empty.
Qed.

Theorem mstep_type_preservation : forall m m' t t' eff T,
  well_typed_references m t ->
  empty |-- t is T ->
  m / t ==[eff]==> m' / t' ->
  empty |-- t' is T.
Proof.
  intros * Hwtr ? ?. inversion_mstep; generalize dependent t';
  remember empty as Gamma;
  induction_type; intros; inversion_step; inversion_clear Hwtr;
  eauto using well_typed_term, type_preservation_subst;
  inversion_type;
  match goal with
  | H : well_typed_references _ _ |- _ => inversion_clear H
  end;
  eauto using context_weakening_empty.
Qed.

(* ------------------------------------------------------------------------- *)
(* Memory Type Preservation                                                  *)
(* ------------------------------------------------------------------------- *)

(* TODO: clean up *)
Theorem mstep_memory_preservation : forall m m' t t' eff ad T M,
  well_typed_references m t ->
  ad < length m ->
  empty |-- t is T ->
  empty |-- m[ad] is M ->
  m / t ==[eff]==> m' / t' ->
  empty |-- m'[ad] is M.
Proof.
  intros * Hwtr ? HtypeT HtypeM ?. inversion_mstep; eauto;
  try solve [rewrite_array TM_Unit].
  decompose sum (lt_eq_lt_dec ad0 ad); subst; rewrite_array TM_Unit.
  generalize dependent t'. remember empty as Gamma.
  induction HtypeT; inversion HeqGamma; subst; intros;
  inversion_clear Hwtr; inversion_step; eauto.
  do 4 auto_specialize.
  inversion HtypeT1; subst.
  inversion H3; subst.
  apply_deterministic_typing.
  eauto.
Qed.


(*
Ltac solve_with_steps :=
  eexists; eexists; eexists; eauto using step, mstep.

Ltac destruct_IH :=
  match goal with
  | IH : valid_accesses _ _ -> value _ \/ _ |- _ =>
    destruct IH as [? | [[eff [? [? ?]]] | [? [? ?]]]]; trivial
  end.

Ltac solve_mstep_progress :=
  match goal with
  | eff : effect |- _ =>
    try solve [solve_with_steps];
    destruct eff; inversion_mstep; try solve [solve_with_steps]
  end.

Theorem progress : forall m t T,
  valid_accesses m t ->
  empty |-- t is T ->
  (value t
    \/ (exists eff m' t', m / t ==[eff]==> m' / t')
    \/ (exists block t', t --[EF_Spawn block]--> t')).
Proof.
  intros. induction_type; try inversion_va;
  try solve [left; eauto using value]; right;
  try solve [right; eauto using step];
  try solve [left; solve_mstep_progress].
  - destruct_IH.
    + left. solve_with_steps.
    + left. destruct eff; inversion_mstep; solve_with_steps.
    + right. eauto using step.
  - destruct_IH.
    + left. solve_with_steps.
    + left. destruct eff; inversion_mstep; solve_with_steps.
    + right. eauto using step.
  - destruct_IH.
    + left. inversion H1; subst; inversion_type.
      eexists. eexists. eexists. eauto using step, mstep, access.
    + left. destruct eff; inversion_mstep; solve_with_steps.
    + right. eauto using step.
  - destruct_IH.
    + left. inversion H1; subst; inversion_type.
      eexists. eexists. eexists. eauto using step, mstep, access.
    + left. destruct eff; inversion_mstep; solve_with_steps.
    + right. eauto using step.
  - shelve.
  - shelve.
  - shelve.
Qed.
*)

