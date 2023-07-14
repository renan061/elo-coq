From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Strings.String.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import References.

(* ------------------------------------------------------------------------- *)
(* memtyp preservation                                                       *)
(* ------------------------------------------------------------------------- *)

Reserved Notation " m 'extends' m' " (at level 20, no associativity).

(* array extension for memory types *)
Inductive extension : mem -> mem -> Prop :=
  | extension_nil : forall m,
    m extends nil

  | extension_cons : forall m m' v v' Tr,
    m extends m' ->
    ((v, Tr) :: m) extends ((v', Tr) :: m') 

  where " m 'extends' m' " := (extension m m').

Module Extension.
  Ltac nil_false :=
    match goal with
    F : nil extends (_ :: _) |- _ => inversion F
    end.

  Lemma refl : forall m,
    m extends m.
  Proof.
    intros. induction m; eauto using extension.
    match goal with |- (?vTr :: _) extends _ => destruct vTr end.
    eauto using extension.
  Qed.

  Lemma trans : forall m m' m'',
    m  extends m'  ->
    m' extends m'' ->
    m  extends m''.
  Proof.
    intros * Hext ?. generalize dependent m''.
    induction Hext; intros; destruct m''; eauto using extension; try nil_false.
    match goal with
    | H : (_ :: _) extends (_ :: _) |- _ => inversion H; subst
    end.
    eauto using extension.
  Qed.

  Lemma add : forall m vTr,
    (m +++ vTr) extends m.
  Proof.
    intros. induction m; unfold add; eauto using extension. simpl in *.
    match goal with |- (?vTr :: _) extends _ => destruct vTr end.
    eauto using extension.
  Qed.

  Lemma get : forall m m' ad,
    ad < #m' ->
    m extends m' ->
    m[ad].typ = m'[ad].typ.
  Proof.
    intros * Hlen Hext. generalize dependent ad. generalize dependent m.
    induction m'; intros; try solve [inversion Hlen].
    destruct m; try nil_false. inversion_subst_clear Hext.
    destruct ad; simpl; eauto using lt_S_n.
  Qed.

  Lemma set : forall m ad v Tr,
    m[ad].typ = Tr -> 
    m[ad <- (v, Tr)] extends m.
  Proof.
    intros * Heq. generalize dependent ad. induction m; intros; simpl in *;
    eauto using extension. simpl in *. destruct ad;
    match goal with |- _ extends (?vTr :: _) => destruct vTr end;
    simpl in *; subst; eauto using refl, extension.
  Qed.
End Extension.

Local Lemma mstep_memtyp_preservation : forall m m' t t' eff,
  well_typed_references m t ->
  m / t ==[eff]==> m' / t' ->
  m' extends m.
Proof.
  intros. inversion_clear_mstep; eauto using Extension.refl, Extension.add.
  eapply Extension.set. induction_step; intros; inversion_wtr; eauto.
  inversion_wtr; eauto.
Qed.

Corollary cstep_memtyp_preservation : forall m m' ths ths' tid eff,
  forall_threads ths (well_typed_references m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  m' extends m.
Proof.
  intros. inversion_cstep;
  eauto using Extension.refl, mstep_memtyp_preservation.
Qed.

(* TODO *)
Corollary cstep_memtyp : forall m m' ths ths' tid eff ad,
  forall_threads ths (well_typed_references m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  ad < #m ->
  m'[ad].typ = m[ad].typ.
Proof.
  intros. assert (m' extends m) by eauto using cstep_memtyp_preservation.
  eapply Extension.get; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

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

Local Lemma context_weakening : forall Gamma Gamma' t T,
  Gamma' |-- t is T ->
  Gamma includes Gamma' ->
  Gamma  |-- t is T.
Proof.
  intros. generalize dependent Gamma.
  induction_type; intros;
  eauto using well_typed_term, safe_preserves_inclusion,
    MapInclusion.update_inclusion.
Qed.

Local Lemma context_weakening_empty : forall Gamma t T,
  empty |-- t is T ->
  Gamma |-- t is T.
Proof.
  intros. eapply (context_weakening _ empty); trivial. discriminate.
Qed.

Local Lemma subst_type_preservation : forall t tx T Tx Tx' Gamma x,
  Gamma |-- <{ fn x Tx t }> is <{{  Tx' --> T }}> ->
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

(* ------------------------------------------------------------------------- *)
(* term preservation                                                         *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_read_type_preservation : forall m t t' ad T,
  well_typed_references m t ->
  empty |-- t is T ->
  t --[EF_Read ad m[ad].tm]--> t' ->
  empty |-- t' is T.
Proof.
  intros. remember empty as Gamma. generalize dependent t'.
  induction_type; intros; inversion_wtr; inversion_step;
  eauto using well_typed_term, subst_type_preservation;
  inversion_type; inversion_wtr; trivial;
  eauto using context_weakening_empty.
Qed.

Local Lemma mstep_type_preservation : forall m m' t t' eff T,
  well_typed_references m t ->
  empty |-- t is T ->
  m / t ==[eff]==> m' / t' ->
  empty |-- t' is T.
Proof.
  intros. inversion_clear_mstep; generalize dependent t';
  remember empty as Gamma;
  induction_type; intros; inversion_step; inversion_wtr;
  eauto using well_typed_term, subst_type_preservation;
  inversion_type; inversion_wtr;
  eauto using context_weakening_empty.
Qed.

(* ------------------------------------------------------------------------- *)
(* memory preservation                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma mstep_mem_type_preservation : forall m m' t t' eff ad T M,
  well_typed_references m t ->
  ad < length m ->
  empty |-- t is T ->
  empty |-- m[ad].tm is M ->
  m / t ==[eff]==> m' / t' ->
  empty |-- m'[ad].tm is M.
Proof.
  intros * ? ? Htype ? ?. rename ad into ad'.
  inversion_clear_mstep; try simpl_array; trivial.
  decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array; trivial.
  generalize dependent t'. remember empty as Gamma.
  induction Htype; inversion HeqGamma; subst; intros;
  inversion_wtr; inversion_step; eauto.
  inversion_type; inversion_wtr; apply_deterministic_typing. eauto.
Qed.

(* TODO *)
(* did not prove preservation *)






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

