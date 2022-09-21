From Coq Require Import Arith.Arith.

From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import WBA.

Lemma deterministic_typing : forall Gamma t T1 T2,
  Gamma |-- t is T1 ->
  Gamma |-- t is T2 ->
  T1 = T2.
Proof.
Admitted.

Ltac apply_deterministic_typing :=
  match goal with
  | H1 : _ |-- ?t is ?T1, H2 : _ |-- ?t is ?T2 |- _ =>
    assert (T1 = T2) by eauto using deterministic_typing; subst
  end.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Inductive well_typed_references (m : mem) : tm -> Prop :=
  | wtr_unit :
    well_typed_references m <{ unit }> 

  | wtr_num : forall n,
    well_typed_references m <{ N n }>

  | wtr_refM : forall T ad,
    empty |-- m[ad] is T ->
    well_typed_references m <{ &ad :: &T }>

  | wtr_refI : forall T ad,
    empty |-- m[ad] is T ->
    well_typed_references m <{ &ad :: i&T }>

  | wtr_new : forall T t,
    well_typed_references m t ->
    well_typed_references m <{ new T t }> 

  | wtr_load : forall t,
    well_typed_references m t ->
    well_typed_references m <{ *t }> 

  | wtr_asg : forall t1 t2,
    well_typed_references m t1 ->
    well_typed_references m t2 ->
    well_typed_references m <{ t1 = t2 }> 

  | wtr_id : forall x,
    well_typed_references m <{ ID x }>

  | wtr_fun : forall x Tx t,
    well_typed_references m t ->
    well_typed_references m <{ fn x Tx --> t }>

  | wtr_call : forall t1 t2,
    well_typed_references m t1 ->
    well_typed_references m t2 ->
    well_typed_references m <{ call t1 t2 }> 

  | wtr_seq : forall t1 t2,
    well_typed_references m t1 ->
    well_typed_references m t2 ->
    well_typed_references m <{ t1; t2 }>
  .

(* TODO talvez separar *)
Definition well_typed_memory (m : mem) := forall ad,
  ad < length m ->
  ((exists T, empty |-- m[ad] is T) /\ well_typed_references m m[ad]).

(*
Lemma wtr_write_value : forall m t t' ad v,
  well_typed_references m t ->
  t --[EF_Write ad v]--> t' ->
  well_typed_references m v.
Proof.
  intros * Hwtr ?. induction_step; inversion_clear Hwbr; eauto.
Qed.
*)

(* ------------------------------------------------------------------------- *)
(* well-typed-references preservation                                        *)
(* ------------------------------------------------------------------------- *)

Local Lemma wtr_subst : forall m x Tx t v,
  well_typed_references m v ->
  well_typed_references m <{ fn x Tx --> t }> ->
  well_typed_references m ([x := v] t).
Proof.
  intros * HwtrV HwtrF.
  assert (HwtrF' : well_typed_references m t) by (inversion HwtrF; trivial).
  clear HwtrF. induction t; simpl; inversion_clear HwtrF';
  try (destruct String.string_dec); eauto using well_typed_references.
Qed.

Local Lemma wtr_mem_add : forall m t v,
  well_behaved_access m t ->
  well_typed_references m t ->
  well_typed_references (m +++ v) t.
Proof.
  intros * ? Hwtr. generalize dependent v.
  induction Hwtr; intros; try (destruct_wba);
  eauto using well_typed_references;
  (eapply wtr_refM || eapply wtr_refI);
  rewrite (get_add_lt TM_Unit); eauto using access.
Qed.

Local Lemma wtr_preservation_none : forall m t t',
  well_typed_references m t ->
  t --[EF_None]--> t' ->
  well_typed_references m t'.
Proof.
  intros * Hwtr ?. induction_step; inversion_clear Hwtr;
  eauto using well_typed_references, wtr_subst.
Qed.

Local Lemma wtr_preservation_alloc: forall m t t' v T,
  empty |-- t is T ->
  well_behaved_access m t ->
  well_typed_references m t ->
  t --[EF_Alloc (length m) v]--> t' ->
  well_typed_references (m +++ v) t'.
Proof.
  intros * ? ? Hwtr ?. generalize dependent T.
  induction_step; intros;
  destruct_wba; inversion_type; inversion_clear Hwtr;
  eauto using well_typed_references, wtr_mem_add;
  (eapply wtr_refM || eapply wtr_refI);
  rewrite (get_add_eq TM_Unit); trivial. 
Qed.

Local Lemma wtr_preservation_read : forall m t t' ad,
  ad < length m ->
  well_typed_references m t ->
  well_typed_memory m ->
  t --[EF_Read ad m[ad]]--> t' ->
  well_typed_references m t'.
Proof.
  intros * Hlen Hwtr Hwtm ?.
  induction_step; inversion_clear Hwtr;
  eauto using well_typed_references.
  match goal with H : well_typed_references _ _ |- _ => inversion H end;
  specialize (Hwtm ad Hlen) as [_ ?]; trivial.
Qed.

Local Lemma wtr_mem_set : forall m t ad v T,
  ad < length m ->
  empty |-- v is T ->
  empty |-- m[ad] is T ->
  well_typed_references m t ->
  well_typed_references m[ad <- v] t.
Proof.
  intros * ? ? ? HwtrT.
  induction HwtrT; eauto using well_typed_references;
  (eapply wtr_refM || eapply wtr_refI);
  match goal with
  |- _ |-- _[?ad'] is _ =>
    decompose sum (lt_eq_lt_dec ad' ad); subst
  end;
  solve [ rewrite (get_set_lt TM_Unit); trivial
        | rewrite (get_set_eq TM_Unit); apply_deterministic_typing; trivial
        | rewrite (get_set_gt TM_Unit); trivial
        ].
Qed.

Local Lemma todo : forall m t t' ad v T V,
  ad < length m ->
  empty |-- t is T ->
  empty |-- v is V ->
  well_typed_references m t ->
  t --[EF_Write ad v]--> t' ->
  empty |-- m[ad] is V.
Proof.
  intros * Hlen HtypeT HtypeV Hwtr ?.
  generalize dependent T.
  induction_step; intros;
  inversion_clear HtypeT; inversion_clear Hwtr; eauto.
  inversion H2; subst;
  inversion H0; subst.
  apply_deterministic_typing.
  eauto using deterministic_typing.
Qed.

Local Lemma well_typed_write_value : forall t t' ad v T,
  empty |-- t is T ->
  t --[EF_Write ad v]--> t' ->
  exists V, empty |-- v is V.
Proof.
  intros * Htype ?. generalize dependent T.
  induction_step; intros; inversion_clear Htype; eauto.
Qed.

Local Lemma wtr_preservation_write : forall m t t' ad v T,
  ad < length m ->
  empty |-- t is T ->
  well_typed_references m t ->
  well_typed_memory m ->
  t --[EF_Write ad v]--> t' ->
  well_typed_references m[ad <- v] t'.
Proof.
  intros * Hlen ? Hwtr Hwtm ?.
  assert (exists V, empty |-- v is V) as [V HtypeV]
    by eauto using well_typed_write_value.
  assert (exists M, empty |-- m[ad] is M) as [M HtypeM]. {
    specialize (Hwtm ad Hlen) as [? _]. trivial.
  }
  generalize dependent T.
  induction_step; intros; inversion_type; inversion_clear Hwtr;
  eauto using well_typed_references, todo, wtr_mem_set.
Qed.

Theorem well_typed_references_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  well_behaved_access m t ->
  well_typed_references m t ->
  well_typed_memory m ->
  m / t ==[eff]==> m' / t' ->
  well_typed_references m' t'.
Proof.
  intros. inversion_mstep;
  eauto using wtr_preservation_none, wtr_preservation_alloc,
    wtr_preservation_read, wtr_preservation_write.
Qed.

