From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.

(* The types of all addresses inside the term correspond with the types in the
memory. *)
Inductive well_typed_references (m : mem) : tm -> Prop :=
  | wtr_unit :
    well_typed_references m <{ unit }> 

  | wtr_num : forall n,
    well_typed_references m <{ N n }>

  | wtr_refM : forall T ad,
    empty |-- m[ad].tm is T ->
    well_typed_references m <{ &ad :: &T }>

  | wtr_refI : forall T ad,
    empty |-- m[ad].tm is (TY_Immut T) ->
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

  | wtr_var : forall x,
    well_typed_references m <{ var x }>

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

(* All terms inside the memory are well typed and satisfy the 
well-typed-references property. *)
Definition well_typed_memory (m : mem) := forall ad,
  ad < length m ->
  ((exists T, empty |-- m[ad].tm is T) /\ well_typed_references m m[ad].tm).

Ltac inversion_wtr m :=
  inversion_term_predicate (well_typed_references m).

Ltac inversion_clear_wtr m :=
  inversion_clear_term_predicate (well_typed_references m).

(* ------------------------------------------------------------------------- *)
(* Auxiliary.                                                                *)
(* ------------------------------------------------------------------------- *)

Local Lemma wtt_alloc_value : forall t t' ad v V T,
  empty |-- t is T ->
  t --[EF_Alloc ad v V]--> t' ->
  exists V', empty |-- v is V'.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_type; eauto.
Qed.

Local Lemma wtt_write_value : forall t t' ad v V T,
  empty |-- t is T ->
  t --[EF_Write ad v V]--> t' ->
  exists V', empty |-- v is V'.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_type; eauto.
Qed.

Local Lemma wtt_write_memory_address : forall m t t' ad v V Vp T,
  empty |-- t is T ->
  empty |-- v is V ->
  well_typed_references m t ->
  t --[EF_Write ad v Vp]--> t' ->
  empty |-- m[ad].tm is V.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_type; inversion_wtr m; eauto.
  inversion_type. inversion_wtr m.
  apply_deterministic_typing. assumption.
Qed.

Local Lemma wtr_alloc_value : forall m t t' ad v V,
  well_typed_references m t ->
  t --[EF_Alloc ad v V]--> t' ->
  well_typed_references m v.
Proof.
  intros. induction_step; intros; inversion_wtr m; eauto.
Qed.

Local Lemma wtr_write_value : forall m t t' ad v V,
  well_typed_references m t ->
  t --[EF_Write ad v V]--> t' ->
  well_typed_references m v.
Proof.
  intros. induction_step; intros; inversion_wtr m; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* well-typed-references preservation                                        *)
(* ------------------------------------------------------------------------- *)

Local Lemma wtr_subst : forall m x Tx t v,
  well_typed_references m v ->
  well_typed_references m <{ fn x Tx --> t }> ->
  well_typed_references m ([x := v] t).
Proof.
  intros. inversion_clear_wtr m.
  induction t; simpl; inversion_wtr m; eauto using well_typed_references;
  destruct String.string_dec; eauto using well_typed_references.
Qed.

Local Lemma wtr_mem_add : forall m t v V,
  valid_accesses m t ->
  well_typed_references m t ->
  well_typed_references (m +++ (v, V)) t.
Proof.
  intros * ? Hwtr. generalize dependent v.
  induction Hwtr; intros; try (inversion_va);
  eauto using well_typed_references;
  (eapply wtr_refM || eapply wtr_refI);
  rewrite (get_add_lt memory_default); eauto using access.
Qed.

Local Lemma wtr_mem_set : forall m t ad' v V T,
  ad' < length m ->
  empty |-- v is T ->
  empty |-- m[ad'].tm is T ->
  well_typed_references m t ->
  well_typed_references m[ad' <- (v, V)] t.
Proof.
  intros * ? ? ? Hwtr. 
  induction Hwtr; eauto using well_typed_references;
  (eapply wtr_refM || eapply wtr_refI);
  decompose sum (lt_eq_lt_dec ad' ad); subst;
  simpl_array; trivial; apply_deterministic_typing; trivial.
Qed.

Local Lemma wtr_preservation_none : forall m t t',
  well_typed_references m t ->
  t --[EF_None]--> t' ->
  well_typed_references m t'.
Proof.
  intros. induction_step; inversion_wtr m;
  eauto using well_typed_references, wtr_subst.
Qed.

Local Lemma wtr_preservation_alloc: forall m t t' v V T,
  empty |-- t is T ->
  valid_accesses m t ->
  well_typed_references m t ->
  t --[EF_Alloc (length m) v V]--> t' ->
  well_typed_references (m +++ (v, V)) t'.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_va; inversion_type; inversion_wtr m;
  eauto using well_typed_references, wtr_mem_add;
  (eapply wtr_refM || eapply wtr_refI);
  simpl_array; trivial.
Qed.

Local Lemma wtr_preservation_read : forall m t t' ad,
  ad < length m ->
  well_typed_references m t ->
  well_typed_memory m ->
  t --[EF_Read ad m[ad].tm]--> t' ->
  well_typed_references m t'.
Proof.
  intros * ? ? Hwtm ?.
  induction_step; inversion_wtr m; eauto using well_typed_references.
  inversion_wtr m; destruct (Hwtm ad) as [_ ?]; trivial.
Qed.

Local Lemma wtr_preservation_write : forall m t t' ad v V T,
  ad < length m ->
  empty |-- t is T ->
  well_typed_references m t ->
  well_typed_memory m ->
  t --[EF_Write ad v V]--> t' ->
  well_typed_references m[ad <- (v, V)] t'.
Proof.
  intros.
  assert (exists V, empty |-- v is V) as [? ?] by eauto using wtt_write_value.
  generalize dependent T.
  induction_step; intros; inversion_type; inversion_wtr m;
  eauto using well_typed_references, wtr_mem_set, wtt_write_memory_address.
Qed.

Theorem well_typed_references_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  valid_accesses m t ->
  well_typed_references m t ->
  well_typed_memory m ->
  m / t ==[eff]==> m' / t' ->
  well_typed_references m' t'.
Proof.
  intros. inversion_mstep;
  eauto using wtr_preservation_none, wtr_preservation_alloc,
    wtr_preservation_read, wtr_preservation_write.
Qed.

(* ------------------------------------------------------------------------- *)
(* well-typed-memory preservation                                            *)
(* ------------------------------------------------------------------------- *)

Theorem well_typed_memory_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  valid_accesses m t ->
  forall_memory_terms m (valid_accesses m) ->
  well_typed_references m t ->
  well_typed_memory m ->
  m / t ==[eff]==> m' / t' ->
  well_typed_memory m'.
Proof.
  intros * ? ? ? ? Hwtm ?. inversion_mstep; trivial;
  intros ad' Hlen; specialize (Hwtm ad'); destruct_and Hwtm;
  assert (exists V, empty |-- v is V) as [? ?]
    by eauto using wtt_alloc_value, wtt_write_value.
  - rewrite add_increments_length in Hlen.
    split; decompose sum (lt_eq_lt_dec ad' (length m)); subst;
    simpl_array; eauto using well_typed_references;
    eauto using well_typed_term, wtr_mem_add, wtr_alloc_value.
  - rewrite set_preserves_length in Hlen.
    split; decompose sum (lt_eq_lt_dec ad' ad); subst;
    simpl_array;
    eauto using wtr_mem_set, wtr_write_value, wtt_write_memory_address.
Qed.

