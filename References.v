From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import WBA.

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

Definition well_typed_memory (m : mem) := forall ad,
  ad < length m ->
  ((exists T, empty |-- m[ad] is T) /\ well_typed_references m m[ad]).

(* ------------------------------------------------------------------------- *)
(* Auxiliary.                                                                *)
(* ------------------------------------------------------------------------- *)

Local Lemma well_typed_alloc_value : forall t t' ad v T,
  empty |-- t is T ->
  t --[EF_Alloc ad v]--> t' ->
  exists V, empty |-- v is V.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_type; eauto.
Qed.

Local Lemma well_typed_write_value : forall t t' ad v T,
  empty |-- t is T ->
  t --[EF_Write ad v]--> t' ->
  exists V, empty |-- v is V.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_type; eauto.
Qed.

Local Lemma wtr_alloc_value : forall m t t' ad v,
  well_typed_references m t ->
  t --[EF_Alloc ad v]--> t' ->
  well_typed_references m v.
Proof.
  intros * Hwtr ?. induction_step; intros; inversion_clear Hwtr; eauto.
Qed.

Local Lemma wtr_write_value : forall m t t' ad v,
  well_typed_references m t ->
  t --[EF_Write ad v]--> t' ->
  well_typed_references m v.
Proof.
  intros * Hwtr ?. induction_step; intros; inversion_clear Hwtr; eauto.
Qed.

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

Local Lemma wtr_preservation_write : forall m t t' ad v T,
  ad < length m ->
  empty |-- t is T ->
  well_typed_references m t ->
  well_typed_memory m ->
  t --[EF_Write ad v]--> t' ->
  well_typed_references m[ad <- v] t'.
Proof.
  intros * Hlen HtypeT Hwtr Hwtm ?.

  assert (exists V, empty |-- v is V) as [V ?]
    by eauto using well_typed_write_value.

  assert (empty |-- m[ad] is V). {
    generalize dependent T.
    induction_step; intros;
    inversion_clear HtypeT; inversion_clear Hwtr; eauto.
    match goal with
    | Htype : empty |-- <{ &_ :: _ }> is _,
      Hwtr : well_typed_references m <{ &_ :: _ }>
      |- _ =>
          inversion Htype; subst; inversion_clear Hwtr
    end.
    erewrite deterministic_typing; eauto.
  }

  generalize dependent T.
  induction_step; intros; inversion_type; inversion_clear Hwtr;
  eauto using well_typed_references, wtr_mem_set.
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

(* ------------------------------------------------------------------------- *)
(* well-typed-memory preservation                                            *)
(* ------------------------------------------------------------------------- *)

Local Lemma todo0 : forall m ad v,
  well_behaved_access m m[ad] ->
  well_typed_references m m[ad] ->
  well_typed_references (m +++ v) m[ad].
Proof.
  intros * Hwba Hwtr. induction Hwtr;
  try destruct_wba; eauto using well_typed_references.
  - eapply wtr_refM.
    decompose sum (lt_eq_lt_dec ad0 (length m)); subst.
    + rewrite (get_add_lt TM_Unit); trivial.
    + specialize (Hwba (length m) (access_ref _ _ _)). lia.
    + rewrite (get_add_gt TM_Unit); trivial.
      rewrite (get_default TM_Unit) in H; trivial. lia.
  - eapply wtr_refI.
    decompose sum (lt_eq_lt_dec ad0 (length m)); subst. (* TODO *)
    + rewrite (get_add_lt TM_Unit); trivial.
    + specialize (Hwba (length m) (access_ref _ _ _)). lia.
    + rewrite (get_add_gt TM_Unit); trivial.
      rewrite (get_default TM_Unit) in H; trivial. lia.
Qed.

Local Lemma todo1 : forall m t ad v T,
  ad < length m ->
  empty |-- v is T ->
  empty |-- m[ad] is T ->
  well_typed_references m t ->
  well_typed_references m v ->
  well_typed_references m[ad <- v] t.
Proof.
  intros * ? ? ? Hwtr ?. generalize dependent T. 
  induction Hwtr; intros * HtypeV HtypeM; 
  eauto using well_typed_references.
  - eapply wtr_refM.
    decompose sum (lt_eq_lt_dec ad0 ad); subst.
    + rewrite (get_set_lt TM_Unit); trivial.
    + apply_deterministic_typing. rewrite (get_set_eq TM_Unit); trivial.
    + rewrite (get_set_gt TM_Unit); trivial.
  - eapply wtr_refI.
    decompose sum (lt_eq_lt_dec ad0 ad); subst.
    + rewrite (get_set_lt TM_Unit); trivial.
    + apply_deterministic_typing. rewrite (get_set_eq TM_Unit); trivial.
    + rewrite (get_set_gt TM_Unit); trivial.
Qed.

Local Lemma todo2 : forall m ad ad' v T,
  ad < length m ->
  empty |-- v is T ->
  empty |-- m[ad] is T ->
  well_typed_references m v ->
  well_typed_references m m[ad'] ->
  well_typed_references m [ad <- v] m [ad'].
Proof.
  intros * ? ? ? HwtrV HwtrM.
  induction HwtrM; eauto using well_typed_references.
  - eapply wtr_refM.
    decompose sum (lt_eq_lt_dec ad0 ad); subst.
    + rewrite (get_set_lt TM_Unit); trivial.
    + apply_deterministic_typing. rewrite (get_set_eq TM_Unit); trivial.
    + rewrite (get_set_gt TM_Unit); trivial.
  - eapply wtr_refI.
    decompose sum (lt_eq_lt_dec ad0 ad); subst.
    + rewrite (get_set_lt TM_Unit); trivial.
    + apply_deterministic_typing. rewrite (get_set_eq TM_Unit); trivial.
    + rewrite (get_set_gt TM_Unit); trivial.
Qed.

Local Lemma todo3 : forall m t v,
  well_behaved_access m t ->
  well_typed_references m t ->
  well_typed_references m v ->
  well_typed_references (m +++ v) t.
Proof.
  intros * Hwba Hwtr ?.
  induction Hwtr; try destruct_wba;
  eauto using well_typed_references.
  - eapply wtr_refM.
    decompose sum (lt_eq_lt_dec ad (length m)); subst.
    + rewrite (get_add_lt TM_Unit); trivial.
    + specialize (Hwba (length m) (access_ref _ _ _)). lia.
    + rewrite (get_add_gt TM_Unit); trivial.
      rewrite get_default in H0; trivial. lia.
  - eapply wtr_refI.
    decompose sum (lt_eq_lt_dec ad (length m)); subst.
    + rewrite (get_add_lt TM_Unit); trivial.
    + specialize (Hwba (length m) (access_ref _ _ _)). lia.
    + rewrite (get_add_gt TM_Unit); trivial.
      rewrite get_default in H0; trivial. lia.
Qed.

Theorem well_typed_memory_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  well_behaved_access m t ->
  well_typed_references m t ->
  well_typed_memory m ->
  m / t ==[eff]==> m' / t' ->
  well_typed_memory m'.
Proof.
  intros * Htype Hwba Hwtr Hwtm ?. inversion_mstep; trivial.
  - intros ad Hlen. split;
    rewrite add_increments_length in Hlen.
    + destruct (lt_eq_lt_dec ad (length m)) as [[Hlt | ?] | ?]; subst.
      * specialize (Hwtm ad Hlt) as [? _].
        rewrite (get_add_lt TM_Unit); trivial.
      * rewrite (get_add_eq TM_Unit); eauto using well_typed_alloc_value.
      * rewrite (get_add_gt TM_Unit); eauto using well_typed_term.
    + destruct (lt_eq_lt_dec ad (length m)) as [[Hlt | ?] | ?]; subst.
      * specialize (Hwtm ad Hlt) as [_ ?].
        rewrite (get_add_lt TM_Unit); trivial.
        eapply todo0; trivial.
        shelve.
      * rewrite (get_add_eq TM_Unit); trivial.
        eapply todo3; trivial.
        ** shelve.
        ** shelve.
        ** shelve.
      * rewrite (get_add_gt TM_Unit); eauto using well_typed_references.
  - intros ad' Hlen. rewrite set_preserves_length in Hlen. split.
    + decompose sum (lt_eq_lt_dec ad' ad); subst.
      * specialize (Hwtm ad' Hlen) as [? _].
        rewrite (get_set_lt TM_Unit); trivial.
      * rewrite (get_set_eq TM_Unit); eauto using well_typed_write_value.
      * specialize (Hwtm ad' Hlen) as [? _].
        rewrite (get_set_gt TM_Unit); trivial.
    + decompose sum (lt_eq_lt_dec ad' ad); subst.
      * specialize (Hwtm ad' Hlen) as [_ ?].
        rewrite (get_set_lt TM_Unit); trivial.
        eapply todo2; trivial.
        ** shelve.
        ** shelve.
        ** shelve.
      * rewrite (get_set_eq TM_Unit); trivial.
        eapply todo1; trivial.
        ** shelve.
        ** shelve.
        ** shelve.
        ** shelve.
      * specialize (Hwtm ad' Hlen) as [_ ?].
        rewrite (get_set_gt TM_Unit); trivial.
        eapply todo2; trivial.
        ** shelve.
        ** shelve.
        ** shelve.
Qed.

