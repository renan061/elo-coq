From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Strings.String.

From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import WBA.

Lemma context_weakening : forall Gamma Gamma' t T,
  Gamma includes Gamma' ->
  Gamma' |-- t is T ->
  Gamma  |-- t is T.
Proof.
  intros. generalize dependent Gamma.
  induction_type; intros;
  eauto using well_typed_term, update_preserves_inclusion.
Qed.

Lemma context_weakening_empty : forall Gamma t T,
  empty |-- t is T ->
  Gamma |-- t is T.
Proof.
  intros. eapply (context_weakening _ empty); trivial. discriminate.
Qed.

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Inductive well_behaved_references (m : mem) : tm -> Prop :=
  | wbr_unit :
    well_behaved_references m <{ unit }> 

  | wbr_num : forall n,
    well_behaved_references m <{ N n }>

  | wbr_refM : forall T ad,
    empty |-- m[ad] is T ->
    well_behaved_references m <{ &ad :: &T }>

  | wbr_refI : forall T ad,
    empty |-- m[ad] is T ->
    well_behaved_references m <{ &ad :: i&T }>

  | wbr_new : forall T t,
    well_behaved_references m t ->
    well_behaved_references m <{ new T t }> 

  | wbr_load : forall t,
    well_behaved_references m t ->
    well_behaved_references m <{ *t }> 

  | wbr_asg : forall t1 t2,
    well_behaved_references m t1 ->
    well_behaved_references m t2 ->
    well_behaved_references m <{ t1 = t2 }> 

  | wbr_id : forall x,
    well_behaved_references m <{ ID x }>

  | wbr_fun : forall x Tx t,
    well_behaved_references m t ->
    well_behaved_references m <{ fn x Tx --> t }>

  | wbr_call : forall t1 t2,
    well_behaved_references m t1 ->
    well_behaved_references m t2 ->
    well_behaved_references m <{ call t1 t2 }> 

  | wbr_seq : forall t1 t2,
    well_behaved_references m t1 ->
    well_behaved_references m t2 ->
    well_behaved_references m <{ t1; t2 }> 
  .

Lemma wbr_subst : forall m x Tx t v,
  well_behaved_references m v ->
  well_behaved_references m <{ fn x Tx --> t }> ->
  well_behaved_references m ([x := v] t).
Proof.
  intros * ? Hwbr. 
  assert (Hwbr' : well_behaved_references m t) by (inversion Hwbr; trivial).
  clear Hwbr.
  induction t; simpl; try (destruct String.string_dec);
  inversion Hwbr'; eauto using well_behaved_references.
Qed.

Lemma wbr_mem_add : forall m t v, 
  well_behaved_access m t ->
  well_behaved_references m t ->
  well_behaved_references (m +++ v) t.
Proof.
  intros * Hwba Hwbr. induction t; eauto using well_behaved_references;
  inversion_clear Hwbr; subst; try (destruct_wba);
  eauto using well_behaved_references;
  try (eapply wbr_refM || eapply wbr_refI);
  match goal with
  | H : _ |-- _ [ ?ad ] is _ |- _ => 
    decompose sum (lt_eq_lt_dec (length m) ad); subst
  end;
  try (specialize (Hwba _ (access_loc _ _ _)));
  solve [ rewrite (get_add_gt TM_Unit); lia
        | rewrite (get_add_eq TM_Unit); lia
        | rewrite (get_add_lt TM_Unit); trivial
        ].
Qed.

Lemma wbr_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  well_behaved_access m t ->
  well_behaved_references m t ->
  m / t ==[eff]==> m' / t' ->
  well_behaved_references m' t'.
Proof.
  intros * Htype Hwba Hwbr ?. inversion_mstep.
  - clear Htype. clear Hwba.
    induction_step; inversion Hwbr; subst;
    eauto using well_behaved_references, wbr_subst.
  - generalize dependent T.
    induction_step; intros * Htype; inversion_clear Htype; 
    try solve [
      inversion_clear Hwbr; destruct_wba;
      eauto using well_behaved_references, wbr_mem_add
    ];
    try (eapply wbr_refM || eapply wbr_refI);
    rewrite (get_add_eq TM_Unit); trivial.
  - clear Hwba.
    generalize dependent T. 
    induction_step; intros * Htype; inversion_clear Htype;
    try solve [
      inversion_clear Hwbr;
      eauto using well_behaved_references, wbr_mem_add
    ].
    + inversion_clear Hwbr; subst.
      inversion_clear H1; subst.
Admitted.

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Lemma preservation_subst : forall t tx T Tx Tx' Gamma x,
  Gamma |-- (TM_Fun x Tx t) is (TY_Fun Tx' T) ->
  empty |-- tx is Tx' ->
  Gamma |-- [x := tx] t is T.
Proof.
  assert (forall t tx T Tx Gamma x,
    Gamma[x <== Tx] |-- t is T ->
    empty |-- tx is Tx ->
    Gamma |-- [x := tx] t is T
  ). {
    unfold subst. intros ?.
    induction t; intros * Htype ?; 
    try (destruct String.string_dec);
    inversion Htype; subst; 
    eauto using well_typed_term, context_weakening, context_weakening_empty,
      update_overwrite, update_permutation.
  }
  intros * ?. inversion_type. intros. eapply H; eauto.
Qed.

Theorem preservation : forall m m' t t' eff T,
  well_behaved_references m t ->
  empty |-- t is T ->
  m / t ==[eff]==> m' / t' ->
  empty |-- t' is T.
Proof.
  intros * Hwbr Htype ?. inversion_mstep; generalize dependent t'.
  remember empty as Gamma.
  - clear Hwbr.
    induction Htype; intros; inversion_step;
    eauto using well_typed_term, preservation_subst.
  - clear Hwbr.
    induction Htype; intros; inversion_step;
    eauto using well_typed_term.
  - induction Htype; intros;
    inversion_step; inversion_clear Hwbr; subst;
    eauto using well_typed_term;
    inversion Htype; subst.
    + match goal with
      | Hwbr' : well_behaved_references _ _ |- _ =>
        inversion Hwbr'; subst
      end.
      eauto using context_weakening_empty.
    + match goal with
      | Hwbr' : well_behaved_references _ _ |- _ =>
        inversion Hwbr'; subst
      end.
      eauto using context_weakening_empty.
  - induction Htype; intros; inversion_step; try (inversion Hwbr; subst);
    eauto using well_typed_term.
Qed.

