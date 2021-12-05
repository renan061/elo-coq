From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.

From Elo Require Export Array.
From Elo Require Export Map.
From Elo Require Export Core.

Ltac splits n :=
  match n with
  | O => fail
  | S O => idtac
  | S ?n' => split; [| splits n']
  end.

(* ------------------------------------------------------------------------- *)
(* Determinism ------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Lemma value_does_not_step : forall v t eff,
  value v -> ~ (v --> t # eff).
Proof.
  intros * Hv Hstep. destruct Hv; inversion Hstep.
Qed.

Theorem deterministic_step : forall t t1 t2 eff,
  t --> t1 # eff ->
  t --> t2 # eff ->
  t1 = t2.
Proof.
  intros * Hstep1. generalize dependent t2.
  induction Hstep1; intros * Hstep2; inversion Hstep2; subst;
  try solve
    [ congruence
    | match goal with
      | Hstep : ?v --> _ # _ , Hv : value ?v |- _ =>
          eapply value_does_not_step in Hstep; eauto; contradiction
      | F : TM_Nil         --> _ # _ |- _ => inversion F
      | F : TM_Num _       --> _ # _ |- _ => inversion F
      | F : TM_Arr _ _     --> _ # _ |- _ => inversion F
      | F : TM_Fun _ _ _ _ --> _ # _ |- _ => inversion F
      | F : TM_Loc _       --> _ # _ |- _ => inversion F
      | H : forall x, _ --> x # _ -> _ = x |- _ => erewrite H; eauto
      end
    ].
Qed.

Theorem deterministic_typing : forall mt Gamma t X Y,
  mt / Gamma |-- t is X ->
  mt / Gamma |-- t is Y ->
  X = Y.
Proof.
  intros * HX. generalize dependent Y.
  induction HX; intros Y HY; inversion HY; subst;
  try solve 
    [ congruence
    | auto
    | match goal with
      | IH : forall T, ?mt / ?Gamma |-- ?t is T -> (_ _) = T,
        H : ?mt / ?Gamma |-- ?t is (_ _)
        |- _ = _ => apply IH in H; congruence
      end
    ].
Qed.

(* ------------------------------------------------------------------------- *)
(* Definitions ------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Definition well_typed_memory mt m :=
  length mt = length m /\
  (forall i, mt / empty |-- (get_tm m i) is (get_typ mt i)).

Definition well_typed_threads mt ths := forall i,
  exists T, mt / empty |-- (get_tm ths i) is T.

Definition well_typed_program mt m ths :=
  well_typed_memory mt m /\
  well_typed_threads mt ths.

Definition finished ths :=
  forall i, value (get_tm ths i).

Inductive extends' {A} : list A -> list A -> Prop :=
  | extends_nil : forall mt,
    extends' mt nil
  | extends_cons : forall x mt mt',
    extends' mt mt' ->
    extends' (x :: mt) (x :: mt').

Infix "extends" := extends' (at level 50, left associativity).

(* ------------------------------------------------------------------------- *)
(* Auxiliary Lemmas -------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Lemma extends_refl : forall {A} (mt : list A),
  mt extends mt.
Proof.
  induction mt; auto using @extends'.
Qed.

Lemma extends_add : forall {A} (mt : list A) a,
  (add mt a) extends mt.
Proof.
  induction mt; eauto using @extends'.
Qed.

Lemma extends_length : forall {A} (mt mt' : list A) i,
  i < length mt' ->
  mt extends mt' ->
  i < length mt.
Proof.
  intros *. generalize dependent mt. generalize dependent i.
  induction mt'; intros * Hlen Hext.
  - inversion Hlen.
  - inversion Hext. destruct i;
    eauto using PeanoNat.Nat.lt_0_succ, Lt.lt_n_S, Lt.lt_S_n.
Qed.

Lemma extends_lookup : forall (mt mt' : list typ) i,
  i < length mt' ->
  mt extends mt' ->
  get_typ mt' i = get_typ mt i.
Proof.
  intros *. generalize dependent mt. generalize dependent i.
  induction mt'; intros * Hlen Hext.
  - inversion Hlen.
  - inversion Hext. subst. destruct i.
    + reflexivity.
    + unfold get_typ, get. simpl in *. eauto using Lt.lt_S_n.
Qed.

Lemma safe_preserves_inclusion : forall Gamma Gamma',
  Gamma includes Gamma' ->
  (safe Gamma) includes (safe Gamma').
Proof.
  unfold Map.includes', safe. intros * H *.
  destruct (Gamma k) eqn:E1; destruct (Gamma' k) eqn:E2;
  solve [ intros F; inversion F
        | eapply H in E2; rewrite E1 in E2; inversion E2; subst; trivial
        ].
Qed.

Lemma update_safe_includes_comm : forall Gamma id T,
  (update (safe Gamma) id T) includes (safe (update Gamma id T)).
Proof.
  unfold Map.includes', update, Map.update', safe. intros *.
  destruct String.eqb; trivial.
  destruct is_safe_type; trivial.
  intros F. inversion F.
Qed.

Lemma memory_weakening : forall mt mt' Gamma t T, 
  mt extends mt' ->
  mt' / Gamma |-- t is T ->  
  mt  / Gamma |-- t is T.
Proof.
  intros * Hext Htype.
  induction Htype; eauto using @typeof, extends_length;
  subst; erewrite extends_lookup; eauto using extends_length, @typeof.
Qed.

Lemma context_weakening : forall mt Gamma Gamma' t T,
  Gamma includes Gamma' ->
  mt / Gamma' |-- t is T ->
  mt / Gamma  |-- t is T.
Proof.
  intros * Hinc Htype.
  generalize dependent Gamma.
  induction Htype; intros * Hinc;
  eauto 6 using @typeof, safe_preserves_inclusion, update_preserves_inclusion.
Qed.

Lemma context_weakening_empty : forall mt Gamma t T,
  mt / empty |-- t is T ->
  mt / Gamma |-- t is T.
Proof.
  intros * Htype.
  eapply (context_weakening _ _ empty); auto.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall mt Gamma id t u T U,
  mt / (update Gamma id U) |-- t is T ->
  mt / empty |-- u is U ->
  mt / Gamma |-- [id := u] t is T.
Proof with eauto using context_weakening, context_weakening_empty,
  lookup_update_kneq, update_overwrite, update_permutation,
  update_safe_includes_comm.

  intros * Ht Hu.
  generalize dependent T. generalize dependent Gamma.
  induction t; intros * Ht; inversion Ht; simpl; subst;
  eauto using @typeof;
  try (destruct String.eqb eqn:E);
  try (apply String.eqb_eq in E; subst);
  try (apply String.eqb_neq in E).
  - rewrite lookup_update_keq in H1. inversion H1. subst...
  - apply T_Id_Val. rewrite <- H1. symmetry...
  - rewrite lookup_update_keq in H1. inversion H1. subst...
  - apply T_Id_Var. rewrite <- H1. symmetry...
  - eapply T_Spawn...
  - apply T_LetVal...
  - apply T_LetVal...
  - apply T_LetVar...
  - apply T_LetVar...
  - eapply T_LetFun...
  - eapply T_LetFun...
  - apply T_Fun...
  - apply T_Fun...
Qed.

Lemma stored_value_has_type : forall mt t t' addr v T,
  t --> t' # EF_Store addr v ->
  mt / empty |-- t is T ->
  mt / empty |-- v is get_typ mt addr.
Proof.
  intros * Hstep Htype. generalize dependent t'.
  induction Htype; intros * Hstep;
  inversion Hstep; subst; eauto.
  inversion Htype1. subst. eauto.
Qed.

Lemma spawn_block_has_type : forall mt t t' block T,
  mt / empty |-- t is T ->
  t --> t' # EF_Spawn block ->
  exists B, mt / empty |-- block is B.
Proof.
  remember empty as Gamma.
  intros * Htype. generalize dependent t'.
  induction Htype; intros * Hstep; inversion Hstep; subst; eauto.
Qed.

Lemma set_preserves_memory_typing : forall m mt t i,
  i < length m ->
  well_typed_memory mt m ->
  mt / empty |-- t is (get_typ mt i) ->
  well_typed_memory mt (set m i t).
Proof.
  intros * ? [Hlen ?] ?. split.
  - rewrite Hlen. apply set_preserves_length.
  - intros j. destruct (i =? j) eqn:E.
    + apply Nat.eqb_eq in E. subst. erewrite (get_set_involutive TM_Nil); auto.
    + apply Nat.eqb_neq in E. erewrite (get_set_i_neq_j TM_Nil); auto.
Qed.

Lemma add_preserves_memory_typing : forall mt m t T,
  well_typed_memory mt m ->
  mt / empty |-- t is T ->
  well_typed_memory (add mt T) (add m t).
Proof.
  intros * [Hlen Hmem] Htype.
  split; auto using add_preserves_length. intros i.
  destruct (lt_eq_lt_dec i (length m)) as [[Hlt | Heq] | Hgt];
  unfold get_tm, get_typ in *; subst.
  - rewrite get_add_lt; trivial.
    rewrite <- Hlen in Hlt.
    rewrite get_add_lt; trivial.
    eauto using extends_add, memory_weakening.
  - rewrite get_add_last. rewrite <- Hlen. rewrite get_add_last.
    eauto using extends_add, memory_weakening.
  - rewrite get_add_gt; trivial.
    rewrite <- Hlen in Hgt.
    rewrite get_add_gt; trivial.
    apply T_Nil.
Qed.

Lemma set_preserves_thread_typing : forall mt ths t T i,
  i < length ths ->
  well_typed_threads mt ths ->
  mt / empty |-- t is T ->
  well_typed_threads mt (set ths i t).
Proof.
  intros * Hlen Htype Hstep.
  intros i'. destruct (i =? i') eqn:E.
  - apply Nat.eqb_eq in E. subst.
    rewrite (get_set_involutive TM_Nil); eauto.
  - apply Nat.eqb_neq in E. apply not_eq_sym in E.
    rewrite (get_set_i_neq_j TM_Nil); eauto.
Qed.

Lemma add_preserves_thread_typing : forall mt ths t T,
  well_typed_threads mt ths ->
  mt / empty |-- t is T ->
  well_typed_threads mt (add ths t).
Proof.
  intros * Hths Htype.
  intros i. destruct (lt_eq_lt_dec i (length ths)) as [[? | Heq] | Hlt].
  - specialize (Hths i) as [? ?]. rewrite (get_add_lt TM_Nil); eauto.
  - subst. rewrite (get_add_last TM_Nil). eauto.
  - rewrite (get_add_gt TM_Nil); eauto using T_Nil.
Qed.

(* ------------------------------------------------------------------------- *)
(* Preservation ------------------------------------------------------------ *)
(* ------------------------------------------------------------------------- *)

Theorem limited_preservation : forall mt t t' eff T,
  mt / empty |-- t is T ->
  t --> t' # eff ->
  ~ (exists addr v, EF_Load addr v = eff) ->
  mt / empty |-- t' is T.
Proof.
  remember empty as Gamma.
  intros * Htype Hstep Heff. generalize dependent t'.
  induction Htype; intros * Hstep;
  inversion Hstep; subst; eauto using @typeof, substitution_preserves_typing;
  solve [contradiction Heff; eexists; eexists; eauto].
Qed.

Theorem preservation : forall ths ths' m m' mt,
  well_typed_program mt m ths ->
  m / ths ==> m' / ths' ->
  exists mt',
    mt' extends mt /\
    well_typed_program mt' m' ths'.
Proof.
  intros * [Hmem Hths] Hcstep. induction Hcstep.
  - exists mt. splits 3; eauto using extends_refl.
    intros i'. destruct (i =? i') eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite (get_set_involutive TM_Nil); trivial.
      specialize (Hths i') as [? ?]. eexists.
      eapply limited_preservation; eauto. intros [? [? F]]. discriminate F.
    + apply Nat.eqb_neq in E. apply not_eq_sym in E.
      rewrite (get_set_i_neq_j TM_Nil); trivial.
  - exists mt. splits 3; eauto using extends_refl.
    intros i'. destruct (i =? i') eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite (get_set_involutive TM_Nil); trivial.
      specialize Hmem as [? ?]. eexists. eauto.
    + apply Nat.eqb_neq in E. apply not_eq_sym in E.
      rewrite (get_set_i_neq_j TM_Nil); trivial.
  - exists mt. splits 3; eauto using extends_refl.
    + specialize (Hths i) as [T Htype].
      apply set_preserves_memory_typing; eauto.
      eauto using stored_value_has_type.
    + destruct (Hths i) as [? ?].
      eapply set_preserves_thread_typing; eauto.
      eapply limited_preservation; eauto.
      intros [? [? F]]. inversion F.
  - eexists. splits 3; eauto using extends_refl.
    destruct (Hths i) as [? ?].
    assert (exists B, mt / empty |-- block is B) as [? Htype].
    { eauto using spawn_block_has_type. }
    eapply add_preserves_thread_typing; eauto. clear Htype.
    eapply set_preserves_thread_typing; eauto.
    eapply limited_preservation; eauto.
    intros [? [? F]]. inversion F.
Qed.

(* ------------------------------------------------------------------------- *)
(* Progress ---------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Theorem limited_progress : forall m mt t T,
  mt / empty |-- t is T ->
  well_typed_memory mt m ->
  (value t \/ exists t' eff, t --> t' # eff).
Proof.
  remember empty as Gamma. intros * Htype [Hlen Hmem].
  assert (forall i, i < length mt -> i < length m). { rewrite Hlen. trivial. }
  induction Htype; subst; auto using value; right;
  try match goal with F : lookup empty _ = Some _ |- _ => inversion F end;
  repeat match goal with
    IH : _ = empty -> _ |- _ => specialize (IH eq_refl) as [? | [? [? ?]]]
  end.
  - eexists. eexists. eapplyeauto using step.
  try solve [eexists; eexists; eauto using step];
  repeat match goal with
    Hv : value ?t , Htype : _ / _ |-- ?t is _ |- _ =>
      destruct Hv; inversion Htype; subst
  end;
  eexists; eexists; eauto using step, value.
Qed.

Theorem progress : forall m mt ths,
  well_typed_program mt m ths ->
  (finished ths \/ exists m' ths', m / ths ==> m' / ths').
Proof.
  intros * [[Hlen Hmem] Hths].
  assert (forall i, i < length mt -> i < length m). { rewrite Hlen. trivial. }

  induction Htype; subst; auto using value; right;
  try match goal with F : lookup empty _ = Some _ |- _ => inversion F end;
  repeat match goal with
    IH : _ = empty -> _ |- _ => specialize (IH eq_refl) as [? | [? [? [? ?]]]]
  end;
  try solve [eexists; eexists; eexists; eauto using step];
  repeat match goal with
    Hv : value ?t , Htype : _ / _ |-- ?t is _ |- _ =>
      destruct Hv; inversion Htype; subst
  end;
  eexists; eexists; eexists; eauto using step, value.
Qed.
