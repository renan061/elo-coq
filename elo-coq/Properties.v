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

Lemma value_does_not_step : forall m m' v t eff,
  value v -> ~ (m / v --> eff / m' / t).
Proof.
  intros * Hv Hstep. destruct Hv; inversion Hstep.
Qed.

Theorem deterministic_step : forall m m' t t1 t2 eff,
  m / t --> eff / m' / t1 ->
  m / t --> eff / m' / t2 ->
  t1 = t2.
Proof.
  intros * Hstep1. generalize dependent t2.
  induction Hstep1; intros * Hstep2; inversion Hstep2; subst;
  try solve
    [ congruence
    | match goal with
      | Hstep : _ / ?v --> _ / _ / _ , Hv : value ?v |- _ =>
        exfalso; apply (value_does_not_step _ _ _ _ _ Hv Hstep); auto
      | F : _ / TM_Nil         --> _ / _ / _ |- _ => inversion F
      | F : _ / TM_Num _       --> _ / _ / _ |- _ => inversion F
      | F : _ / TM_Arr _ _     --> _ / _ / _ |- _ => inversion F
      | F : _ / TM_Fun _ _ _ _ --> _ / _ / _ |- _ => inversion F
      | F : _ / TM_Loc _       --> _ / _ / _ |- _ => inversion F
      | H : forall x, _ / _ --> _ / _ / x -> _ = x |- _ => erewrite H; eauto
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
(* Progress, Preservation & Soundness -------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Definition well_typed_memory (mt : list typ) (m : mem) :=
  length mt = length m /\
  (forall i, mt / empty |-- (get_tm m i) is (get_typ mt i)).

Inductive extends' {A} : list A -> list A -> Prop :=
  | extends_nil : forall mt,
    extends' mt nil
  | extends_cons : forall x mt mt',
    extends' mt mt' ->
    extends' (x :: mt) (x :: mt').

Infix "extends" := extends' (at level 50, left associativity).

Lemma extends_lookup : forall i (mt mt' : list typ),
  i < length mt' ->
  mt extends mt' ->
  get_typ mt' i = get_typ mt i.
Proof.
  intros *.
  generalize dependent mt.
  generalize dependent i.
  induction mt'; intros * Hlen Hext.
  - inversion Hlen.
  - inversion Hext. subst. destruct i.
    + reflexivity.
    + unfold get_typ, get. simpl in *. eauto using Lt.lt_S_n.
Qed.

Lemma extends_length : forall {A} i (mt mt' : list A),
  i < length mt' ->
  mt extends mt' ->
  i < length mt.
Proof.
  intros *.
  generalize dependent mt.
  generalize dependent i.
  induction mt'; intros * Hlen Hext.
  - inversion Hlen.
  - inversion Hext. destruct i;
    eauto using PeanoNat.Nat.lt_0_succ, Lt.lt_n_S, Lt.lt_S_n.
Qed.

Lemma extends_add : forall {A} (mt : list A) x,
  (add mt x) extends mt.
Proof.
  induction mt; eauto using @extends'.
Qed.

Lemma extends_refl : forall {A} (mt : list A),
  mt extends mt.
Proof.
  induction mt; auto using @extends'.
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

Lemma safe_preserves_inclusion : forall Gamma Gamma',
  Gamma includes Gamma' ->
  (safe Gamma) includes (safe Gamma').
Proof.
  unfold Map.includes', safe. intros * H *.
  destruct (Gamma k) eqn:E1; destruct (Gamma' k) eqn:E2;
  solve 
    [ intros F; inversion F
    | eapply H in E2; rewrite E1 in E2; inversion E2; subst; trivial
    ].
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

Lemma assignment_preserves_memory_typing : forall m mt t i,
  i < length m ->
  well_typed_memory mt m ->
  mt / empty |-- t is (get_typ mt i) ->
  well_typed_memory mt (set m i t).
Proof.
  intros * Hi [Hlen Htype1] Htype2. split.
  - rewrite Hlen. apply set_preserves_length.
  - intros j. destruct (PeanoNat.Nat.eqb i j) eqn:E.
    + apply PeanoNat.Nat.eqb_eq in E. subst.
      erewrite (get_set_involutive TM_Nil); auto.
    + apply PeanoNat.Nat.eqb_neq in E. subst.
      erewrite (get_set_i_neq_j TM_Nil); auto.
Qed.

Lemma update_safe_includes_safe_update : forall Gamma id T,
  (update (safe Gamma) id T) includes (safe (update Gamma id T)).
Proof.
  unfold Map.includes', update, Map.update', safe. intros *.
  destruct String.eqb; trivial.
  destruct is_safe_type; trivial.
  intros F. inversion F.
Qed.

Lemma substitution_preserves_typing : forall mt Gamma id t u T U,
  mt / (update Gamma id U) |-- t is T ->
  mt / empty |-- u is U ->
  mt / Gamma |-- [id := u] t is T.
Proof with eauto using context_weakening, context_weakening_empty,
  lookup_update_kneq, update_overwrite, update_permutation,
  update_safe_includes_safe_update.

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

Lemma add_preserves_well_typed_memories : forall mt m t T,
  well_typed_memory mt m ->
  mt / empty |-- t is T ->
  well_typed_memory (add mt T) (add m t).
Proof.
  intros * [Hlen H] Htype.
  unfold well_typed_memory.
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

Theorem preservation : forall m m' mt t t' eff T,
  mt / empty |-- t is T ->
  well_typed_memory mt m ->
  m / t --> eff / m' / t' ->
  exists mt',
    mt' extends mt /\
    mt' / empty |-- t' is T /\
    well_typed_memory mt' m'.
Proof.
  remember empty as Gamma.
  intros * Htype.
  generalize dependent t'.
  induction Htype;
  intros ?t' Hmem Hstep;
  inversion Hstep; subst;
  try solve
    [ match goal with
      | IH : _ -> _ -> _ -> _ -> exists mt', _ /\ _ /\ _,
        H  : _ / _ --> _ / _ / _ |- _ =>
          eapply IH in H; trivial; destruct H as [? [? [? ?]]];
          eexists; splits 3; eauto using memory_weakening, @typeof
      end
    | exists mt; splits 3; eauto using extends_refl, @typeof;
      match goal with H : _ / _ |-- _ is _ |- _ =>
        inversion H; subst;
        solve [ destruct Hmem; trivial
              | auto using assignment_preserves_memory_typing
              | eauto using substitution_preserves_typing
              ]
      end
    | exists (add mt E); inversion Hmem as [Hlen ?]; rewrite <- Hlen;
      splits 3; auto using extends_add, add_preserves_well_typed_memories;
      eauto using @typeof, length_l_lt_add, get_add_last
    ].
  (* LetVar *)
  - exists (add mt E). inversion Hmem as [Hlen ?]. rewrite <- Hlen.
    splits 3; auto using extends_add, add_preserves_well_typed_memories.
    eapply substitution_preserves_typing;
    eauto using extends_add, memory_weakening.
    assert (Haux : TY_Ref E = TY_Ref (get_typ (add mt E) (length mt))).
    { unfold get_typ. rewrite (get_add_last TY_Void). reflexivity. }
    rewrite Haux. auto using T_Loc, length_l_lt_add.
Qed.

Theorem progress : forall m mt t T,
  mt / empty |-- t is T ->
  well_typed_memory mt m ->
  (value t \/ exists m' t' eff, m / t --> eff / m' / t').
Proof.
  remember empty as Gamma. intros * Htype [Hlen Hmem].
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

Definition normal_form m t : Prop :=
  ~ exists m' t' eff, m / t --> eff / m' / t'.

Definition stuck m t : Prop := normal_form m t /\ ~ value t.

Corollary soundness : forall mt m m' t t' T,
  mt / empty |-- t is T ->
  well_typed_memory mt m ->
  m / t -->* m' / t' ->
  ~ (stuck m' t').
Proof.
  intros * ? ? Hmultistep [Hnormal_form ?]. generalize dependent mt.
  unfold normal_form in Hnormal_form. induction Hmultistep; intros.
  - assert (value t \/ exists m' t' eff, m / t --> eff / m' / t') as [? | ?];
    eauto using progress.
  - assert (exists mt',
      mt' extends mt /\
      mt' / empty |-- t is T /\
      well_typed_memory mt' m) as [? [? [? ?]]].
    eauto using preservation.
    assert (value t \/ exists m' t' eff, m / t --> eff / m' / t') as [? | ?];
    eauto using progress.
Qed.

(* ------------------------------------------------------------------------- *)
(* Concurrent Progress, Preservation & Soundness --------------------------- *)
(* ------------------------------------------------------------------------- *)

Definition get_ctx := get (@empty typ).

Definition empties (ths : list tm) :=
  List.repeat (@empty typ) (length ths).

Definition well_typed_threads mt Gammas ths := forall i,
  exists T, mt / (get_ctx Gammas i) |-- (get_tm ths i) is T.

Definition finished ths :=
  forall i, value (get_tm ths i).

Lemma empties_length : forall ths,
  length (empties ths) = length ths.
Proof.
  intros. unfold empties. induction ths.
  - reflexivity.
  - simpl. f_equal. auto.
Qed.

Lemma empties_get : forall ths i,
  get_ctx (empties ths) i = empty.
Proof.
  intros *. unfold get_ctx, empties. generalize dependent i.
  induction ths as [| ? ? IH]; intros i; destruct i; trivial.
  apply IH.
Qed.

Lemma empties_set : forall ths i t,
  empties (set ths i t) = empties ths.
Proof.
  intros. unfold empties. rewrite <- set_preserves_length. reflexivity.
Qed.

Lemma well_typed_threads_destruct : forall mt th ths,
  well_typed_threads mt (empties (th :: ths)) (th :: ths) ->
  well_typed_threads mt (empties ths) ths.
Proof.
  intros *. intros H i. specialize (H (S i)) as [T H].
  exists T. unfold get_tm, get_ctx in *. assumption.
Qed.

Lemma finished_nil : finished nil.
Proof.
  intros i. destruct i; apply V_Nil.
Qed.

Lemma finished_cons : forall th ths,
  value th ->
  finished ths ->
  finished (th :: ths).
Proof.
  intros th ths ? ? i. destruct i; unfold get_tm; simpl; trivial.
Qed.

Lemma cstep_cons : forall m m' th ths ths',
  m / ths ==> m' / ths' ->
  m / (th :: ths) ==> m' / (th :: ths').
Proof.
  intros * H. destruct H;
  repeat (
    try (  eapply CST_None  with (i := S i) (ths := th :: ths)
        || eapply CST_Spawn with (i := S i) (ths := th :: ths)
        );
    simpl; auto using lt_n_S;
    unfold get_tm; rewrite get_S_i; assumption
   ).
Qed.

Lemma step_preserves_thread_typing : forall mt m m' eff ths t i,
  m / get_tm ths i --> eff / m' / t ->
  well_typed_memory mt m ->
  well_typed_threads mt (empties ths) ths ->
  exists mt',
    mt' extends mt /\
    well_typed_threads mt' (empties (set ths i t)) (set ths i t) /\
    well_typed_memory mt' m'.
Proof.
  intros * Hstep Hmem Htypes.
  destruct (Htypes i) as [T Htype].
  rewrite empties_get in Htype.
  assert (exists mt',
            mt' extends mt /\
            mt' / empty |-- t is T /\
            well_typed_memory mt' m') as [? [? [? ?]]].
  { eauto using preservation. }
  eexists. splits 3; eauto.
  intros i'. rewrite empties_get. unfold get_tm.
  destruct (i =? i') eqn:E.
  + apply Nat.eqb_eq in E. subst.
    destruct (le_lt_dec (length ths) i').
    * rewrite get_set_default; eauto using T_Nil.
    * rewrite get_set_involutive; eauto.
  + apply Nat.eqb_neq in E. apply not_eq_sym in E.
    rewrite get_set_i_neq_j; trivial.
    destruct (le_lt_dec (length ths) i').
    * rewrite get_default; eauto using T_Nil.
    * specialize (Htypes i') as [? ?].
      unfold get_tm in *. rewrite empties_get in *.
      eauto using memory_weakening.
Qed.

Lemma spawn_preserves_thread_typing : forall mt mt' ths block T,
  mt' extends mt ->
  mt / empty |-- block is T ->
  well_typed_threads mt (empties ths) ths ->
  well_typed_threads mt' (empties (add ths block)) (add ths block).
Proof.
  intros * Hext Htype Htypes i.
  destruct (lt_eq_lt_dec i (length ths)) as [[? | ?] | ?]; unfold get_tm.
  - specialize (Htypes i) as [T' ?]. exists T'.
    rewrite get_add_lt; trivial. rewrite empties_get in *.
    eauto using memory_weakening.
  - exists T. subst. rewrite get_add_last.
    rewrite empties_get. eauto using memory_weakening.
  - rewrite get_add_gt; trivial. rewrite empties_get. eauto using T_Nil.
Qed.

Lemma spawn_block_has_type: forall mt m m' t t' block T,
  mt / empty |-- t is T ->
  m / t --> EF_Spawn block / m' / t' ->
  exists B, mt / empty |-- block is B.
Proof.
  intros ? ? ? t. induction t; intros * Htype Hstep;
  inversion Hstep; inversion Htype; subst; eauto.
Qed.

Theorem cpreservation : forall ths ths' m m' mt,
  well_typed_threads mt (empties ths) ths ->
  well_typed_memory mt m ->
  m / ths ==> m' / ths' ->
  exists mt',
    mt' extends mt /\
    well_typed_threads mt' (empties ths') ths' /\
    well_typed_memory mt' m'.
Proof.
  intros * Htypes Hmem Hcstep. induction Hcstep.
  - eauto using step_preserves_thread_typing.
  - rewrite add_set_comm; trivial.
    eapply step_preserves_thread_typing; eauto.
    + unfold get_tm in *. rewrite get_add_lt; eauto.
    + destruct (Htypes i) as [T Htype]. rewrite empties_get in Htype.
      assert (exists B, mt / empty |-- block is B) as [? ?].
      { eauto using spawn_block_has_type. }
      eauto using spawn_preserves_thread_typing, extends_refl.
Qed.

Theorem cprogress : forall ths m mt,
  well_typed_memory mt m ->
  well_typed_threads mt (empties ths) ths ->
  (finished ths \/ exists m' ths', m / ths ==> m' / ths').
Proof.
  intros * Hmem Htypes.
  induction ths as [| th ths IH].
  - left. apply finished_nil.
  - apply well_typed_threads_destruct in Htypes as Htypes'.
    specialize (IH Htypes') as [IH | [m' [ths' IH]]].
    + destruct (is_value th) eqn:E.
      * left. apply value_equivalence in E. eauto using finished_cons.
      * right. specialize (Htypes 0) as [T Htype]. rewrite empties_get in Htype.
        assert (value th \/ exists m' th' eff, m / th --> eff / m' / th')
        as [F | [m' [th' [eff Hstep]]]].
        { eauto using progress. }
        ** apply value_equivalence in F. rewrite E in F. discriminate.
        ** destruct eff; eauto using cstep, Nat.lt_0_succ.
    + right. eauto using cstep_cons.
Qed.

Definition cnormal_form m th : Prop :=
  ~ exists m' th', m / th ==> m' / th'.

Definition cstuck m th : Prop := cnormal_form m th /\ ~ finished th.

Corollary csoundness : forall mt m m' ths ths',
  well_typed_memory mt m ->
  well_typed_threads mt (empties ths) ths ->
  m / ths ==>* m' / ths' ->
  ~ (cstuck m' ths').
Proof.
  intros * ? ? Hmultistep [Hnormal_form ?]. generalize dependent mt.
  unfold cnormal_form in Hnormal_form. induction Hmultistep; intros.
  - assert (finished ths \/ exists m' ths', m / ths ==> m' / ths') as [? | ?];
    eauto using cprogress.
  - assert (exists mt',
      mt' extends mt /\
      well_typed_threads mt' (empties ths) ths /\
      well_typed_memory mt' m) as [? [? [? ?]]].
    { eauto using cpreservation. }
    assert (finished ths \/ exists m' ths', m / ths ==> m' / ths') as [? | ?];
    eauto using cprogress.
Qed.
