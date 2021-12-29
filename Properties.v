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

Lemma value_does_not_step : forall v eff t,
  value v -> ~ (v --[eff]--> t).
Proof.
  intros * Hv Hstep. destruct Hv; inversion Hstep.
Qed.

Theorem deterministic_step : forall t eff t1 t2,
  t --[eff]--> t1 ->
  t --[eff]--> t2 ->
  t1 = t2.
Proof.
  intros * Hstep1. generalize dependent t2.
  induction Hstep1; intros * Hstep2; inversion Hstep2; subst;
  try solve
    [ congruence
    | match goal with
      | Hstep : ?v --[ _ ]--> _ , Hv : value ?v |- _ =>
          eapply value_does_not_step in Hstep; eauto; contradiction
      | F : TM_Nil         --[ _ ]--> _ |- _ => inversion F
      | F : TM_Num _       --[ _ ]--> _ |- _ => inversion F
      | F : TM_Arr _ _     --[ _ ]--> _ |- _ => inversion F
      | F : TM_Fun _ _ _ _ --[ _ ]--> _ |- _ => inversion F
      | F : TM_Loc _       --[ _ ]--> _ |- _ => inversion F
      | H : forall x, _ --[ _ ]--> x -> _ = x |- _ => erewrite H; eauto
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

Inductive well_behaved_effect : effect -> mem -> Prop :=
  | well_behaved_none : forall m,
    well_behaved_effect EF_None m

  | well_behaved_spawn : forall m block,
    well_behaved_effect (EF_Spawn block) m

  | well_behaved_alloc : forall m v,
    well_behaved_effect (EF_Alloc (length m) v) m

  | well_behaved_load : forall m addr,
    well_behaved_effect (EF_Load addr (get_tm m addr)) m

  | well_behaved_store : forall m addr v,
    addr < length m ->
    well_behaved_effect (EF_Store addr v) m
  .

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

Lemma update_safe_includes_safe_update : forall Gamma id T,
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

Lemma concurrent_memory_weakening : forall mt mt' ths,
  mt' extends mt ->
  well_typed_threads mt ths ->
  well_typed_threads mt' ths.
Proof.
  intros * Hext Hths. intros i.
  specialize (Hths i) as [? ?]. eexists.
  eauto using memory_weakening.
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

Lemma alloc_value_has_type : forall mt t t' addr v T,
  mt / empty |-- t is T ->
  t --[EF_Alloc addr v]--> t' ->
  exists V, mt / empty |-- v is V.
Proof.
  remember empty as Gamma.
  intros * Htype. generalize dependent t'.
  induction Htype; intros * Hstep; inversion Hstep; subst; eauto.
Qed.

Lemma store_value_has_type : forall mt t t' addr v T,
  mt / empty |-- t is T ->
  t --[EF_Store addr v]--> t' ->
  mt / empty |-- v is (get_typ mt addr).
Proof.
  remember empty as Gamma.
  intros * Htype. generalize dependent t'.
  induction Htype; intros * Hstep;
  inversion Hstep; subst; eauto;
  solve [match goal with
    | H1 : _ / _ |-- ?v is _,
      H2 : _ / _ |-- _  is _
      |- _ / _ |-- ?v is _ =>
        inversion H2; subst; eauto
    end].
Qed.

Lemma spawn_block_has_type : forall mt t t' block T,
  mt / empty |-- t is T ->
  t --[EF_Spawn block]--> t' ->
  exists B, mt / empty |-- block is B.
Proof.
  remember empty as Gamma.
  intros * Htype. generalize dependent t'.
  induction Htype; intros * Hstep; inversion Hstep; subst; eauto.
Qed.

Lemma store_preserves_well_typed_memory : forall m mt t i,
  i < length m ->
  well_typed_memory mt m ->
  mt / empty |-- t is (get_typ mt i) ->
  well_typed_memory mt (set m i t).
Proof.
  intros * ? [Hlen ?] ?. split.
  - rewrite Hlen. apply set_preserves_length.
  - intros j. destruct (i =? j) eqn:E.
    + apply Nat.eqb_eq in E. subst. erewrite (get_i_set_i TM_Nil); auto.
    + apply Nat.eqb_neq in E. erewrite (get_i_set_j TM_Nil); auto.
Qed.

Lemma alloc_preserves_well_typed_memory : forall mt m t T,
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

Lemma step_preserves_well_typed_threads : forall mt ths t T i,
  i < length ths ->
  well_typed_threads mt ths ->
  mt / empty |-- t is T ->
  well_typed_threads mt (set ths i t).
Proof.
  intros * Hlen Htype Hstep.
  intros i'. destruct (i =? i') eqn:E.
  - apply Nat.eqb_eq in E. subst.
    rewrite (get_i_set_i TM_Nil); eauto.
  - apply Nat.eqb_neq in E. apply not_eq_sym in E.
    rewrite (get_i_set_j TM_Nil); eauto.
Qed.

Lemma spawn_preserves_well_typed_threads : forall mt ths t T,
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

Definition is_alloc_or_load eff :=
  match eff with
  | EF_Alloc _ _ | EF_Load _ _ => true
  | _ => false
  end.

Lemma limited_preservation : forall mt m t t' eff T,
  well_typed_memory mt m ->
  mt / empty |-- t is T ->
  t --[eff]--> t' ->
  is_alloc_or_load eff = false ->
  mt / empty |-- t' is T.
Proof.
  remember empty as Gamma.
  intros * [Hlen Hmem] Htype Hstep Heff.
  generalize dependent t'.
  induction Htype; intros * Hstep; inversion Hstep; subst;
  solve
    [ discriminate Heff
    | eauto using substitution_preserves_typing, @typeof
    | match goal with
      | Htype : _ / _ |-- _ is _ |- _ =>
        inversion Htype; subst;
        eauto using substitution_preserves_typing, @typeof
      end
    ].
Qed.

Lemma alloc_preservation : forall mt t t' v T V,
  mt / empty |-- t is T ->
  mt / empty |-- v is V ->
  t --[EF_Alloc (length mt) v]--> t' ->
  (add mt V) / empty |-- t' is T.
Proof.
  remember empty as Gamma.
  intros * Htype ? Hstep. generalize dependent t'.
  assert (R : forall T, T = get_typ (add mt T) (length mt)).
  { intros. eauto using get_add_last. }
  induction Htype; intros * Hstep; inversion Hstep; subst;
  eauto using @typeof, extends_add, memory_weakening;
  match goal with
  | H1 : mt / _ |-- v is ?T1, H2 : mt / _ |-- v is ?T2 |- _ =>
    eapply (deterministic_typing _ _ _ T1 T2) in H1; eauto; subst
  end;
  try match goal with
  |- _ / _ |-- _ is _ ?T =>
    rewrite (R T); eauto using @typeof, length_lt_add
  end.
  - eapply substitution_preserves_typing;
    eauto using extends_add, memory_weakening.
    assert (R' : forall T, TY_Ref T = TY_Ref (get_typ (add mt T) (length mt))).
    { intros. f_equal. eauto using get_add_last. }
    rewrite R'. eauto using @typeof, length_lt_add.
Qed.

Lemma load_preservation : forall mt m t t' addr T,
  well_typed_memory mt m ->
  mt / empty |-- t is T ->
  t --[EF_Load addr (get_tm m addr)]--> t' ->
  mt / empty |-- t' is T.
Proof.
  remember empty as Gamma.
  intros * [Hlen Hmem] Htype Hstep. generalize dependent t'.
  induction Htype; intros * Hstep; inversion Hstep; subst;
  try solve [ eauto using @typeof
            | repeat match goal with 
              | H : _ / _ |-- _ is _ |- _ => inversion H; subst; eauto
              end
            ].
Qed.

(* ------------------------------------------------------------------------- *)
(* Preservation ------------------------------------------------------------ *)
(* ------------------------------------------------------------------------- *)

Theorem preservation : forall mt m m' ths ths' ceff,
  well_typed_program mt m ths ->
  m / ths ==> m' / ths' # ceff ->
  exists mt',
    mt' extends mt /\
    well_typed_program mt' m' ths'.
Proof.
  intros * [Hmem Hths] Hcstep.
  inversion Hcstep; subst; destruct (Hths i) as [? ?].
  (* None *)
  - eexists. splits 3; eauto using extends_refl.
    intros i'. destruct (i =? i') eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite (get_i_set_i TM_Nil); trivial.
      specialize (Hths i') as [? ?]. eexists.
      eauto using limited_preservation.
    + apply Nat.eqb_neq in E. apply not_eq_sym in E.
      rewrite (get_i_set_j TM_Nil); trivial.
  (* Alloc *)
  - rewrite <- (proj1 Hmem) in *.
    assert (exists V, mt / empty |-- v is V) as [V ?].
    { eauto using alloc_value_has_type. }
    exists (add mt V). splits 3;
    eauto using extends_add,
      alloc_preserves_well_typed_memory,
      step_preserves_well_typed_threads,
      concurrent_memory_weakening,
      alloc_preservation.
  (* Load *)
  - eexists. splits 3; eauto using extends_refl.
    eauto using step_preserves_well_typed_threads, load_preservation.
  (* Store *)
  - eexists. splits 3; eauto using extends_refl;
    eauto using store_preserves_well_typed_memory,
      store_value_has_type,
      step_preserves_well_typed_threads,
      limited_preservation.
  (* Spawn *)
  - eexists. splits 3; eauto using extends_refl.
    assert (exists B, mt / empty |-- block is B) as [? ?].
    { eauto using spawn_block_has_type. }
    eauto using spawn_preserves_well_typed_threads,
      step_preserves_well_typed_threads,
      limited_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* Progress ---------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Lemma well_typed_threads_tail : forall mt th ths,
  well_typed_threads mt (th :: ths) ->
  well_typed_threads mt ths.
Proof.
  intros * Hths. intros i.
  specialize (Hths (S i)) as [T Htype].
  eexists. eauto.
Qed.

Lemma concurrent_step_weakening : forall m m' th ths ths' ceff,
  m / ths ==> m' / ths' # ceff ->
  exists ceff', m / (th :: ths) ==> m' / (th :: ths') # ceff'.
Proof.
  intros * Hcstep.
  inversion Hcstep; subst;
  solve [rewrite set_tail || rewrite add_set_tail; eauto using cstep, lt_n_S].
Qed.

Lemma memory_length : forall mt m i,
  well_typed_memory mt m ->
  (i < length mt) -> (i < length m).
Proof.
  intros * [Hlen _]. rewrite Hlen. trivial.
Qed.

Lemma limited_progress : forall mt m t T,
  well_typed_memory mt m ->
  mt / empty |-- t is T ->
  value t \/ exists t' eff',
    t --[eff']--> t' /\
    well_behaved_effect eff' m.
Proof.
  remember empty as Gamma.
  intros * Hmem Htype.
  induction Htype; subst; auto using value; right;
  try match goal with F : lookup empty _ = Some _ |- _ => inversion F end;
  repeat match goal with
    IH : _ -> _ \/ _ |- _ => specialize (IH eq_refl) as [? | [? [? [? ?]]]]
  end;
  try solve [eexists; eexists; split; eauto using step, well_behaved_effect];
  repeat match goal with
    Hv : value ?t , Htype : _ / _ |-- ?t is _ |- _ =>
      destruct Hv; inversion Htype; subst
  end;
  eexists; eexists; split;
  eauto using memory_length, step, value, well_behaved_effect.
Qed.

Theorem progress : forall m mt ths,
  well_typed_program mt m ths ->
  (finished ths \/ exists m' ths' ceff, m / ths ==> m' / ths' # ceff).
Proof.
  intros * [Hmem Hths].
  induction ths as [| th ths IH].
  - left. intros i. destruct i; auto using value.
  - destruct (is_value th) eqn:E.
    + apply value_equivalence_true in E.
      destruct (IH (well_typed_threads_tail _ _ _ Hths)) as [? | [? [? [? ?]]]].
      * left. intros i. destruct i; eauto.
      * right. eexists. eexists. eauto using concurrent_step_weakening.
    + apply value_equivalence_false in E. right.
      specialize (IH (well_typed_threads_tail _ _ _ Hths)) as [? | IH].
      * destruct (Hths 0) as [T Htype].
        unfold get_tm in Htype. simpl in Htype.
        assert (value th \/
          exists th' eff, th --[eff]--> th' /\ well_behaved_effect eff m)
        as [? | [? [eff [? Heff]]]];
        eauto using limited_progress; try contradiction.
        destruct eff; inversion Heff; subst;
        eauto using cstep, Nat.lt_0_succ.
      * specialize IH as [? [? [? ?]]].
        eexists. eexists. eauto using concurrent_step_weakening.
Qed.

(*
Corollary soundness : forall mt m m' ths ths',
  well_typed_program mt m ths ->
  m / ths ==>* m' / ths' ->
  ~ (cstuck m' ths').
Proof.
Qed.
*)
