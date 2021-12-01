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
  remember empty as Gamma.
  intros * Htype Hmem.
  induction Htype; subst; auto using value; right;
  try solve
    [ match goal with
      | Htype : _ / _ |-- _ is _, IH : _ -> _ \/ _ _ _ |- _ =>
        destruct (IH eq_refl) as [Hv | [? [? [? ?]]]];
        try (destruct Hv; inversion Htype; subst);
        eexists; eexists; eexists; eauto using step, value
      end
    ].
  (* ArrIdx *)
  - destruct (IHHtype1 eq_refl) as [Hv1 | [? [? [? ?]]]];
    destruct (IHHtype2 eq_refl) as [Hv2 | [? [? [? ?]]]];
    try (eexists; eexists; eexists; eauto using step; fail).
    destruct Hv1; inversion Htype1; subst.
    destruct Hv2; inversion Htype2; subst.
    eexists. eexists. eexists. eauto using step.
  - destruct (IHHtype1 eq_refl) as [Hv1 | [? [? [? ?]]]];
    destruct (IHHtype2 eq_refl) as [Hv2 | [? [? [? ?]]]];
    try (eexists; eexists; eauto using step; fail).
    destruct Hv1; inversion Htype1; subst.
    destruct Hv2; inversion Htype2; subst.
    eexists. eexists. eauto using step.
  (* Id *)
  - inversion H.
  - inversion H.
  (* Asg *)
  - destruct (IHHtype1 eq_refl) as [Hv | [? [? [? ?]]]];
    destruct (IHHtype2 eq_refl) as [?  | [? [? [? ?]]]];
    try (eexists; eexists; eauto using step; fail).
    destruct Hv; inversion Htype1. subst.
    destruct Hmem as [Hlen ?]. rewrite Hlen in H3.
    eexists. eexists. eauto using step.
  (* ArrAsg *)
  - destruct (IHHtype1 eq_refl) as [Hv | [? [? [? ?]]]];
    destruct (IHHtype2 eq_refl) as [?  | [? [? [? ?]]]];
    destruct (IHHtype3 eq_refl) as [?  | [? [? [? ?]]]];
    try (eexists; eexists; eauto using step; fail).
    destruct Hv; inversion Htype1; subst.
    destruct Hmem as [Hlen ?]. rewrite Hlen in H6.
    eexists. eexists. eauto using step.
  (* Call *)
  - destruct (IHHtype1 eq_refl) as [Hv | [? [? [? ?]]]];
    destruct (IHHtype2 eq_refl) as [?  | [? [? [? ?]]]];
    try (eexists; eexists; eauto using step; fail).
    destruct Hv; inversion Htype1; subst.
    eexists; eexists; eauto using step.
(*
  - destruct (IHHtype1 eq_refl) as [Hv | [? [? [? ?]]]];
    destruct (IHHtype2 eq_refl) as [?  | [? [? [? ?]]]];
    eexists; eexists; eauto using step.
*)
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
  intros * ? ? Hmultistep [Hnormal_form ?].
  generalize dependent mt.
  unfold normal_form in Hnormal_form.
  induction Hmultistep; intros.
  - assert (Hprogress : value t \/ exists m' t' eff, m / t --> eff / m' / t').
    eauto using progress. destruct Hprogress; eauto.
  - assert (Hpreservation : exists mt',
      mt' extends mt /\
      mt' / empty |-- t is T /\
      well_typed_memory mt' m).
    eauto using preservation. decompose record Hpreservation.
    assert (Hprogress : value t \/ exists m' t' eff, m / t --> eff / m' / t').
    eauto using progress. destruct Hprogress; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* Concurrent Progress, Preservation & Soundness --------------------------- *)
(* ------------------------------------------------------------------------- *)

Definition get_ctx := get (@empty typ).

Definition empties (threads : list tm) :=
  List.repeat (@empty typ) (length threads).

Lemma empties_length : forall threads,
  length (empties threads) = length threads.
Proof.
  intros. unfold empties. induction threads.
  - reflexivity.
  - simpl. f_equal. auto.
Qed.

Lemma empties_get : forall threads i,
  get_ctx (empties threads) i = empty.
Proof.
  intros *. unfold get_ctx, empties. generalize dependent i.
  induction threads as [| ? ? IH]; intros i; destruct i; trivial.
  apply IH.
Qed.

Lemma empties_set : forall threads i t,
  empties (set threads i t) = empties threads.
Proof.
  intros. unfold empties. rewrite <- set_preserves_length. reflexivity.
Qed.

Lemma empties_head : forall th ths,
  empties (th :: ths) = empty :: empties (ths).
Proof.
  intros. reflexivity.
Qed.

Definition well_typed_threads mt Gammas threads := forall i,
  length Gammas = length threads ->
  exists T, mt / (get_ctx Gammas i) |-- (get_tm threads i) is T.

Lemma well_typed_threads_destruct : forall Gamma Gammas ths th mt,
  well_typed_threads mt (Gamma :: Gammas) (th :: ths) ->
  well_typed_threads mt Gammas ths.
Proof.
  unfold well_typed_threads. simpl.
  intros *. intros H i Hlen.
  eapply eq_S in Hlen. specialize (H (S i) Hlen) as [T H].
  exists T. unfold get_tm, get_ctx in *. simpl in H. assumption.
Qed.

Definition finished threads :=
  forall i, value (get_tm threads i).

Lemma cstep_cons : forall m m' th ths ths',
  m / ths ==> m' / ths' ->
  m / (th :: ths) ==> m' / (th :: ths').
Proof.
  intros * H. induction H.
  - apply (CST_None (S i) _ _ _ (th :: threads)).
    unfold get_tm. rewrite get_S_i. assumption.
  - apply (CST_Spawn (S i) _ m' _ _ (th :: threads)).
    + simpl. auto using lt_n_S.
    + unfold get_tm. rewrite get_S_i. assumption.
Qed.

Lemma step_preserves_thread_typing : forall mt m m' eff threads t i,
  m / get_tm threads i --> eff / m' / t ->
  well_typed_memory mt m ->
  well_typed_threads mt (empties threads) threads ->
  exists mt',
    mt' extends mt /\
    well_typed_threads mt' (empties (set threads i t)) (set threads i t) /\
    well_typed_memory mt' m'.
Proof.
  intros * Hstep Hmem Hctype.
  destruct (Hctype i (empties_length threads)) as [T Htype].
  rewrite empties_get in Htype.
  assert (Preservation : exists mt',
            mt' extends mt /\
            mt' / empty |-- t is T /\
            well_typed_memory mt' m').
  { eauto using preservation. }
  destruct Preservation as [? [? [? ?]]].
  eexists. splits 3; eauto.
  intros i' ?. rewrite empties_get. unfold get_tm.
  destruct (i =? i') eqn:E.
  + apply Nat.eqb_eq in E. subst.
    destruct (le_lt_dec (length threads) i').
    * rewrite get_set_default; trivial. exists TY_Void. apply T_Nil.
    * rewrite get_set_involutive; trivial. exists T. eauto.
  + apply Nat.eqb_neq in E. apply not_eq_sym in E.
    rewrite get_set_i_neq_j; trivial.
    destruct (le_lt_dec (length threads) i').
    * rewrite get_default; trivial. exists TY_Void. apply T_Nil.
    * specialize (Hctype i' (empties_length threads)) as [? ?].
      unfold get_tm in *. rewrite empties_get in *.
      eexists. eauto using memory_weakening.
Qed.

Lemma spawn_preserves_thread_typing : forall mt mt' threads block T,
  mt' extends mt ->
  mt / empty |-- block is T ->
  well_typed_threads mt (empties threads) threads ->
  well_typed_threads mt' (empties (add threads block)) (add threads block).
Proof.
  intros * Hext Htype Hctype i Hlen.
  destruct (lt_eq_lt_dec i (length threads)) as [[? | ?] | ?].
  - specialize (Hctype i (empties_length threads)) as [T' Htype'].
    exists T'. unfold get_tm. rewrite get_add_lt; trivial.
    rewrite empties_get in *. eauto using memory_weakening.
  - exists T. unfold get_tm. subst. rewrite get_add_last.
    rewrite empties_get in *. eauto using memory_weakening.
  - unfold get_tm. rewrite get_add_gt; trivial.
    rewrite empties_get. exists TY_Void. apply T_Nil.
Qed.

Lemma spawn_block_has_type: forall mt m m' t t' block T,
  mt / empty |-- t is T ->
  m / t --> EF_Spawn block / m' / t' ->
  exists B, mt / empty |-- block is B.
Proof.
  intros ? ? ? t. induction t; intros * Htype Hstep;
  inversion Hstep; inversion Htype; eauto. subst.
  eexists. eauto.
Qed.

Theorem cpreservation : forall threads threads' m m' mt,
  well_typed_threads mt (empties threads) threads ->
  well_typed_memory mt m ->
  m / threads ==> m' / threads' ->
  exists mt',
    mt' extends mt /\
    well_typed_threads mt' (empties threads') threads' /\
    well_typed_memory mt' m'.
Proof.
  intros * Hthreads Hmem Hcstep. induction Hcstep.
  - eauto using step_preserves_thread_typing.
  - rewrite add_set_comm; trivial.
    eapply step_preserves_thread_typing; eauto.
    + unfold get_tm in *. rewrite get_add_lt; eauto.
    + destruct (Hthreads i (empties_length threads)) as [T Htype].
      rewrite empties_get in Htype.
      assert (Hblock : exists B, mt / empty |-- block is B).
      { eauto using spawn_block_has_type. }
      destruct Hblock.
      eauto using spawn_preserves_thread_typing, extends_refl.
Qed.

Theorem cprogress : forall threads m mt,
  well_typed_memory mt m ->
  well_typed_threads mt (empties threads) threads ->
  (finished threads \/ exists m' threads', m / threads ==> m' / threads').
Proof.
  intros * Hmem Hth.
  induction threads as [| th ths IH].
  - left. intros i. destruct i; apply V_Nil.
  - rewrite empties_head in Hth.
    apply well_typed_threads_destruct in Hth as Hth'.
    specialize (IH Hth') as [IH | [m' [threads' IH]]].
    + destruct (is_value th) eqn:E.
      * left. apply value_equivalence in E.
        intros i. destruct i; unfold get_tm; simpl; trivial.
      * right.
        specialize (Hth 0). simpl in Hth.
        assert (Hlen : S (length (empties ths)) = S (length ths)).
        { f_equal. apply empties_length. }
        specialize (Hth Hlen) as [T Htype].
        unfold get_ctx, get_tm in Htype. simpl in Htype.
        assert (value th \/ exists m' th' eff, m / th --> eff / m' / th').
        { eauto using progress. }
        destruct H as [F | [m' [th' [eff Hstep]]]].
        ** apply value_equivalence in F. rewrite E in F. discriminate.
        ** destruct eff.
          *** eexists. eexists. eauto using (CST_None 0).
          *** eexists. eexists. eauto using (CST_Spawn 0), Nat.lt_0_succ.
    + right. exists m'. exists (th :: threads'). eauto using cstep_cons.
Qed.
