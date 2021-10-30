From Elo Require Export Array.
From Elo Require Export Map.
From Elo Require Export Core.

(* Auxiliary Lemmas *)

Definition well_typed_memory (mt : list typ) (m : mem) :=
  length mt = length m /\
  (forall i, mt / empty |-- (get_tm m i) is (get_typ mt i)).

Inductive extends' : list typ -> list typ -> Prop :=
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
    + unfold get_typ, get, List.nth_default.
      simpl in *. eauto using Lt.lt_S_n.
Qed.

Lemma extends_length : forall i mt mt',
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

Lemma extends_add : forall mt x,
  (add mt x) extends mt.
Proof.
  induction mt; eauto using extends'.
Qed.

Lemma extends_refl : forall mt,
  mt extends mt.
Proof.
  induction mt; auto using extends'.
Qed.

Lemma memory_weakening : forall mt mt' Gamma t T, 
  mt extends mt' ->
  mt' / Gamma |-- t is T ->  
  mt  / Gamma |-- t is T.
Proof.
  intros * Hext Htype.
  induction Htype; eauto using @typeof.
  assert (i < length mt). { eauto using extends_length. }
  erewrite extends_lookup; auto using T_Loc.
Qed.

Lemma context_weakening : forall mt Gamma Gamma' t T,
  Gamma includes Gamma' ->
  mt / Gamma' |-- t is T ->
  mt / Gamma  |-- t is T.
Proof.
  intros * Hinc Htype.
  generalize dependent Gamma.
  induction Htype; intros * Hinc;
  eauto 6 using @typeof, update_preserves_inclusion.
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

Lemma substitution_preserves_typing : forall mt Gamma id t u T U,
  mt / (update Gamma id U) |-- t is T ->
  mt / empty |-- u is U ->
  mt / Gamma |-- [id := u] t is T.
Proof.
  intros * Ht Hu.
  generalize dependent T.
  generalize dependent Gamma.
  induction t; intros * Ht;
  inversion Ht; simpl; subst;
  eauto using @typeof.
  - destruct String.eqb eqn:E.
    + apply String.eqb_eq in E. subst.
      rewrite lookup_update_involutive in H1.
      inversion H1. subst.
      apply context_weakening_empty. assumption.
    + apply T_Id_Val.
      rewrite <- H1.
      apply String.eqb_neq in E.
      symmetry. apply lookup_update_idempotent. assumption.
  - destruct String.eqb eqn:E.
    + apply String.eqb_eq in E. subst.
      apply context_weakening_empty.
      rewrite lookup_update_involutive in H1.
      inversion H1. subst.
      assumption.
    + apply String.eqb_neq in E.
      apply T_Id_Var.
      rewrite <- H1.
      symmetry. apply lookup_update_idempotent.
      assumption.
  - destruct String.eqb eqn:E in *; apply T_LetVal; eauto.
    + apply String.eqb_eq in E. subst.
      eauto using context_weakening, update_overwrite.
    + apply String.eqb_neq in E.
      eauto using context_weakening, update_permutation.
  - destruct String.eqb eqn:E in *; apply T_LetVar; eauto.
    + apply String.eqb_eq in E. subst.
      eauto using context_weakening, update_overwrite.
    + apply String.eqb_neq in E.
      eauto using context_weakening, update_permutation.
  - apply T_LetFun.
    + destruct String.eqb eqn:E.
      * apply String.eqb_eq in E. subst.
        eauto using context_weakening, update_overwrite.
      * apply String.eqb_neq in E.
        eauto using context_weakening, update_permutation.
    + destruct String.eqb eqn:E.
      * apply String.eqb_eq in E. subst.
        eauto using context_weakening, update_overwrite.
      * apply String.eqb_neq in E.
        eauto using context_weakening, update_permutation.
Qed.

Lemma length_add : forall {A B} (l1 : list A) (l2 : list B) a b,
  length l1 = length l2 ->
  length (add l1 a) = length (add l2 b).
Proof.
Admitted.

Theorem preservation : forall m m' mt t t' T,
  mt / empty |-- t is T ->
  well_typed_memory mt m ->
  m / t --> m' / t' ->
  exists mt',
    mt' extends mt /\
    mt' / empty |-- t' is T /\
    well_typed_memory mt' m'.
Proof.
  remember empty as Gamma.
  intros * Htype.
  generalize dependent t'.
  induction Htype; intros ?t' Hmem Hstep;
  inversion Hstep; subst.
  (* T_Asg *)
  * eapply IHHtype2 in H4; trivial.
    destruct H4 as [mt' [Hext [Htype' Hmem']]].
    exists mt'. split; try split; eauto using memory_weakening, T_Asg.
  * eapply IHHtype1 in H5; trivial.
    destruct H5 as [mt' [Hext [Htype' Hmem']]].
    exists mt'. split; try split; eauto using memory_weakening, T_Asg.
  * exists mt. split. apply extends_refl. split. apply T_Nil.
    eapply assignment_preserves_memory_typing; auto.
    inversion Htype1. subst. eauto.
  (* T_Call *)
  * eapply IHHtype2 in H4; trivial.
    destruct H4 as [mt' [Hextends [Htype' Hmem']]].
    exists mt'. split; trivial.
    split; try eapply T_Call; eauto using memory_weakening.
  * exists mt. inversion Htype1. subst.
    split; only 1 : apply extends_refl.
    split; only 2 : trivial.
    eapply substitution_preserves_typing; eauto.
    admit.
  (* T_Seq *)
  * specialize (IHHtype1 eq_refl t2 Hmem H4).
    destruct IHHtype1 as [mt' [? [? ?]]].
    exists mt'. split. assumption.
    split; eauto using T_Seq, memory_weakening.
  * exists mt. split. apply extends_refl. split; assumption.
  (* T_LetVal *)
  * specialize (IHHtype1 eq_refl e' Hmem H6).
    destruct IHHtype1 as [mt' [Hextends [Htype' Hmem']]].
    exists mt'. split. assumption.
    split; eauto using T_LetVal, memory_weakening.
  * exists mt. split. apply extends_refl. split; auto.
    eapply substitution_preserves_typing; eauto.
  (* T_LetVar *)
  * specialize (IHHtype1 eq_refl e' Hmem H6).
    destruct IHHtype1 as [mt' [Hextends [Htype' Hmem']]].
    exists mt'. split. assumption.
    split; eauto using T_LetVar, memory_weakening.
  * exists (add mt E). split. apply extends_add. split.
    ** admit.
    ** destruct Hmem as [Hlen Htype]. admit. (* easy *)
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
Admitted.

Theorem progress : forall D m mt t T,
  D / mt / empty |-- t is T ->
  well_typed_memory D mt m ->
  (value t \/ exists D' m' t', D / m / t --> D' / m' / t').
Admitted.
