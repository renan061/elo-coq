From Elo Require Export Array.
From Elo Require Export Map.
From Elo Require Export Core.

(* Auxiliary Lemmas *)

Definition well_typed_memory D (mt : list typ) (m : mem) :=
  length mt = length m /\
  (forall i, D / mt / (empty, empty) |- (get_tm m i) is (get_typ mt i)).

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

Lemma assignment_preserves_memory_typing : forall D m mt t i,
  i < length mt ->
  well_typed_memory D mt m ->
  D / mt / (empty, empty) |- t is (get_typ mt i) ->
  well_typed_memory D mt (set m i t).
Proof.
  intros * Hi [Hlen Htype1] Htype2. split.
  - rewrite Hlen. apply set_preserves_length.
  - intros j. destruct (PeanoNat.Nat.eqb i j) eqn:E.
    + apply PeanoNat.Nat.eqb_eq in E. subst.
      rewrite Hlen in *.
      erewrite (get_set_involutive TM_Nil); auto.
    + apply PeanoNat.Nat.eqb_neq in E. subst.
      erewrite (get_set_i_neq_j TM_Nil); auto.
Qed.

Lemma aux : forall id id' T T' D mt Delta Gamma,
  id <> id' ->
  (D / mt / (Delta, Gamma) |- TM_Id id is T <->
  D / mt / (Delta, update Gamma id' T') |- TM_Id id is T).
Proof.
  intros *.
Admitted.

Lemma aux2 : forall id U V D mt Delta Gamma t T,
  D / mt / (Delta, update (update Gamma id U) id V) |- t is T ->
  D / mt / (Delta, update Gamma id V) |- t is T.
Proof.
Admitted.

Lemma gamma_weakening : forall D mt Gamma Gamma' t T,
  Gamma includes Gamma' ->
  D / mt / (empty, Gamma') |- t is T ->
  D / mt / (empty, Gamma)  |- t is T.
Proof.
  intros * Hinc Htype.
  remember (empty, Gamma)  as Context.  
  remember (empty, Gamma') as Context'.
  generalize dependent Gamma.
  induction Htype; intros * Hinc Hc; subst;
  inversion HeqContext'; subst;
  eauto using @typeof.
  - inversion HeqContext'. subst.
    unfold lookup, empty, Map.empty' in H.
    discriminate H.
  - eapply T_Call.
    + apply H.
    + apply (IHHtype1 eq_refl Gamma0 Hinc eq_refl).
    + apply (IHHtype2 eq_refl Gamma0 Hinc eq_refl).
  (* TODO : remover par do contexto *)
Qed.

(*
Lemma weakening : ∀ Gamma Gamma' ST t T,
     inclusion Gamma Gamma' →
     Gamma ; ST ⊢ t \in T →
     Gamma' ; ST ⊢ t \in T.
Proof.
  intros Gamma Gamma' ST t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
Qed.
Lemma weakening_empty : ∀ Gamma ST t T,
     empty ; ST ⊢ t \in T →
     Gamma ; ST ⊢ t \in T.
Proof.
  intros Gamma ST t T.
  eapply weakening.
  discriminate.
Qed.
*)

Lemma substitution_preserves_typing : forall D mt Delta Gamma id t u T U,
  D / mt / (Delta, update Gamma id U) |- t is T ->
  D / mt / (empty, empty) |- u is U ->
  D / mt / (Delta, Gamma) |- [id := u] t is T.
Proof.
  intros * Ht Hu.
  generalize dependent T.
  generalize dependent Gamma.
  induction t;
  intros Gamma T Ht;
  inversion Ht; simpl; subst;
  eauto using @typeof.
  - destruct String.eqb eqn:E.
    + apply String.eqb_eq in E. subst.
      rewrite lookup_update_involutive in H4.
      discriminate H4.
    + apply String.eqb_neq in E.
      eapply (aux n id); eauto.
  - destruct String.eqb eqn:E.
    + apply String.eqb_eq in E. subst.
      rewrite lookup_update_involutive in H4.
      inversion H4. subst. auto.
      admit.
    + apply String.eqb_neq in E.
      eapply (aux n id); eauto.
  - destruct String.eqb eqn:E.
    + apply String.eqb_eq in E. subst.
      rewrite lookup_update_involutive in H4.
      admit.
    + apply String.eqb_neq in E.
      eapply (aux n id); eauto.
  - admit.
  - apply T_LetVal.
    specialize (IHt1 _ _ H6).
    apply IHt1.
    destruct String.eqb eqn:E.
    + apply String.eqb_eq in E. subst.
      eauto using aux2.
    + apply String.eqb_neq in E.
  - admit.
Admitted.

Lemma memory_weakening : forall D mt mt' Delta Gamma t T, 
  D / mt' / (Delta, Gamma) |- t is T ->
  mt extends mt' ->
  D / mt  / (Delta, Gamma) |- t is T.
Proof.
  intros * Htype Hext.
  induction Htype; eauto using @typeof.
  assert (i < length mt). { eauto using extends_length.  }
  erewrite extends_lookup; auto using T_Loc.
Qed.

(* Lemma well_typed_memory_app : forall D mt m t T,
  well_typed_memory D mt m ->
  D / mt / (nil, nil) |- t is T ->
  well_typed_memory D (mt ++ T :: nil) (m ++ t :: nil).
Admitted. *)

Lemma length_add : forall {A B} (l1 : list A) (l2 : list B) a b,
  length l1 = length l2 ->
  length (add l1 a) = length (add l2 b).
Proof.
Admitted.

Theorem preservation : forall D D' m m' mt t t' T,
  D / mt / (nil, nil) |- t is T ->
  well_typed_memory D mt m ->
  D / m / t --> D' / m' / t' ->
  exists mt',
    mt' extends mt /\
    D' / mt' / (nil, nil) |- t' is T /\
    well_typed_memory D' mt' m'.
Proof.
  remember (nil, nil) as Context.
  intros * Htype.
  generalize dependent t'.
  induction Htype; intros ?t' Hmem Hstep.
  - inversion Hstep. (* T_Nil *)
  - inversion Hstep. (* T_Num *)
  - inversion Hstep. (* T_IdSharedVal *)
  - inversion Hstep. (* T_IdLocalVal *)
  - inversion Hstep. (* T_IdVar *)
  - (* T_Asg *)
    inversion Hstep; inversion HeqContext; subst.
    + specialize (IHHtype2 eq_refl e' Hmem H6).
      destruct IHHtype2 as [mt' [Hextends [Htype' Hmem']]].
      exists mt'. split. apply Hextends. split.
      * eauto using memory_weakening, T_Asg.
      * auto.
    + specialize (IHHtype1 eq_refl t'0 Hmem H7).
      destruct IHHtype1 as [mt' [Hextends [Htype' Hmem']]].
      exists mt'. split. apply Hextends. split.
      * eauto using memory_weakening, T_Asg.
      * auto.
    + inversion Htype1. subst. exists mt. split.
      * apply extends_refl.
      * split.
        { apply T_Nil. }
        { apply assignment_preserves_memory_typing; auto. }
  - (* T_Call *)
    inversion Hstep; inversion HeqContext; subst.
    + specialize (IHHtype1 eq_refl e' Hmem H7).
      destruct IHHtype1 as [mt' [Hextends [Htype' Hmem']]].
      exists mt'. split.
      * auto.
      * split.
        { eapply T_Call; eauto using memory_weakening. }
        { auto. }
    + exists mt. split.
      * apply extends_refl.
      * split.
        { rewrite H in H8. injection H8 as ?; subst.
          eapply substitution_preserves_typing; eauto. }
        { auto. }
  - (* T_Seq *)
    inversion Hstep; inversion HeqContext; subst.
    + specialize (IHHtype1 eq_refl t2 Hmem H6).
      destruct IHHtype1 as [mt' [Hextends [Htype' Hmem']]].
      exists mt'. split.
      * auto.
      * split; eauto using T_Seq, memory_weakening.
    + exists mt. split.
      * apply extends_refl.
      * split; assumption.
  - (* T_LetVal *)
    inversion Hstep; inversion HeqContext; subst.
    + specialize (IHHtype1 eq_refl e' Hmem H8).
      destruct IHHtype1 as [mt' [Hextends [Htype' Hmem']]].
      exists mt'. split.
      * assumption.
      * split; try assumption.
        eauto using T_LetVal, memory_weakening.
    + exists (add mt A). split.
      * apply extends_add.
      * split.
        { eapply substitution_preserves_typing.
          assert (add mt A extends mt). { apply extends_add. }
          eapply (memory_weakening _ _ _ _ _ _ _ Htype2 H).
          admit.
        }
        { destruct Hmem as [Hlen H]. split.
          - unfold m'1. apply length_add. auto.
          - intros j. specialize (H j).
            admit.
        }
  - (* T_LetVar *)
    inversion Hstep; inversion HeqContext; subst.
    + specialize (IHHtype1 eq_refl e' Hmem H9).
      destruct IHHtype1 as [mt' [Hextends [Htype' Hmem']]].
      exists mt'. split.
      * assumption.
      * split; try assumption.
        eauto using T_LetVar, memory_weakening.
    + exists (add mt A). split.
      * apply extends_add.
      * split.
        { eapply substitution_preserves_typing.
          assert (add mt A extends mt). { apply extends_add. }
          eapply (memory_weakening _ _ _ _ _ _ _ Htype2 H).
          admit.
        }
        { destruct Hmem as [Hlen H]. split.
          - apply length_add. auto.
          - intros j. specialize (H j).
            admit.
        }
  - admit.
Admitted.
(* Qed *)

Theorem progress : forall D m mt t T,
  D / mt / (nil, nil) |- t is T ->
  well_typed_memory D mt m ->
  (value t \/ exists D' m' t', D / m / t --> D' / m' / t').
Admitted.