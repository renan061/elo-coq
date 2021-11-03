From Coq Require Import Arith.Arith.

From Elo Require Export Array.
From Elo Require Export Map.
From Elo Require Export Core.

Ltac splits n :=
  match n with
  | O => fail
  | S O => idtac
  | S ?n' => split; [| splits n']
  end.

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
    + unfold get_typ, get. simpl in *. eauto using Lt.lt_S_n.
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
Proof with eauto using context_weakening, context_weakening_empty,
  lookup_update_idempotent, update_overwrite, update_permutation.
  intros * Ht Hu.
  generalize dependent T. generalize dependent Gamma.
  induction t; intros * Ht; inversion Ht; simpl; subst;
  eauto using @typeof; destruct String.eqb eqn:E;
  try (apply String.eqb_eq in E; subst); try (apply String.eqb_neq in E).
  - rewrite lookup_update_involutive in H1. inversion H1. subst...
  - apply T_Id_Val. rewrite <- H1. symmetry...
  - rewrite lookup_update_involutive in H1. inversion H1. subst...
  - apply T_Id_Var. rewrite <- H1. symmetry...
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
  induction Htype;
  intros ?t' Hmem Hstep;
  inversion Hstep; subst.
  (* T_Asg *)
  - eapply IHHtype2 in H4; trivial.
    destruct H4 as [mt' [? [? ?]]].
    exists mt'. splits 3; eauto using memory_weakening, T_Asg.
  - eapply IHHtype1 in H5; trivial.
    destruct H5 as [mt' [? [? ?]]].
    exists mt'. splits 3; eauto using memory_weakening, T_Asg.
  - exists mt. splits 3; auto using extends_refl, T_Nil.
    eapply assignment_preserves_memory_typing; auto.
    inversion Htype1. subst. eauto.
  (* T_Call *)
  - eapply IHHtype2 in H4; trivial.
    destruct H4 as [mt' [? [? ?]]].
    exists mt'. splits 3; trivial.
    eapply T_Call; eauto using memory_weakening.
  - eapply IHHtype1 in H5; trivial.
    destruct H5 as [mt' [? [? ?]]].
    exists mt'. splits 3; trivial.
    eauto using T_Call, memory_weakening.
  - exists mt. splits 3; auto using extends_refl.
    inversion Htype1. subst.
    eapply substitution_preserves_typing; eauto.
  (* T_Seq *)
  - eapply IHHtype1 in H4; trivial.
    destruct H4 as [mt' [? [? ?]]].
    exists mt'. splits 3; eauto using T_Seq, memory_weakening.
  - exists mt. splits 3; auto using extends_refl.
  (* T_LetVal *)
  - eapply IHHtype1 in H6; trivial.
    destruct H6 as [mt' [? [? ?]]].
    exists mt'. splits 3; eauto using T_LetVal, memory_weakening.
  - exists mt. splits 3; auto using extends_refl.
    eapply substitution_preserves_typing; eauto.
  (* T_LetVar *)
  - eapply IHHtype1 in H6; trivial.
    destruct H6 as [mt' [? [? ?]]].
    exists mt'. splits 3; trivial.
    eauto using T_LetVar, memory_weakening.
  - exists (add mt E). inversion Hmem.
    splits 3; auto using extends_add, add_preserves_well_typed_memories.
    eapply substitution_preserves_typing.
    + eauto using extends_add, memory_weakening.
    + rewrite <- H.
      assert (TY_Ref E = TY_Ref (get_typ (add mt E) (length mt))).
      { unfold get_typ. rewrite (get_add_last TY_Void). reflexivity. }
      rewrite H1. auto using T_Loc, length_l_lt_add.
  (* T_LetFun *)
  - eapply IHHtype1 in H7; trivial.
    destruct H7 as [mt' [? [? ?]]].
    exists mt'. splits 3; eauto using T_LetFun, memory_weakening.
  - exists mt. splits 3; auto using extends_refl.
    eapply substitution_preserves_typing; eauto.
  (* T_Load *)
  - apply IHHtype in H1; trivial.
    destruct H1 as [mt' [? [? ?]]].
    exists mt'. splits 3; auto using T_Load_Ref.
  - exists mt. splits 3; auto using extends_refl.
    inversion Htype. destruct Hmem. auto.
  - apply IHHtype in H1; trivial.
    destruct H1 as [mt' [? [? ?]]].
    exists mt'. splits 3; auto using T_Load_ImmutRef.
  - inversion Htype.
Qed.

Theorem progress : forall m mt t T,
  mt / empty |-- t is T ->
  well_typed_memory mt m ->
  (value t \/ exists m' t', m / t --> m' / t').
Proof.
  remember empty as Gamma.
  intros * Htype Hmem.
  induction Htype; subst; auto using value; right.
  - inversion H.
  - inversion H.
  - specialize (IHHtype1 eq_refl).
    specialize (IHHtype2 eq_refl).
    destruct IHHtype1, IHHtype2.
    + destruct H eqn:E; inversion Htype1; subst.
      eexists. eexists. apply ST_Asg; trivial.
      destruct Hmem as [Hlen ?]. rewrite <- Hlen. assumption.
    + destruct H0 as [? [? ?]]. eexists. eexists. apply ST_Asg1; eauto.
    + destruct H as [? [? ?]]. eexists. eexists. apply ST_Asg2; eauto.
    + destruct H0 as [? [? ?]]. eexists. eexists. apply ST_Asg1; eauto.
  - specialize (IHHtype1 eq_refl).
    specialize (IHHtype2 eq_refl).
    destruct IHHtype2.
    + destruct IHHtype1.
      * destruct H0; inversion Htype1; subst.
        eexists. eexists. eapply ST_Call; trivial.
      * destruct H0 as [? [? ?]]. eexists. eexists. apply ST_Call2; eauto.
    + destruct H as [? [? ?]]. eexists. eexists. apply ST_Call1; eauto.
  - specialize (IHHtype1 eq_refl).
    specialize (IHHtype2 eq_refl).
    destruct IHHtype1.
    + destruct H; inversion Htype1. eexists. eexists. apply ST_Seq.
    + destruct H as [? [? ?]]. eexists. eexists. apply ST_Seq1; eauto.
  - specialize (IHHtype1 eq_refl).
    destruct IHHtype1.
    + eexists. eexists. apply ST_LetVal; trivial.
    + destruct H as [? [? ?]]. eexists. eexists. apply ST_LetVal1; eauto.
  - specialize (IHHtype1 eq_refl).
    destruct IHHtype1.
    + eexists. eexists. apply ST_LetVar; trivial.
    + destruct H as [? [? ?]]. eexists. eexists. apply ST_LetVar1; eauto.
  - specialize (IHHtype1 eq_refl).
    destruct IHHtype1.
    + eexists. eexists. apply ST_LetFun; trivial.
    + destruct H as [? [? ?]]. eexists. eexists. apply ST_LetFun1; eauto.
  - specialize (IHHtype eq_refl).
    destruct IHHtype.
    + destruct H; inversion Htype; subst. eexists. eexists. apply ST_Load.
    + destruct H as [? [? ?]]. eexists. eexists. eapply ST_Load1; eauto.
  - specialize (IHHtype eq_refl).
    destruct IHHtype.
    + destruct H; inversion Htype.
    + destruct H as [? [? ?]]. eexists. eexists. eapply ST_Load1; eauto.
Qed.
