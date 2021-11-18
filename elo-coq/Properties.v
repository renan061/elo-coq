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

(* Determinism *)

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
  assert (forall A B, TY_Ref A  = TY_Ref  B -> A = B).        { congruence. }
  assert (forall A B, TY_IRef A = TY_IRef B -> A = B).        { congruence. }
  assert (iref_neq_ref : forall A B, TY_IRef A <> TY_Ref  B). { congruence. }
  assert (ref_neq_iref : forall A B, TY_Ref  A <> TY_IRef B). { congruence. }

  intros * HX.
  generalize dependent Y.
  induction HX; intros Y HY;
  inversion HY; subst;
  try solve [congruence | auto];
  try (match goal with H : context [?C _ = _] |- _ = _ =>
    exfalso;
    match C with
    | TY_Ref => eapply ref_neq_iref
    | TY_IRef => eapply iref_neq_ref
    end;
    eauto
  end; fail).
  - apply IHHX1 in H4. congruence.
  - apply IHHX1 in H4. congruence. 
  - apply IHHX1 in H4. congruence.
  - apply IHHX1 in H4. congruence.
  - apply IHHX1 in H4. apply IHHX2 in H6. congruence.
Qed.

(* Progress, Preservation & Soundness *)

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
  induction Htype; eauto using @typeof, extends_length;
  subst; erewrite extends_lookup; eauto using extends_length, @typeof.
Qed.

Lemma safe_preserves_lookup : forall Gamma Gamma' k,
  lookup Gamma k = lookup Gamma' k ->
  lookup (safe Gamma) k = lookup (safe Gamma') k.
Proof.
  intros * H. induction Gamma' as [| id' T' Gamma' IH'].
  - simpl in *. induction Gamma as [| id T Gamma IH].
    + reflexivity.
    + simpl in *. destruct (String.eqb id k) eqn:E.
      * discriminate.
      * destruct (safe_type_bool T).
        ** simpl in *. rewrite E. auto.
        ** auto.
  - simpl in *. induction Gamma as [| id T Gamma IH].
    + simpl in *. destruct (String.eqb id' k) eqn:E.
      * discriminate.
      * destruct (safe_type_bool T').
        ** simpl in *. rewrite E. auto.
        ** auto.
    + simpl in *. destruct (String.eqb id' k) eqn:E1.
      apply String.eqb_eq in E1. subst.
      * destruct (String.eqb id k) eqn:E2.
        ** apply String.eqb_eq in E2. subst.
           injection H as H'. subst.
Admitted.

Lemma safe_preserves_inclusion : forall Gamma Gamma',
  Gamma includes Gamma' ->
  (safe Gamma) includes (safe Gamma').
Proof.
  intros *. unfold Map.includes'.
  induction Gamma as [| id T Gamma IH]; intros * Hinc *.
  - admit.
  - destruct Gamma' as [| id' T' Gamma'].
    + discriminate.
    + simpl in *.
      * destruct (safe_type_bool T') eqn:E1.
        ** simpl in *.
           destruct (String.eqb id' k) eqn:E2.
           *** apply String.eqb_eq in E2. subst.
               destruct (safe_type_bool T) eqn:E3.
               **** simpl in *.
                    specialize (Hinc k v).
                    rewrite String.eqb_refl in *.
                    destruct (String.eqb id k) eqn:E4.
                    ***** assumption.
                    ***** intros H. apply IH.
                          ****** intros.
Admitted.

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

Fixpoint type_equality T U :=
  match T, U with
  | TY_Void, TY_Void
  | TY_Num, TY_Num => true
  | TY_Arr T', TY_Arr U'
  | TY_IArr T', TY_IArr U'
  | TY_Ref T', TY_Ref U'
  | TY_IRef T', TY_IRef U'  => type_equality T' U'
  | TY_Fun P R, TY_Fun P' R' => andb (type_equality P P') (type_equality R R')
  | _, _ => false
  end.

Theorem type_equality_correct : forall T U,
  type_equality T U = true <-> T = U.
Proof.
Admitted.

(* TODO: unused *)
Corollary destruct_lookup_update : forall {A} (m : map A) k k' v,
  lookup (update m k' v) k = lookup m k \/ lookup (update m k' v) k = Some v.
Proof.
  intros *. destruct (String.eqb k k') eqn:E.
  - right. apply String.eqb_eq in E. subst. apply lookup_update_k_eq.
  - left. apply String.eqb_neq, not_eq_sym in E. apply lookup_update_k_neq.
    assumption.
Qed.

(* TODO : renomear prova; criar lemas e encurtar essa prova. *)
Lemma aux : forall Gamma id T,
  (update (safe Gamma) id T) includes (safe (update Gamma id T)).
Proof.
  intros *. unfold Map.includes'. intros *.
  destruct (String.eqb id k) eqn:E1.
  - apply String.eqb_eq in E1. subst.
    rewrite lookup_update_k_eq.
    intros H. rewrite <- H. symmetry.
    destruct (safe_type_bool T) eqn:E2.
    + induction Gamma.
      * simpl in *. rewrite E2 in *.
        simpl in *. rewrite String.eqb_refl in *.
        trivial.
      * simpl in *. destruct (String.eqb k k0) eqn:E3.
        ** simpl in *. rewrite E2 in *.
           simpl in *. rewrite String.eqb_refl in *.
           reflexivity.
        ** simpl in *. destruct (safe_type_bool v0) eqn:E4; auto.
           simpl in *. rewrite String.eqb_sym in E3. rewrite E3 in *. auto.
    + induction Gamma.
      * simpl in *. rewrite E2 in *. discriminate H.
      * simpl in *. destruct (String.eqb k k0) eqn:E3.
        ** simpl in *. rewrite E2 in *. auto.
        ** simpl in *.  destruct (safe_type_bool v0) eqn:E4; auto.
           simpl in *. rewrite String.eqb_sym in E3. rewrite E3 in *. auto.
  - apply String.eqb_neq in E1 as E1'.
    rewrite lookup_update_k_neq; trivial.
    intros H. rewrite <- H. symmetry.
    destruct (safe_type_bool T) eqn:E2.
    + induction Gamma.
      * simpl in *. rewrite E2 in *.
        simpl in *. rewrite E1.
        reflexivity.
      * simpl in *. destruct (String.eqb id k0) eqn:E3.
        ** apply String.eqb_eq in E3. subst.
           simpl in *. rewrite E2 in *.
           simpl in *. rewrite E1 in *.
           destruct (safe_type_bool v0) eqn:E4; auto.
           simpl in *. rewrite E1. auto.
        ** simpl in *. destruct (safe_type_bool v0) eqn:E4; auto.
           simpl in *. destruct (String.eqb k0 k) eqn: E5; auto.
    + induction Gamma.
      * simpl in *. rewrite E2 in *. discriminate H.
      * simpl in *. destruct (String.eqb id k0) eqn:E3.
        ** apply String.eqb_eq in E3. subst.
           simpl in *. rewrite E2 in *.
           destruct (safe_type_bool v0) eqn:E4; auto.
           simpl in *. rewrite E1. auto.
        ** simpl in *.  destruct (safe_type_bool v0) eqn:E4; auto.
           simpl in *. destruct (String.eqb k0 k) eqn: E5; auto.
Qed.

Lemma substitution_preserves_typing : forall mt Gamma id t u T U,
  mt / (update Gamma id U) |-- t is T ->
  mt / empty |-- u is U ->
  mt / Gamma |-- [id := u] t is T.
Proof with eauto using context_weakening, context_weakening_empty,
  lookup_update_k_neq, update_overwrite, update_permutation, aux.
  intros * Ht Hu.
  generalize dependent T. generalize dependent Gamma.
  induction t; intros * Ht; inversion Ht; simpl; subst;
  eauto using @typeof;
  try (destruct String.eqb eqn:E);
  try (apply String.eqb_eq in E; subst);
  try (apply String.eqb_neq in E).
  - rewrite lookup_update_k_eq in H1. inversion H1. subst...
  - apply T_Id_Val. rewrite <- H1. symmetry...
  - rewrite lookup_update_k_eq in H1. inversion H1. subst...
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
