From Coq Require Logic.ClassicalFacts.
From Coq Require Import Logic.Decidable.

(* Miscellaneous Utilities *)

Ltac auto_specialize :=
  match goal with
  | P : ?x, H : ?x -> _ |- _ => specialize (H P)
  end.

Ltac inversion_subst_clear H :=
  inversion H; subst; clear H.

(* TODO: classic *)
Local Lemma destruct_and' : forall a x y,
  (a -> x /\ y) -> ((a -> x) /\ (a -> y)). 
Proof.
  intros * H. split; intros a'; specialize (H a') as [? ?]; trivial.
Qed.

(* TODO: decompose record ? *)
Ltac destruct_and H :=
  eapply destruct_and' in H as [? ?].

Axiom excluded_middle : ClassicalFacts.excluded_middle.

Corollary classic_decidable : forall (P : Prop),
  decidable P.
Proof.
  intros. unfold decidable. eauto using excluded_middle.
Qed.

(* Unused

Definition memory_has_values (m : mem) :=
  forall ad, value (getTM m ad).

Theorem memory_has_values_preservation : forall m m' t t' eff,
  memory_has_values m ->
  m / t ==[eff]==> m' / t' ->
  memory_has_values m'.
Proof.
  intros. inversion_mstep; trivial.
  - remember (EF_Alloc _ _) as eff.
    induction_step; inversion Heqeff; subst; eauto. intros ad.
    decompose sum (lt_eq_lt_dec ad (length m)); subst.
    + rewrite (get_add_lt TM_Unit); trivial.
    + rewrite (get_add_eq TM_Unit); trivial.
    + rewrite (get_add_gt TM_Unit); eauto using value.
  - remember (EF_Store _ _) as eff.
    induction_step; inversion Heqeff; subst; eauto. intros ad'.
    decompose sum (lt_eq_lt_dec ad' ad); subst.
    + rewrite (get_set_lt TM_Unit); trivial.
    + rewrite (get_set_eq TM_Unit); trivial.
    + rewrite (get_set_gt TM_Unit); trivial.
Qed.

*)
