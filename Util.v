From Coq Require Logic.ClassicalFacts.
From Coq Require Import Logic.Decidable.

(* miscellaneous utilities *)

Ltac auto_specialize :=
  match goal with
  | P : ?x, H : ?x -> _ |- _ => specialize (H P)
  end.

Ltac inversion_subst_clear H :=
  inversion H; subst; clear H.

Axiom excluded_middle : ClassicalFacts.excluded_middle.

Corollary classic_decidable : forall (P : Prop),
  decidable P.
Proof.
  intros. unfold decidable. eauto using excluded_middle.
Qed.

