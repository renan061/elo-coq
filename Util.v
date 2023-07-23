From Coq Require Logic.ClassicalFacts.
From Coq Require Import Logic.Decidable.

(* inversion shortcuts *)

Ltac inv_subst H := inversion H; subst.

Ltac inv_subst_clear H := inv_subst H; clear H.

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

(* dec *)

From Coq Require Arith.Compare_dec.
From Coq Require Arith.Peano_dec.
From Coq Require Strings.String.

Definition nat_eq_dec := Peano_dec.eq_nat_dec.
Definition string_eq_dec := String.string_dec.
Definition lt_eq_lt_dec := Compare_dec.lt_eq_lt_dec.

