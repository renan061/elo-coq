From Coq Require Logic.ClassicalFacts.
From Coq Require Import Logic.Decidable.
From Coq Require Import Lia.

(* inversion shortcuts *)

Ltac inv H := inversion H; subst.

Ltac invc H := inv H; clear H.

(* miscellaneous utilities *)

Ltac splits n :=
  match n with
  | O => fail
  | S O => idtac
  | S ?n' => split; [| splits n']
  end.

Ltac auto_specialize :=
  match goal with
  | P : ?x, H : ?x -> _ |- _ => specialize (H P)
  | H : ?x = ?x -> _ |- _ => specialize (H eq_refl) 
  end.

#[export] Hint Extern 4 =>
  match goal with
  | _ : ?n < ?n  |- _ => lia
  | _ : ?n > ?n  |- _ => lia
  | F : ?x <> ?x |- _ => contradict F; eauto
  end : core.

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

(* misc *)

Lemma ge_iff_le : forall m n,
  m >= n <-> n <= m.
Proof.
  intros; split; destruct n; eauto.
Qed.

