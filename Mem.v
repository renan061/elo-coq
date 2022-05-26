From Coq Require Import Lists.List.

Definition mem (A : Type) := list (nat * A). 

Fixpoint get {A : Type} (m : mem A) i default :=
  match m with
  | nil => default
  | (i', a') :: m' => if Nat.eqb i i' then a' else get m' i default 
  end.

Definition set {A : Type} (m : mem A) i a :=
  (i, a) :: m.

Definition length {A : Type} (m : mem A) :=
  fold_left (fun x y => max x (fst y)) m 0. 

(* Proofs *)

Lemma get_set_eq : forall {A} default (m : mem A) i a,
  get ((i, a) :: m) i default = a.
Proof.
  intros. simpl. rewrite PeanoNat.Nat.eqb_refl. reflexivity.
Qed.

Lemma get_set_neq : forall {A} (m : mem A) i i' a,
  i <> i' ->
  get ((i', a) :: m) i = get m i.
Proof.
  intros * Hneq. eapply PeanoNat.Nat.eqb_neq in Hneq.
  simpl. rewrite Hneq. reflexivity.
Qed.

