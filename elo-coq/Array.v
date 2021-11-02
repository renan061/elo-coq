From Coq Require Import Lists.List.

Definition add {A} (l : list A) (a : A) := l ++ (a :: nil).

Definition get {A} (default : A) (l : list A) (i : nat) :=
  nth_default default l i.

Fixpoint set {A} (l : list A) (i : nat) (a : A) : list A :=
  match l with
  | nil => nil
  | a' :: l' =>
    match i with
    | O => a :: l'
    | S i' => a' :: set l' i' a
    end
  end.

(* Proofs *)

Lemma get_S_i : forall {A} default (l : list A) a i,
  get default (a :: l) (S i) = get default l i.
Proof.
 intros *. unfold get, nth_default. reflexivity.
Qed.

Lemma set_preserves_length : forall {A} (l : list A) i a,
  length l = length (set l i a).
Proof.
  intros ?. induction l.
  - reflexivity.
  - destruct i; simpl; auto using Lt.lt_S_n.
Qed.

Lemma add_preserves_length : forall {A1 A2} (l1 : list A1) (l2 : list A2) a1 a2,
  length l1 = length l2 ->
  length (add l1 a1) = length (add l2 a2).
Proof.
  intros * H. unfold add. rewrite 2 last_length. auto.
Qed.

Lemma length_l_lt_add : forall {A} (l : list A) a,
  length l < length (add l a).
Proof.
  intros *. unfold add. rewrite last_length.
  auto using PeanoNat.Nat.lt_succ_diag_r.
Qed.

Lemma get_set_involutive : forall {A} default (l : list A) i a,
  i < length l ->
  get default (set l i a) i = a.
Proof.
  intros ? ? l.
  induction l as [| ? ? IH]; intros * H.
  - inversion H.
  - destruct i; unfold get, List.nth_default.
    + reflexivity.
    + apply IH. auto using Lt.lt_S_n.
Qed.

Lemma set_get_involutive : forall {A} default (l : list A) i,
  i < length l ->
  set l i (get default l i) = l.
Proof.
  intros ? ? l.
  induction l as [| ? ? IH]; intros * H.
  - inversion H.
  - destruct i.
    + unfold get, nth_default, nth_error. reflexivity.
    + simpl. rewrite get_S_i, IH; auto using Lt.lt_S_n.
Qed.

Lemma get_set_i_neq_j : forall {A} d (l : list A) i j a,
  i <> j ->
  get d (set l j a) i = get d l i.
Proof.
  intros ? ? l.
  induction l as [| x xs IH]; intros * Hdiff.
  - reflexivity.
  - destruct i, j; try (contradiction || reflexivity).
    assert (H : forall n y ys, get d (y :: ys) (S n) = get d ys n). { auto. }
    simpl. rewrite 2 H. auto.
Qed.
