From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.

Definition add {A} (l : list A) (a : A) := l ++ (a :: nil).

Definition get {A} (default : A) (l : list A) (i : nat) :=
  nth i l default.

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
 intros *. unfold get. reflexivity.
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

Lemma get_add_lt : forall {A} default (l : list A) a i,
  i < length l ->
  get default (add l a) i = get default l i.
Proof.
  intros *. generalize dependent i.
  induction l. intros * Hlen.
  - destruct i eqn:E.
    + inversion Hlen.
    + destruct n; reflexivity.
  - intros i. simpl. destruct i; intros H.
    + reflexivity.
    + apply PeanoNat.Nat.succ_lt_mono in H. auto.
Qed.

Lemma get_add_last : forall {A} default (l : list A) a,
  get default (add l a) (length l) = a.
Proof.
  intros. induction l; auto.
Qed.

Lemma get_add_gt : forall {A} default (l : list A) a i,
  length l < i ->
  get default (add l a) i = default.
Proof.
  intros *. generalize dependent i.
  induction l. intros * Hlen.
  - destruct i eqn:E.
    + inversion Hlen.
    + destruct n; reflexivity.
  - intros i. simpl. destruct i; intros H.
    + inversion H.
    + apply PeanoNat.Nat.succ_lt_mono in H. auto.
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
  - destruct i; unfold get.
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
    + reflexivity.
    + simpl in *. f_equal. auto using Lt.lt_S_n.
Qed.

Lemma get_set_i_neq_j : forall {A} d (l : list A) i j a,
  i <> j ->
  get d (set l j a) i = get d l i.
Proof.
  intros ? ? l.
  induction l as [| x xs IH]; intros * Hdiff.
  - reflexivity.
  - destruct i, j; try (contradiction || reflexivity).
    simpl. auto using PeanoNat.Nat.succ_inj_wd_neg.
Qed.

Lemma get_default : forall {A} d (l : list A) i,
  length l <= i -> get d l i = d.
Proof.
  intros ? ? l. induction l as [| ? ? IH]; intros i Hlen; destruct i; trivial.
  - apply Nat.nle_succ_0 in Hlen. contradiction.
  - simpl in *. apply le_S_n in Hlen. apply (IH i Hlen).
Qed.

Lemma get_set_default : forall {A} d (l : list A) i a,
  length l <= i ->
  get d (set l i a) i = d.
Proof.
  intros * Hlen.
  erewrite set_preserves_length in Hlen.
  eauto using get_default.
Qed.

Lemma add_set_comm : forall {A} (l : list A) i a1 a2,
  i < length l ->
  add (set l i a1) a2 = set (add l a2) i a1.
Proof.
  unfold add.
  intros ? l. induction l as [| ? ? IH]; intros * H.
  - destruct i eqn:E.
    + inversion H.
    + reflexivity.
  - simpl in *. destruct i eqn:E.
    + reflexivity.
    + apply lt_S_n in H. rewrite <- (IH n a1 a2 H). reflexivity.
Qed.
