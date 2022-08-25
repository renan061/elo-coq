From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

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

Lemma set_invalid : forall {A} (l : list A) i a,
  length l <= i ->
  set l i a = l.
Proof.
  intros *. generalize dependent i.
  induction l as [| ? ? IH]; intros * H; trivial.
  simpl. destruct i; try solve [inversion H].
  simpl in H. eapply le_S_n in H.
  rewrite IH; eauto.
Qed.

Lemma set_preserves_length : forall {A} (l : list A) i a,
  length (set l i a) = length l.
Proof.
  intros ?. induction l; trivial.
  destruct i; simpl; eauto using Lt.lt_S_n.
Qed.

Lemma add_increments_length : forall {A} (l : list A) a,
  length (add l a) = S (length l).
Proof.
  intros. unfold add. rewrite last_length. reflexivity.
Qed.

Lemma get_default : forall {A} default (l : list A) i,
  length l <= i ->
  get default l i = default.
Proof.
  intros *. generalize dependent i.
  induction l as [| ? ? IH]; intros * H;
  simpl; destruct i; trivial;
  try solve [inversion H].
  simpl in H. eapply le_S_n in H.
  rewrite IH; eauto.
Qed.

Lemma get_set_eq : forall {A} default (l : list A) i a,
  i < length l ->
  get default (set l i a) i = a.
Proof.
  intros ? ? l.
  induction l as [| ? ? IH]; intros * H; try solve [inversion H].
  destruct i; unfold get; trivial.
  eapply IH. eauto using Lt.lt_S_n.
Qed.

Lemma get_set_neq : forall {A} default (l : list A) i j a,
  i <> j ->
  get default (set l j a) i = get default l i.
Proof.
  intros ? ? l.
  induction l as [| x xs IH]; intros * H; trivial.
  destruct i, j; trivial; try contradiction.
  simpl. eauto using PeanoNat.Nat.succ_inj_wd_neg.
Qed.

Lemma get_set_lt : forall {A} default (l : list A) i j a,
  i < j ->
  get default (set l j a) i = get default l i.
Proof.
  intros. eapply get_set_neq. lia. 
Qed.

Lemma get_set_gt : forall {A} default (l : list A) i j a,
  j < i ->
  get default (set l j a) i = get default l i.
Proof.
  intros. eapply get_set_neq. lia.
Qed.

Lemma get_set_invalid : forall {A} default (l : list A) i a,
  length l <= i ->
  get default (set l i a) i = default.
Proof.
  intros * H. rewrite set_invalid; trivial. eauto using get_default.
Qed.

Lemma get_add_eq : forall {A} default (l : list A) a,
  get default (add l a) (length l) = a.
Proof.
  intros. induction l; eauto.
Qed.

Lemma get_add_lt : forall {A} default (l : list A) a i,
  i < length l ->
  get default (add l a) i = get default l i.
Proof.
  intros ? ? ? ?. induction l; intros ?.
  - intros H. destruct i; inversion H.
  - simpl. intros H. destruct i; trivial.
    eapply PeanoNat.Nat.succ_lt_mono in H. eauto.
Qed.

Lemma get_add_gt : forall {A} default (l : list A) a i,
  length l < i ->
  get default (add l a) i = default.
Proof.
  intros ? ? ? ?. induction l; intros ? H;
  destruct i; try solve [inversion H].
  - destruct i; trivial.
  - simpl. eapply PeanoNat.Nat.succ_lt_mono in H. eauto.
Qed.

(* Properties *)

Definition property {A} (a : A) (P : A -> Prop) (l : list A) : Prop :=
  forall i, P (get a l i).

Lemma property_add : forall {A} (P : A -> Prop) default l a,
  P default ->
  P a ->
  property default P l ->
  property default P (add l a).
Proof.
  intros; intros i. decompose sum (lt_eq_lt_dec i (length l)); subst.
  - rewrite (get_add_lt default); trivial.
  - rewrite (get_add_eq default); trivial.
  - rewrite (get_add_gt default); trivial.
Qed.

Lemma property_set : forall {A} (P : A -> Prop) default l i a,
  P default ->
  P a ->
  property default P l ->
  property default P (set l i a).
Proof.
  intros; intros i'. decompose sum (lt_eq_lt_dec i i'); subst.
  - rewrite (get_set_gt default); trivial.
  - decompose sum (le_lt_dec (length l) i').
    + rewrite set_invalid in *; trivial.
    + rewrite (get_set_eq default); trivial.
  - rewrite (get_set_lt default); trivial.
Qed.

(*

TODO: Probably used by progress/preservation.

Lemma add_preserves_length : forall {A1 A2} (l1 : list A1) (l2 : list A2) a1 a2,
  length l1 = length l2 ->
  length (add l1 a1) = length (add l2 a2).
Proof.
  intros * H. unfold add. rewrite 2 last_length. auto.
Qed.

Lemma length_lt_add : forall {A} (l : list A) a,
  length l < length (add l a).
Proof.
  intros *. unfold add. rewrite last_length.
  auto using PeanoNat.Nat.lt_succ_diag_r.
Qed.

Lemma add_tail : forall {A} head (tail : list A) a,
  head :: add tail a = add (head :: tail) a.
Proof.
  eauto.
Qed.

Lemma set_tail : forall {A} head (tail : list A) i a,
  head :: set tail i a = set (head :: tail) (S i) a.
Proof.
  eauto.
Qed.

Lemma add_set_tail : forall {A} head (tail : list A) i a a',
  head :: add (set tail i a) a' = add (set (head :: tail) (S i) a) a'.
Proof.
  eauto.
Qed.

*)
