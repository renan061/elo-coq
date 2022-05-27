From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List.

Definition mem (A : Type) := list (nat * A).

Fixpoint get {A} default (m : mem A) i :=
  match m with
  | nil => default
  | (i', a') :: m' => if Nat.eqb i i' then a' else get default m' i
  end.

Definition set {A} (m : mem A) i a :=
  (i, a) :: m.

Local Fixpoint max (n m : nat) :=
  match n with
  | 0 => m
  | S n' => match m with
            | 0 => n
            | S m' => S (max n' m')
            end
  end.

Fixpoint length {A : Type} (m : mem A) :=
  match m with
  | nil => 0
  | (i, _) :: m' => max i (length m')
  end.

Definition add {A} (m : mem A) a :=
  (length m, a) :: m.

(* Proofs *)

Lemma get_set_eq : forall {A} default (m : mem A) i a,
  get default ((i, a) :: m) i = a.
Proof.
  intros. simpl. rewrite PeanoNat.Nat.eqb_refl. reflexivity.
Qed.

Lemma get_set_neq : forall {A} default (m : mem A) i i' a,
  i <> i' ->
  get default ((i', a) :: m) i = get default m i.
Proof.
  intros * Hneq. eapply PeanoNat.Nat.eqb_neq in Hneq.
  simpl. rewrite Hneq. reflexivity.
Qed.

Lemma get_add_eq : forall {A} default (m : mem A) a,
  get default (add m a) (length m) = a.
Proof.
  intros. unfold add. eauto using get_set_eq.
Qed.

Lemma get_add_lt : forall {A} default (m : mem A) a i,
  i < length m ->
  get default (add m a) i = get default m i.
Proof.
  intros. simpl. destruct (Nat.eqb _ _) eqn:E; trivial. 
  eapply Nat.eqb_eq in E. lia.
Qed.

Lemma get_add_gt : forall {A} default (m : mem A) a i,
  length m < i ->
  get default (add m a) i = default.
Proof.
  intros * H. simpl. destruct (Nat.eqb _ _) eqn:E.
  - eapply Nat.eqb_eq in E. lia.
  - clear E. unfold length in *.
    induction m as [| [i' a'] m]; trivial.
    fold (@length A) in *.
    destruct (Nat.eq_dec i i'); subst.
    + rewrite get_set_eq.

    induction m as [| [i' a'] m]; trivial.
    simpl. destruct (i =? i') eqn:E.
    + eapply Nat.eqb_eq in E; subst.
Admitted.

Lemma set_preserves_memory_length : forall {A} (m : mem A) i a,
  i < length m ->
  length m = length (set m i a).
Proof.
  intros * H. unfold set.
  destruct m as [|[i' a'] m]; try solve [inversion H].
  assert (forall x y, x < y -> y = max x y). {
    intros x. induction x; eauto.
    intros y. destruct y; try lia.
    eauto using eq_S, Lt.lt_S_n.
  }
  eauto.
Qed.

Lemma add_increments_memory_length : forall {A} (m : mem A) a,
  length (add m a) = length m.
Proof.
  intros. destruct m as [|[i a'] m]; trivial.
  simpl. destruct (max i (length m)); trivial.
  assert (forall x, max (S x) (S x) = S x).
  { intros. unfold max. induction x; eauto. }
  eauto.
Qed.

