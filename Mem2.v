From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List.

(*
Ltac destruct_access_H H :=
  idtac H;
  match type of H with
    | access _ TM_Nil _ => inversion H
    | access _ (TM_Num _) _ => inversion H
    | access _ (TM_New _) _ => eapply new_access in H
  end.
*)

Inductive mem {A : Type} : nat -> list (nat * A) -> Prop :=
  | empty : mem 0 nil

  | add : forall n m a,
    mem n m ->
    mem (S n) ((n, a) :: m) 

  | set : forall n m i a,
    mem n m ->
    i < n ->
    mem n ((i, a) :: m) 
  .

Definition length {A} n (l : list (nat * A)) (m : mem n l) :=
  n.

Definition get {A} n (l : list (nat * A)) (m : mem n l) :=
  match m with
  | empty => None
  | add n' m' a H => None
  | set n' m' i a H1 H2 => None
  end.

(* Proofs *)

Lemma get_set_eq : forall {A} n (l : list (nat * A)) (m : mem n l) i a,
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
(*
    induction m as [| [i' a'] m]; trivial.
    simpl. destruct (i =? i') eqn:E.
    + eapply Nat.eqb_eq in E; subst.
*)
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
  simpl.
  eapply eq_S.
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

