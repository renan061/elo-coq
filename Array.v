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

(* ------------------------------------------------------------------------- *)
(* notations                                                                 *)
(* ------------------------------------------------------------------------- *)

Notation "# l" := (length l) (at level 15).
Notation " l +++ a " := (add l a) (at level 50).
Notation " l '[' i ']' 'or' default " := (get default l i)
  (at level 9, i at next level).
Notation " l '[' i <- a ']' " := (set l i a)
  (at level 9, i at next level, a at next level).

(* ------------------------------------------------------------------------- *)
(* proofs                                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma set_invalid : forall {A} (l : list A) i a,
  #l <= i ->
  l[i <- a] = l.
Proof.
  intros *. generalize dependent i.
  induction l as [| ? ? IH]; intros * H; trivial.
  simpl. destruct i; try solve [inversion H].
  simpl in H. eapply le_S_n in H.
  rewrite IH; eauto.
Qed.

Lemma set_preserves_length : forall {A} (l : list A) i a,
  #l[i <- a] = #l.
Proof.
  intros ?. induction l; trivial.
  destruct i; simpl; eauto.
Qed.

Lemma add_increments_length : forall {A} (l : list A) a,
  #(l +++ a) = S (#l).
Proof.
  intros. unfold add. rewrite last_length. reflexivity.
Qed.

Lemma add_length_neq : forall {A} (l : list A) a,
  l <> l +++ a.
Proof.
  intros. unfold add. induction l.
  - rewrite app_nil_l. discriminate.
  - intros F. inversion F. contradiction.
Qed.

Lemma add_set_length_neq : forall {A} (l : list A) i a1 a2,
  l[i <- a1] <> l +++ a2.
Proof.
  intros. intros F. remember (l[i <- a1]) as l1. remember (l +++ a2) as l2.
  assert (Heq : #l1 = #l2) by (rewrite F; reflexivity).
  rewrite Heql1 in Heq. rewrite set_preserves_length in Heq.
  rewrite Heql2 in Heq. rewrite add_increments_length in Heq.
  lia.
Qed.

Lemma add_inv_head : forall {A} (l : list A) a1 a2,
  l +++ a1 = l +++ a2 ->
  a1 = a2.
Proof.
  unfold add. intros * H. eapply app_inv_head in H. inversion H. reflexivity.
Qed.

Lemma get_default : forall {A} default (l : list A) i,
  #l <= i ->
  l[i] or default = default.
Proof.
  intros *. generalize dependent i.
  induction l as [| ? ? IH]; intros * H;
  simpl; destruct i; trivial;
  try solve [inversion H].
  simpl in H. eapply le_S_n in H.
  rewrite IH; eauto.
Qed.

Lemma get_set_eq : forall {A} default (l : list A) i a,
  i < #l ->
  l[i <- a][i] or default = a.
Proof.
  intros ? ? l. induction l as [| ? ? IH]; intros * Hlen;
  try solve [inversion Hlen]. destruct i; unfold get; trivial.
  simpl in Hlen. rewrite <- Nat.succ_lt_mono in Hlen. eapply IH. assumption.
Qed.

Lemma get_set_neq : forall {A} default (l : list A) i j a,
  i <> j ->
  l[j <- a][i] or default = l[i] or default.
Proof.
  intros ? ? l.
  induction l as [| x xs IH]; intros * H; trivial.
  destruct i, j; trivial; try contradiction.
  simpl. eauto using PeanoNat.Nat.succ_inj_wd_neg.
Qed.

Lemma get_set_lt : forall {A} default (l : list A) i j a,
  i < j ->
  l[j <- a][i] or default = l[i] or default.
Proof.
  intros. eapply get_set_neq. lia. 
Qed.

Lemma get_set_gt : forall {A} default (l : list A) i j a,
  j < i ->
  l[j <- a][i] or default = l[i] or default.
Proof.
  intros. eapply get_set_neq. lia.
Qed.

Lemma get_set_invalid : forall {A} default (l : list A) i a,
  #l <= i ->
  l[i <- a][i] or default = default.
Proof.
  intros * H. rewrite set_invalid; trivial. eauto using get_default.
Qed.

Corollary get_set_invalid_eq : forall {A} default (l : list A) a,
  l[#l <- a][#l] or default = default.
Proof.
  intros. assert (#l <= #l) by lia. eauto using get_set_invalid.
Qed.

Lemma get_add_eq : forall {A} default (l : list A) a,
  (l +++ a)[#l] or default = a.
Proof.
  intros. induction l; eauto.
Qed.

Lemma get_add_lt : forall {A} default (l : list A) i a,
  i < #l ->
  (l +++ a)[i] or default = l[i] or default.
Proof.
  intros. generalize dependent i. induction l; intros ?.
  - intros H. destruct i; inversion H.
  - simpl. intros H. destruct i; trivial.
    eapply PeanoNat.Nat.succ_lt_mono in H. eauto.
Qed.

Lemma get_add_gt : forall {A} default (l : list A) i a,
  #l < i ->
  (l +++ a)[i] or default = default.
Proof.
  intros. generalize dependent i. induction l; intros ? H;
  destruct i; try solve [inversion H].
  - destruct i; trivial.
  - simpl. eapply PeanoNat.Nat.succ_lt_mono in H. eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* rewrites & simpl                                                          *)
(* ------------------------------------------------------------------------- *)

Ltac rewrite_get_add_eq :=
  match goal with
  | H : context C [ (?l +++ ?a)[#?l] or ?d ] |- _ =>
    rewrite (get_add_eq d l a) in H
  | |-  context C [ (?l +++ ?a)[#?l] or ?d ] =>
    rewrite (get_add_eq d l a)
  end.

Ltac rewrite_get_add_lt :=
  match goal with
  | Hlen : ?i < #?l, H : context C [ (?l +++ ?a)[?i] or ?d ] |- _ =>
    rewrite (get_add_lt d l i a Hlen) in H
  | Hlen : ?i < #?l  |-  context C [ (?l +++ ?a)[?i] or ?d ] =>
    rewrite (get_add_lt d l i a Hlen)
  end.

Ltac rewrite_get_add_gt :=
  match goal with
  | Hlen : #?l < ?i, H : context C [ (?l +++ ?a)[?i] or ?d ] |- _ =>
    rewrite (get_add_gt d l i a Hlen) in H
  | Hlen : #?l < ?i  |-  context C [ (?l +++ ?a)[?i] or ?d ] =>
    rewrite (get_add_gt d l i a Hlen)
  end.

Ltac rewrite_get_set_eq :=
  match goal with
  | Hlen : ?i < #?l, H : context C [ ?l[?i <- ?a ][?i] or ?d ] |- _ =>
    rewrite (get_set_eq d l i a Hlen) in H
  | Hlen : ?i < #?l  |-  context C [ ?l[?i <- ?a ][?i] or ?d ] =>
    rewrite (get_set_eq d l i a Hlen)
  end.

Ltac rewrite_get_set_neq :=
  match goal with
  | Hlen : ?i <> ?j, H : context C [ ?l[?j <- ?a ][?i] or ?d ] |- _ =>
    rewrite (get_set_neq d l i j a Hlen) in H
  | Hlen : ?j <> ?i, H : context C [ ?l[?j <- ?a ][?i] or ?d ] |- _ =>
    eapply not_eq_sym in Hlen as Hlen';
    rewrite (get_set_neq d l i j a Hlen') in H;
    clear Hlen'
  | Hlen : ?i <> ?j  |-  context C [ ?l[?j <- ?a ][?i] or ?d ] =>
    rewrite (get_set_neq d l i j a Hlen)
  | Hlen : ?j <> ?i  |-  context C [ ?l[?j <- ?a ][?i] or ?d ] =>
    eapply not_eq_sym in Hlen as Hlen';
    rewrite (get_set_neq d l i j a Hlen');
    clear Hlen'
  end.

Ltac rewrite_get_set_lt :=
  match goal with
  | Hlen : ?i < ?j, H : context C [ ?l[?j <- ?a ][?i] or ?d ] |- _ =>
    rewrite (get_set_lt d l i j a Hlen) in H
  | Hlen : ?i < ?j  |-  context C [ ?l[?j <- ?a ][?i] or ?d ] =>
    rewrite (get_set_lt d l i j a Hlen)
  end.

Ltac rewrite_get_set_gt :=
  match goal with
  | Hlen : ?j < ?i, H : context C [ ?l[?j <- ?a ][?i] or ?d ] |- _ =>
    rewrite (get_set_gt d l i j a Hlen) in H
  | Hlen : ?j < ?i  |-  context C [ ?l[?j <- ?a ][?i] or ?d ] =>
    rewrite (get_set_gt d l i j a Hlen)
  end.

Ltac rewrite_get_set_invalid_eq :=
  match goal with
  | H : context C [ ?l[(# ?l) <- ?a ][(# ?l)] or ?d ] |- _ =>
    rewrite (get_set_invalid_eq d l a) in H
  | |-  context C [ ?l[(# ?l) <- ?a ][(# ?l)] or ?d ] =>
    rewrite (get_set_invalid_eq d l a)
  end.

Ltac rewrite_get_default :=
  match goal with
  | H : context C [ ?l[#?l] or ?d] |- _ => 
    assert (Hlen : #l <= #l) by eauto using Nat.eq_le_incl;
    rewrite (get_default d l (#l) Hlen) in H;
    clear Hlen
  | |-  context C [ ?l[#?l] or ?d] => 
    assert (Hlen : #l <= #l) by eauto using Nat.eq_le_incl;
    rewrite (get_default d l (#l) Hlen);
    clear Hlen
  | Hlen : #?l < ?i, H : context C [ ?l[?i] or ?d] |- _ => 
    rewrite (get_default d l i (Nat.lt_le_incl _ _ Hlen)) in H
  | Hlen : #?l < ?i  |-  context C [ ?l[?i] or ?d] => 
    rewrite (get_default d l i (Nat.lt_le_incl _ _ Hlen))
  end.

Ltac rewrite_set_invalid :=
  match goal with
  | Hlen : #?l <= ?i, H : context C [ ?l[?i <- ?a] ] |- _ => 
    rewrite (set_invalid l i a Hlen) in H
  | Hlen : #?l <= ?i  |-  context C [ ?l[?i <- ?a] ] => 
    rewrite (set_invalid l i a Hlen)
  | Hlen : #?l < ?i, H : context C [ ?l[?i <- ?a] ] |- _ => 
    rewrite (set_invalid l i a (Nat.lt_le_incl _ _ Hlen)) in H
  | Hlen : #?l < ?i  |-  context C [ ?l[?i <- ?a] ] => 
    rewrite (set_invalid l i a (Nat.lt_le_incl _ _ Hlen))
  end.

Ltac rewrite_get_add_set :=
  match goal with
  (* eq *)
  | H : context C [ (?l[?i' <- ?a'] +++ ?a)[#?l] or ?d ] |- _ =>
    rewrite <- (set_preserves_length _ i' a') in H
  | |- context C [ (?l[?i' <- ?a'] +++ ?a)[#?l] or ?d ] =>
    rewrite <- (set_preserves_length _ i' a')
  (* lt *)
  | Hlen : ?i < #?l,
    H : context C [ (?l[?i' <- ?a'] +++ ?a)[?i] or ?d ]
    |- _ =>
    rewrite <- (set_preserves_length _ i' a') in Hlen
  | Hlen : ?i < #?l
    |- context C [ (?l[?i' <- ?a'] +++ ?a)[?i] or ?d ] =>
    rewrite <- (set_preserves_length _ i' a') in Hlen
  (* gt *)
  | Hlen : #?l < ?i,
    H : context C [ (?l[?i' <- ?a'] +++ ?a)[?i] or ?d ]
    |- _ =>
    rewrite <- (set_preserves_length _ i' a') in Hlen
  | Hlen : #?l < ?i
    |- context C [ (?l[?i' <- ?a'] +++ ?a)[?i] or ?d ] =>
    rewrite <- (set_preserves_length _ i' a') in Hlen
  end.

Ltac simpl_array :=
  progress (repeat (rewrite_get_add_eq
  || rewrite_get_add_lt
  || rewrite_get_add_gt
  || rewrite_get_set_eq
  || rewrite_get_set_neq
  || rewrite_get_set_lt
  || rewrite_get_set_gt
  || rewrite_get_set_invalid_eq
  || rewrite_get_default
  || rewrite_set_invalid
  || rewrite_get_add_set
  )).

(* ------------------------------------------------------------------------- *)
(* forall                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition forall_array {A} (default : A) (P : A -> Prop) (l : list A) : Prop :=
  forall i, P (l[i] or default).

Lemma forall_array_add : forall {A} (P : A -> Prop) default l a,
  P default ->
  P a ->
  forall_array default P l ->
  forall_array default P (l +++ a).
Proof.
  intros ** i. decompose sum (lt_eq_lt_dec i (#l)); subst;
  simpl_array; trivial.
Qed.

Lemma forall_array_set : forall {A} (P : A -> Prop) default l i a,
  P default ->
  P a ->
  forall_array default P l ->
  forall_array default P l[i <- a].
Proof.
  intros; intros i'. decompose sum (lt_eq_lt_dec i i'); subst;
  decompose sum (le_lt_dec (#l) i');
  simpl_array; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* rewrite tests                                                             *)
(* ------------------------------------------------------------------------- *)

Local Ltac test_with T :=
  intros; T; reflexivity.

Local Lemma test_rewrite_get_add_eq : forall {A} default (l : list A) a,
  (l +++ a)[#l] or default = a.
Proof. intros. rewrite_get_add_eq. reflexivity. Qed.

Local Lemma test_rewrite_get_add_lt : forall {A} default (l : list A) i a,
  i < #l ->
  (l +++ a)[i] or default = l[i] or default.
Proof. intros. rewrite_get_add_lt. reflexivity. Qed.

Local Lemma test_rewrite_get_add_gt : forall {A} default (l : list A) i a,
  #l < i ->
  (l +++ a)[i] or default = default.
Proof. intros. rewrite_get_add_gt. reflexivity. Qed.

Local Lemma test_rewrite_get_set_eq : forall {A} default (l : list A) i a,
  i < #l ->
  l[i <- a][i] or default = a.
Proof. intros. rewrite_get_set_eq. reflexivity. Qed.

Local Lemma test_rewrite_get_set_neq1 : forall {A} default (l : list A) i j a,
  i <> j ->
  l[j <- a][i] or default = l[i] or default.
Proof. intros. rewrite_get_set_neq. reflexivity. Qed.

Local Lemma test_rewrite_get_set_neq2 : forall {A} default (l : list A) i j a,
  j <> i ->
  l[j <- a][i] or default = l[i] or default.
Proof. intros. rewrite_get_set_neq. reflexivity. Qed.

Local Lemma test_rewrite_get_set_lt : forall {A} default (l : list A) i j a,
  i < j ->
  l[j <- a][i] or default = l[i] or default.
Proof. intros. rewrite_get_set_lt. reflexivity. Qed.

Local Lemma test_rewrite_get_set_gt : forall {A} default (l : list A) i j a,
  j < i ->
  l[j <- a][i] or default = l[i] or default.
Proof. intros. rewrite_get_set_gt. reflexivity. Qed.

Local Lemma test_rewrite_get_default1 : forall {A} default (l : list A) i,
  #l < i ->
  l[i] or default = default.
Proof. intros. rewrite_get_default. reflexivity. Qed.

Local Lemma test_rewrite_get_default2 : forall {A} default (l : list A),
  l[#l] or default = default.
Proof. intros. rewrite_get_default. reflexivity. Qed.

Local Lemma test_rewrite_set_invalid : forall {A} (l : list A) i a,
  #l <= i ->
  l[i <- a] = l.
Proof. intros. rewrite_set_invalid. reflexivity. Qed.

