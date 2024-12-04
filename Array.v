From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Elo Require Import Util.

Definition add {A} (l : list A) (a : A) := l ++ (a :: nil).

Definition get {A} (default : A) (l : list A) (i : nat) := nth i l default.

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

Notation "# l" := (length l)
  (at level 15).
Notation " l +++ a " := (add l a)
  (at level 50).
Notation " l '[' i ']' 'or' d " := (get d l i)
  (at level 9, i at next level).
Notation " l '[' i '<-' a ']' " := (set l i a)
  (at level 9, i at next level).

(* ------------------------------------------------------------------------- *)
(* length                                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma add_increments_length : forall {A} (l : list A) a,
  #(l +++ a) = S (#l).
Proof.
  intros. unfold add. rewrite last_length. reflexivity.
Qed.

Lemma set_preserves_length : forall {A} (l : list A) i a,
  #l[i <- a] = #l.
Proof.
  intros ?. induction l; trivial. destruct i; simpl; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* sigma lemmas                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma set_invalid_eq : forall {A} (l : list A) a,
  l[#l <- a] = l.
Proof.
  intros. induction l as [| ? ? IH]; trivial.
  simpl. rewrite IH. reflexivity.
Qed.

Lemma set_invalid_gt : forall {A} (l : list A) i a,
  #l < i ->
  l[i <- a] = l.
Proof.
  intros * Hgt. generalize dependent i. induction l as [| ? ? IH]; trivial.
  intros. destruct i.
  - inv Hgt.
  - simpl in *. eapply lt_S_n in Hgt. rewrite IH; eauto.
Qed.

Lemma set_invalid_ge : forall {A} (l : list A) i a,
  #l <= i ->
  l[i <- a] = l.
Proof.
  intros * Hge. eapply le_lt_or_eq in Hge as [? | ?]; subst;
  eauto using set_invalid_eq, set_invalid_gt.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma get_default_eq : forall {A} d (l : list A),
  l[#l] or d = d.
Proof.
  intros. induction l; eauto.
Qed.

Lemma get_default_gt : forall {A} d (l : list A) i,
  #l < i ->
  l[i] or d = d.
Proof.
  intros * Hgt. generalize dependent i. induction l; intros;
  destruct i; eauto using lt_S_n; inv Hgt.
Qed.

Lemma get_default_ge : forall {A} d (l : list A) i,
  #l <= i ->
  l[i] or d = d.
Proof.
  intros * Hge. eapply le_lt_or_eq in Hge as [? | ?]; subst;
  eauto using get_default_eq, get_default_gt.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma add_get_eq : forall {A} d (l : list A) a,
  (l +++ a)[#l] or d = a.
Proof.
  intros. induction l; eauto.
Qed.

Lemma add_get_lt : forall {A} d (l : list A) i a,
  i < #l ->
  (l +++ a)[i] or d = l[i] or d.
Proof.
  intros. generalize dependent i. induction l; intros ?.
  - intros H. destruct i; inversion H.
  - simpl. intros H. destruct i; trivial.
    eapply PeanoNat.Nat.succ_lt_mono in H. eauto.
Qed.

Lemma add_get_gt : forall {A} d (l : list A) i a,
  #l < i ->
  (l +++ a)[i] or d = d.
Proof.
  intros. generalize dependent i. induction l; intros ? H;
  destruct i; try solve [inversion H].
  - destruct i; trivial.
  - simpl. eapply PeanoNat.Nat.succ_lt_mono in H. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma set_get_eq : forall {A} d (l : list A) i a,
  i < #l ->
  l[i <- a][i] or d = a.
Proof.
  intros ? ? l. induction l as [| ? ? IH]; intros * Hlen;
  try solve [inversion Hlen]. destruct i; unfold get; trivial.
  simpl in Hlen. rewrite <- Nat.succ_lt_mono in Hlen. eapply IH. assumption.
Qed.

Lemma set_get_neq : forall {A} d (l : list A) i j a,
  i <> j ->
  l[j <- a][i] or d = l[i] or d.
Proof.
  intros ? ? l.
  induction l as [| x xs IH]; intros * H; trivial.
  destruct i, j; trivial; try contradiction.
  simpl. eauto using PeanoNat.Nat.succ_inj_wd_neg.
Qed.

Lemma set_get_lt : forall {A} d (l : list A) i j a,
  i < j ->
  l[j <- a][i] or d = l[i] or d.
Proof.
  intros. eapply set_get_neq. lia. 
Qed.

Lemma set_get_gt : forall {A} d (l : list A) i j a,
  j < i ->
  l[j <- a][i] or d = l[i] or d.
Proof.
  intros. eapply set_get_neq. lia.
Qed.

Corollary set_get_invalid_eq : forall {A} d (l : list A) i a,
  l[i <- a][#l] or d = d.
Proof.
  intros. rewrite <- (set_preserves_length l i a). eauto using get_default_eq.
Qed.

Corollary set_get_invalid_gt : forall {A} d (l : list A) i j a,
  #l < i ->
  l[j <- a][i] or d = d.
Proof.
  intros. eapply get_default_gt. rewrite set_preserves_length. assumption.
Qed.

Corollary set_get_invalid_ge : forall {A} d (l : list A) i j a,
  #l <= i ->
  l[j <- a][i] or d = d.
Proof.
  intros. eapply get_default_ge. rewrite set_preserves_length. assumption.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma set_add_get_eq : forall {A} d (l : list A) i' a a',
  (l[i' <- a'] +++ a)[#l] or d = a.
Proof.
  intros.
  erewrite <- set_preserves_length. rewrite add_get_eq.
  reflexivity.
Qed.

Lemma set_add_get_lt : forall {A} d (l : list A) i i' a a',
  i < #l ->
  (l[i' <- a'] +++ a)[i] or d = l[i' <- a'][i] or d.
Proof.
  intros. rewrite add_get_lt; trivial.
  rewrite set_preserves_length. assumption.
Qed.

Lemma set_add_get_gt : forall {A} d (l : list A) i i' a a',
  #l < i ->
  (l[i' <- a'] +++ a)[i] or d = d.
Proof.
  intros.
  rewrite add_get_gt; trivial. rewrite set_preserves_length.
  assumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* sigma simplification                                                      *)
(* ------------------------------------------------------------------------- *)

Ltac sigma_once :=
  match goal with
  (* ---------------------------------------- *)
  (* length-add -- #(l +++ a)                 *)
  (* ---------------------------------------- *)
  | H : context C [ #(_ +++ _) ] |- _ => rewrite add_increments_length in H
  |  |- context C [ #(_ +++ _) ]      => rewrite add_increments_length
  (* ---------------------------------------- *)
  (* length-set -- #(l[i <- a])               *)
  (* ---------------------------------------- *)
  | H : context C [ #(_[_ <- _]) ] |- _ => rewrite set_preserves_length in H
  |  |- context C [ #(_[_ <- _]) ]      => rewrite set_preserves_length
  (* ---------------------------------------- *)
  (* get -- l[i]                              *)
  (* ---------------------------------------- *)
  (* get (i == #l) *)
  | H : context C [ ?l[#?l] or ?d] |- _ => rewrite (get_default_eq d l) in H
  | |-  context C [ ?l[#?l] or ?d]      => rewrite (get_default_eq d l)
  (* get (i > #l) *)
  | Hlen : #?l < ?i, H : context C [ ?l[?i] or ?d] |- _ => 
    rewrite (get_default_gt d l i Hlen) in H
  | Hlen : #?l < ?i  |-  context C [ ?l[?i] or ?d] => 
    rewrite (get_default_gt d l i Hlen)
  (* get (i >= #l) *)
  | Hlen : #?l <= ?i, H : context C [ ?l[?i] or ?d] |- _ => 
    rewrite (get_default_ge d l i Hlen) in H
  | Hlen : #?l <= ?i  |-  context C [ ?l[?i] or ?d] => 
    rewrite (get_default_ge d l i Hlen)
  (* ---------------------------------------- *)
  (* set -- l[i <- a]                         *)
  (* ---------------------------------------- *)
  (* set (i == #l) *)
  | H : context C [ ?l[?i <- ?a] ] |- _ => rewrite (set_invalid_eq l) in H
  | |-  context C [ ?l[?i <- ?a] ]      => rewrite (set_invalid_eq l)
  (* set (i > #l) *)
  | Hlen : #?l < ?i, H : context C [ ?l[?i <- ?a] ] |- _ => 
    rewrite (set_invalid_gt l i a Hlen) in H
  | Hlen : #?l < ?i  |-  context C [ ?l[?i <- ?a] ] => 
    rewrite (set_invalid_gt l i a Hlen)
  (* set (i >= #l) *)
  | Hlen : #?l <= ?i, H : context C [ ?l[?i <- ?a] ] |- _ => 
    rewrite (set_invalid_ge l i a Hlen) in H
  | Hlen : #?l <= ?i  |-  context C [ ?l[?i <- ?a] ] => 
    rewrite (set_invalid_ge l i a Hlen)
  (* ---------------------------------------- *)
  (* add-get -- (l +++ a)[i]                  *)
  (* ---------------------------------------- *)
  (* add-get (i == #l *)
  | H : context C [ (?l +++ ?a)[#?l] or ?d ] |- _ =>
    rewrite (add_get_eq d l a) in H
  | |-  context C [ (?l +++ ?a)[#?l] or ?d ] =>
    rewrite (add_get_eq d l a)
  (* add-get (i < #l) *)
  | Hlen : ?i < #?l, H : context C [ (?l +++ ?a)[?i] or ?d ] |- _ =>
    rewrite (add_get_lt d l i a Hlen) in H
  | Hlen : ?i < #?l  |-  context C [ (?l +++ ?a)[?i] or ?d ] =>
    rewrite (add_get_lt d l i a Hlen)
  (* add-get (i > #l) *)
  | Hlen : #?l < ?i, H : context C [ (?l +++ ?a)[?i] or ?d ] |- _ =>
    rewrite (add_get_gt d l i a Hlen) in H
  | Hlen : #?l < ?i  |-  context C [ (?l +++ ?a)[?i] or ?d ] =>
    rewrite (add_get_gt d l i a Hlen)
  (* ---------------------------------------- *)
  (* set-get -- l[j <- a][i]                  *)
  (* ---------------------------------------- *)
  (* set-get (i < #l and i == j) *)
  | Hlen : ?i < #?l, H : context C [ ?l[?i <- ?a ][?i] or ?d ] |- _ =>
    rewrite (set_get_eq d l i a Hlen) in H
  | Hlen : ?i < #?l  |-  context C [ ?l[?i <- ?a ][?i] or ?d ] =>
    rewrite (set_get_eq d l i a Hlen)
  (* set-get (i < #l and i <> j) *)
  | Hlen : ?i <> ?j, H : context C [ ?l[?j <- ?a ][?i] or ?d ] |- _ =>
    rewrite (set_get_neq d l i j a Hlen) in H
  | Hlen : ?j <> ?i, H : context C [ ?l[?j <- ?a ][?i] or ?d ] |- _ =>
    eapply not_eq_sym in Hlen
  | Hlen : ?i <> ?j  |-  context C [ ?l[?j <- ?a ][?i] or ?d ] =>
    rewrite (set_get_neq d l i j a Hlen)
  | Hlen : ?j <> ?i  |-  context C [ ?l[?j <- ?a ][?i] or ?d ] =>
    eapply not_eq_sym in Hlen
  (* set-get (i < j) *)
  | Hlen : ?i < ?j, H : context C [ ?l[?j <- ?a ][?i] or ?d ] |- _ =>
    rewrite (set_get_lt d l i j a Hlen) in H
  | Hlen : ?i < ?j  |-  context C [ ?l[?j <- ?a ][?i] or ?d ] =>
    rewrite (set_get_lt d l i j a Hlen)
  (* set-get (i > j) *)
  | Hlen : ?j < ?i, H : context C [ ?l[?j <- ?a ][?i] or ?d ] |- _ =>
    rewrite (set_get_gt d l i j a Hlen) in H
  | Hlen : ?j < ?i  |-  context C [ ?l[?j <- ?a ][?i] or ?d ] =>
    rewrite (set_get_gt d l i j a Hlen)
  (* set-get (i == #l) *)
  | H : context C [ ?l[?j <- ?a ][(# ?l)] or ?d ] |- _ =>
    rewrite (set_get_invalid_eq d l j a) in H
  | |-  context C [ ?l[?j <- ?a ][(# ?l)] or ?d ] =>
    rewrite (set_get_invalid_eq d l j a)
  (* ---------------------------------------- *)
  (* set-add-get -- l[i' <- a' +++ a][i]      *)
  (* ---------------------------------------- *)
  (* set-add-get (i == #l) *)
  | H : context C [ (?l[?i' <- ?a'] +++ ?a)[#?l] or ?d ] |- _ =>
    rewrite (set_add_get_eq d l i' a a') in H
  | |-  context C [ (?l[?i' <- ?a'] +++ ?a)[#?l] or ?d ] =>
    rewrite (set_add_get_eq d l i' a a')
  (* set-add-get (i < #l) *)
  | Hlen : ?i < #?l, H : context C [ (?l[?i' <- ?a'] +++ ?a)[?i] or ?d ] |- _ =>
    rewrite (set_add_get_lt d l i i' a a' Hlen) in H
  | Hlen : ?i < #?l   |- context C [ (?l[?i' <- ?a'] +++ ?a)[?i] or ?d ] =>
    rewrite (set_add_get_lt d l i i' a a' Hlen)
  (* set-add-get (i > #l) *)
  | Hlen : #?l < ?i, H : context C [ (?l[?i' <- ?a'] +++ ?a)[?i] or ?d ] |- _ =>
    rewrite (set_add_get_gt d l i i' a a' Hlen) in H
  | Hlen : #?l < ?i   |- context C [ (?l[?i' <- ?a'] +++ ?a)[?i] or ?d ] =>
    rewrite (set_add_get_gt d l i i' a a' Hlen)
  end.

Ltac sigma := repeat sigma_once.

(* ------------------------------------------------------------------------- *)
(* omicron split                                                             *)
(* ------------------------------------------------------------------------- *)

Local Ltac split_set_add_get l i1 i2 :=
  nat_eq_dec i1 i2; lt_eq_gt i2 (#l); sigma; try lia.

Local Ltac split_set_get_eq l i :=
  decompose sum (le_lt_dec (#l) i); sigma.

Local Ltac split_set_get i1 i2 :=
  nat_eq_dec i1 i2; sigma; try lia.

Local Ltac split_add_get l i :=
  decompose sum (lt_eq_lt_dec i (#l)); subst; sigma.

Ltac omicron :=
  sigma;
  match goal with
  (* set-add-get *)
  | _ : context C [ (?l[?i1 <- _] +++ _)[?i2] or _ ] |- _ =>
    split_set_add_get l i1 i2
  | |-  context C [ (?l[?i1 <- _] +++ _)[?i2] or _ ] =>
    split_set_add_get l i1 i2
  (* set-get-eq -- l[i <- a][i] *)
  | _ : context C [ ?l[?i <- _][?i] or _ ] |- _ =>
    split_set_get_eq l i
  | |-  context C [ ?l[?i <- _][?i] or _ ] =>
    split_set_get_eq l i
  (* set-get -- l[i1 <- a][i2] (i1 <> i2) *)
  | _ : context C [ _[?i1 <- _][?i2] or _ ] |- _ =>
    split_set_get i1 i2
  | |-  context C [ _[?i1 <- _][?i2] or _ ] =>
    split_set_get i1 i2
  (* add-get *)
  | _ : context C [ (?l +++ _)[?i] or _ ] |- _ =>
    split_add_get l i
  | |-  context C [ (?l +++ _)[?i] or _ ] =>
    split_add_get l i
  end.

(* ------------------------------------------------------------------------- *)
(* sigma tests                                                               *)
(* ------------------------------------------------------------------------- *)

Local Ltac test_with T :=
  intros; T; reflexivity.

Local Lemma test_rewrite_get_default1 : forall {A} d (l : list A) i,
  #l < i ->
  l[i] or d = d.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_get_default2 : forall {A} d (l : list A),
  l[#l] or d = d.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_set_invalid : forall {A} (l : list A) i a,
  #l <= i ->
  l[i <- a] = l.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_add_get_eq : forall {A} d (l : list A) a,
  (l +++ a)[#l] or d = a.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_add_get_lt : forall {A} d (l : list A) i a,
  i < #l ->
  (l +++ a)[i] or d = l[i] or d.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_add_get_gt : forall {A} d (l : list A) i a,
  #l < i ->
  (l +++ a)[i] or d = d.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_set_get_eq : forall {A} d (l : list A) i a,
  i < #l ->
  l[i <- a][i] or d = a.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_set_get_neq1 : forall {A} d (l : list A) i j a,
  i <> j ->
  l[j <- a][i] or d = l[i] or d.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_set_get_neq2 : forall {A} d (l : list A) i j a,
  j <> i ->
  l[j <- a][i] or d = l[i] or d.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_set_get_lt : forall {A} d (l : list A) i j a,
  i < j ->
  l[j <- a][i] or d = l[i] or d.
Proof. test_with sigma. Qed.

Local Lemma test_rewrite_set_get_gt : forall {A} d (l : list A) i j a,
  j < i ->
  l[j <- a][i] or d = l[i] or d.
Proof. test_with sigma. Qed.

(* ------------------------------------------------------------------------- *)
(* forall                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition forall_array {A} (d : A) (P : A -> Prop) (l : list A) : Prop :=
  forall i, P (l[i] or d).

(* TODO: Am I using this?

Lemma forall_array_add : forall {A} (P : A -> Prop) d l a,
  P d ->
  P a ->
  forall_array d P l ->
  forall_array d P (l +++ a).
Proof.
  intros ** ?. omicron; trivial.
Qed.

Lemma forall_array_set : forall {A} (P : A -> Prop) d l i a,
  P d ->
  P a ->
  forall_array d P l ->
  forall_array d P l[i <- a].
Proof.
  intros ** ?. do 2 (omicron; trivial).
Qed.

*)

(* ------------------------------------------------------------------------- *)
(* misc. lemmas                                                              *)
(* ------------------------------------------------------------------------- *)

(* TODO: Are these being used?

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
  rewrite Heql1 in Heq. rewrite Heql2 in Heq. sigma. lia.
Qed.

Lemma add_inv_head : forall {A} (l : list A) a1 a2,
  l +++ a1 = l +++ a2 ->
  a1 = a2.
Proof.
  unfold add. intros * H. eapply app_inv_head in H. inversion H. reflexivity.
Qed.
 
*)

