From Coq Require Import Strings.String.

Local Definition map' (A : Type) := string -> A. (* total map *)

Local Definition empty' {A : Type} v : map' A := (fun _ => v).

Local Definition update' {A : Type} (m : map' A) k v :=
  fun k' => if eqb k k' then v else m k'.

Definition map (A : Type) := map' (option A). (* partial map *)

Definition empty {A : Type} : map A := empty' None.

Definition update {A : Type} (m : map A) k v :=
  update' m k (Some v).

Definition lookup {A : Type} (m : map A) k := m k.

Notation "m '[' k '<==' v ']'" := (update m k v) (at level 9).

(* ------------------------------------------------------------------------- *)
(* Proofs                                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma lookup_update_eq : forall {A} (m : map A) k v,
  m[k <== v] k = Some v.
Proof.
  intros. unfold lookup, update, update'.
  rewrite eqb_refl. reflexivity.
Qed.

Lemma lookup_update_neq : forall {A} (m : map A) k k' v,
  k' <> k ->
  m[k' <== v] k = m k.
Proof.
  intros. unfold update, update'.
  destruct eqb eqn:E; trivial.
  apply eqb_eq in E. contradiction.
Qed.

(* ------------------------------------------------------------------------- *)
(* Equivalence                                                               *)
(* ------------------------------------------------------------------------- *)

Definition equivalent {A} (m1 m2 : map A) :=
  forall k, m1 k = m2 k.

Lemma equivalent_refl : forall {A} (m1 m2 : map A),
  equivalent m1 m2 ->
  equivalent m2 m1.
Proof.
  unfold equivalent in *. intros. eauto.
Qed.

Lemma equivalent_trans : forall {A} (m1 m2 m3 : map A),
  equivalent m1 m2 ->
  equivalent m2 m3 ->
  equivalent m1 m3.
Proof.
  unfold equivalent in *. intros * H ? *. rewrite H. eauto.
Qed.

Lemma equivalent_lookup : forall {A} (m1 m2 : map A) k v,
  equivalent m1 m2 ->
  m1 k = v ->
  m2 k = v. 
Proof.
  intros * Heq ?. specialize (Heq k). inversion Heq. trivial.
Qed.

Lemma equivalent_update : forall {A} (m1 m2 : map A) k v,
  equivalent m1 m2 ->
  equivalent m1[k <== v] m2[k <== v].
Proof.
  unfold equivalent, update, update'. intros. destruct eqb; eauto.
Qed.

Lemma equivalent_update_permutation : forall {A} (m : map A) k1 k2 v1 v2,
  k1 <> k2 ->
  equivalent m[k1 <== v1][k2 <== v2] m[k2 <== v2][k1 <== v1].
Proof.
  unfold equivalent, update, update'. intros.
  destruct (eqb k1 k) eqn:E1; destruct (eqb k2 k) eqn:E2; auto.
  apply eqb_eq in E1, E2. subst. contradiction.
Qed.

Lemma equivalent_update_overwrite : forall {A} (m : map A) k v v',
  equivalent m[k <== v] m[k <== v'][k <== v].
Proof.
  unfold equivalent, update, update'. intros.
  destruct eqb; intros; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* Inclusion                                                                 *)
(* ------------------------------------------------------------------------- *)

(* m includes m' *)
Definition includes' {A} (m m' : map A) := forall k v,
  m' k = Some v -> m k = Some v.

Infix "includes" := includes' (at level 50, left associativity).

Lemma inclusion_update : forall {A} (m m' : map A) k v,
  m includes m' ->
  m[k <== v] includes m'[k <== v].
Proof.
  unfold includes', update, update'. intros. destruct eqb; auto.
Qed.

Lemma inclusion_update_permutation : forall {A} (m : map A) k1 k2 v1 v2,
  k1 <> k2 ->
  m[k1 <== v1][k2 <== v2] includes m[k2 <== v2][k1 <== v1].
Proof.
  unfold includes', update, update'. intros.
  destruct (eqb k1 k) eqn:E1; destruct (eqb k2 k) eqn:E2; auto.
  apply eqb_eq in E1, E2. subst. contradiction.
Qed.

Lemma inclusion_update_overwrite : forall {A} (m : map A) k v v',
  m[k <== v] includes m[k <== v'][k <== v].
Proof.
  unfold includes', update, update'. intros.
  destruct eqb; intros; assumption.
Qed.

