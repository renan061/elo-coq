From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Elo Require Export Array.

Local Definition map' (A : Type) := string -> A. (* total map *)

Local Definition empty' {A : Type} v : map' A := (fun _ => v).

Local Definition update' {A : Type} (m : map' A) k v :=
  fun k' => if String.eqb k k' then v else m k'.

Definition map (A : Type) := map' (option A). (* partial map *)

Definition empty {A : Type} : map A := empty' None.

Definition update {A : Type} (m : map A) k v :=
  update' m k (Some v).

Definition lookup {A : Type} (m : map A) k := m k.

(* Proofs *)

Local Lemma lookup_update_involutive' : forall {A} (m : map A) k v,
  (update m k v) k = Some v.
Proof.
  intros.
  unfold update, Map.update'.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

(* TODO : names *)
Lemma lookup_update_involutive : forall {A} (m : map A) k v,
  lookup (update m k v) k = Some v.
Proof.
  unfold lookup. intros.
  apply lookup_update_involutive'.
Qed.

(* TODO : names *)
Lemma lookup_update_idempotent : forall {A} (m : map A) k k' v,
  k' <> k ->
  lookup (update m k' v) k = lookup m k.
Proof.
  intros * H.
  unfold lookup, update, update'.
  destruct (String.eqb k' k) eqn:E.
  - apply String.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

(* m includes m' *)
Definition includes' {A} (m m' : map A) := forall k v,
  m' k = Some v -> m k = Some v.

Infix "includes" := includes' (at level 50, left associativity).

Lemma update_preserves_inclusion : forall {A} (m m' : map A) k v,
  m includes m' ->
  (update m k v) includes (update m' k v).
Proof.
  unfold includes'.
  intros * H k' v' H'.
  unfold update, update' in *.
  destruct (String.eqb k k') eqn:E.
  - assumption.
  - specialize (H k' v'). auto.
Qed.

Lemma update_permutation : forall {A} (m : map A) k1 k2 v1 v2,
  k1 <> k2 ->
  update (update m k1 v1) k2 v2 includes update (update m k2 v2) k1 v1.
Proof.
  unfold includes'. intros * H k v.
  unfold update, update'.
  destruct (String.eqb k1 k) eqn:E1;
  destruct (String.eqb k2 k) eqn:E2;
  auto.
  apply String.eqb_eq in E1, E2. subst. contradiction.
Qed.

Lemma update_overwrite : forall {A} (m : map A) k v v',
  update m k v includes update (update m k v') k v.
Proof.
  intros * k' m'.
  unfold update, update'.
  destruct (String.eqb k k') eqn:E1; intros; assumption.
Qed.

Lemma update_empty : forall {A} k1 k2 (v1 v2 : A),
  k1 <> k2 ->
  update (update empty k1 v1) k2 v2 includes (update empty k1 v1).
Proof.
  intros * Hneq.
  unfold includes'. intros k v.
  unfold update, Map.update'.
  destruct (String.eqb k1 k) eqn:E1, (String.eqb k2 k) eqn:E2.
  - apply String.eqb_eq in E1, E2. subst. contradiction.
  - trivial.
  - unfold empty, Map.empty'. intros F. inversion F.
  - unfold empty, Map.empty'. intros F. inversion F.
Qed.
