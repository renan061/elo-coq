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

Lemma lookup_update_involutive' : forall {A} (m : map A) k v,
  update m k v k = Some v.
Proof.
  intros.
  unfold update, Map.update'.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma lookup_update_involutive : forall {A} (m : map A) k v,
  lookup (update m k v) k = Some v.
Proof.
  unfold lookup.
  intros.
  apply lookup_update_involutive'.
Qed.

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

