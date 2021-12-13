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

(* Proofs *)

Lemma lookup_update_keq : forall {A} (m : map A) k v,
  lookup (update m k v) k = Some v.
Proof.
  intros. unfold lookup, update, update'.
  rewrite eqb_refl. reflexivity.
Qed.

Lemma lookup_update_kneq : forall {A} (m : map A) k k' v,
  k' <> k ->
  lookup (update m k' v) k = lookup m k.
Proof.
  intros. unfold lookup, update, update'.
  destruct eqb eqn:E; trivial.
  apply eqb_eq in E. contradiction.
Qed.

(* m includes m' *)
Definition includes' {A} (m m' : map A) := forall k v,
  m' k = Some v -> m k = Some v.

Infix "includes" := includes' (at level 50, left associativity).

Lemma update_preserves_inclusion : forall {A} (m m' : map A) k v,
  m includes m' ->
  (update m k v) includes (update m' k v).
Proof.
  unfold includes', update, update'. intros.
  destruct eqb; auto.
Qed.

Lemma update_permutation : forall {A} (m : map A) k1 k2 v1 v2,
  k1 <> k2 ->
  update (update m k1 v1) k2 v2 includes update (update m k2 v2) k1 v1.
Proof.
  unfold includes', update, update'. intros.
  destruct (eqb k1 k) eqn:E1; destruct (eqb k2 k) eqn:E2; auto.
  apply eqb_eq in E1, E2. subst. contradiction.
Qed.

Lemma update_overwrite : forall {A} (m : map A) k v v',
  (update m k v) includes (update (update m k v') k v).
Proof.
  unfold includes', update, update'. intros.
  destruct eqb; intros; assumption.
Qed.
