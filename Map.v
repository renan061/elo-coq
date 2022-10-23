From Coq Require Import Strings.String.

Local Definition map' (A : Type) := string -> A. (* total map *)

Local Definition empty' {A : Type} v : map' A := (fun _ => v).

Local Definition update' {A : Type} (m : map' A) k v :=
  fun k' => if string_dec k k' then v else m k'.

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
  intros. unfold lookup, update, update'. eauto.
  destruct string_dec; trivial; contradiction.
Qed.

Lemma lookup_update_neq : forall {A} (m : map A) k k' v,
  k' <> k ->
  m[k' <== v] k = m k.
Proof.
  intros. unfold update, update'.
  destruct string_dec; trivial; subst. contradiction.
Qed.

(* ------------------------------------------------------------------------- *)
(* Equivalence                                                               *)
(* ------------------------------------------------------------------------- *)

Definition map_equivalence {A} (m1 m2 : map A) :=
  forall k, m1 k = m2 k.

Notation " m1 === m2 " := (map_equivalence m1 m2)
  (at level 70, no associativity).

Module MapEquivalence.
  Lemma refl : forall {A} (m : map A),
    m === m.
  Proof.
    unfold map_equivalence. intros. eauto.
  Qed.

  Lemma trans : forall {A} (m1 m2 m3 : map A),
    m1 === m2 ->
    m2 === m3 ->
    m1 === m3.
  Proof.
    unfold map_equivalence. intros * H1 H2 ?.
    rewrite (H1 _). rewrite (H2 _). trivial.
  Qed.

  Lemma sym : forall {A} (m1 m2 : map A),
    m1 === m2 ->
    m2 === m1.
  Proof.
    unfold map_equivalence. intros. eauto.
  Qed.

  Lemma lookup : forall {A} (m1 m2 : map A) k v,
    m1 === m2 ->
    m1 k = v ->
    m2 k = v. 
  Proof.
    intros * Heq ?. specialize (Heq k). inversion Heq. trivial.
  Qed.

  Lemma update_equivalence : forall {A} (m1 m2 : map A) k v,
    m1 === m2 ->
    m1[k <== v] === m2[k <== v].
  Proof.
    unfold map_equivalence, update, update'. intros.
    destruct string_dec; trivial.
  Qed.

  Lemma update_permutation : forall {A} (m : map A) k1 k2 v1 v2,
    k1 <> k2 ->
    m[k1 <== v1][k2 <== v2] === m[k2 <== v2][k1 <== v1].
  Proof.
    unfold map_equivalence, update, update'. intros.
    do 2 (destruct string_dec; subst); trivial.
    contradiction.
  Qed.

  Lemma update_overwrite : forall {A} (m : map A) k v v',
    m[k <== v] === m[k <== v'][k <== v].
  Proof.
    unfold map_equivalence, update, update'. intros.
    destruct string_dec; intros; trivial.
  Qed.
End MapEquivalence.

(* ------------------------------------------------------------------------- *)
(* Inclusion                                                                 *)
(* ------------------------------------------------------------------------- *)

(* m includes m' *)
Definition inclusion {A} (m m' : map A) := forall k v,
  m' k = Some v -> m k = Some v.

Infix "includes" := inclusion (at level 70, no associativity).

Module MapInclusion.
  Lemma refl : forall {A} (m : map A),
    m includes m.
  Proof.
    unfold inclusion. intros. eauto.
  Qed.

  Lemma trans : forall {A} (m1 m2 m3 : map A),
    m1 includes m2 ->
    m2 includes m3 ->
    m1 includes m3.
  Proof.
    unfold inclusion. intros * H1 H2 ? ? ?.
    rewrite (H1 k v); trivial. rewrite (H2 k v); trivial.
  Qed.

  Lemma antisym : forall {A} (m1 m2 : map A),
    m1 includes m2 ->
    m2 includes m1 ->
    m1 = m2.
  Proof.
  Abort.

  Lemma update_inclusion : forall {A} (m m' : map A) k v,
    m includes m' ->
    m[k <== v] includes m'[k <== v].
  Proof.
    unfold inclusion, update, update'. intros.
    destruct string_dec; eauto.
  Qed.

  Lemma update_permutation : forall {A} (m : map A) k1 k2 v1 v2,
    k1 <> k2 ->
    m[k1 <== v1][k2 <== v2] includes m[k2 <== v2][k1 <== v1].
  Proof.
    unfold inclusion, update, update'. intros.
    do 2 (destruct string_dec; subst); trivial. contradiction.
  Qed.

  Lemma update_overwrite : forall {A} (m : map A) k v v',
    m[k <== v] includes m[k <== v'][k <== v].
  Proof.
    unfold inclusion, update, update'. intros.
    destruct string_dec; trivial.
  Qed.
End MapInclusion.

