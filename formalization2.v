From Coq Require Init.Nat.
From Coq Require Import PeanoNat.

From Elo Require Export Array.
From Elo Require Export Map.

Definition name := String.string.
Definition num := nat.

(* Lemma get_length_Some : forall {A} (l : list A) i a,
  get l i = Some a ->
  i < length l.
Proof.
  intros A l i a. generalize dependent i.
  induction l; destruct i; try discriminate.
  - eauto using Nat.lt_0_succ.
  - eauto using Lt.lt_n_S.
Qed.
 *)
(* ************************************************************************** *)

(*
(* m includes m' *)
Definition includes {A : Type} (m m' : map A) := forall k (v : A),
  lookup m' k = Some v -> lookup m k = Some v.

Infix "includes" := includes (at level 50, left associativity).

(* update preserves map inclusion *)
Lemma inclusion_update : forall A m m' k (v : A),
  m includes m' ->
  (update m k v) includes (update m' k v).
Admitted.

Lemma weakening_delta : forall D mt Gamma Delta Delta' t T,
  Delta includes Delta' ->
  D / mt / (Delta', Gamma) |- t is T ->
  D / mt / (Delta, Gamma)  |- t is T.
Admitted.

Lemma weakening_gamma : forall D mt Gamma Gamma' Delta t T,
  Gamma includes Gamma' ->
  D / mt / (Delta, Gamma') |- t is T ->
  D / mt / (Delta, Gamma)  |- t is T.
Admitted.

Lemma weakening_empty_delta : forall D mt Gamma t T,
  D / mt / (nil, nil)   |- t is T ->
  D / mt / (nil, Gamma) |- t is T.
Admitted.

Lemma weakening_empty_gamma : forall D mt Delta t T,
  D / mt / (nil, nil)   |- t is T ->
  D / mt / (Delta, nil) |- t is T.
Admitted.

Lemma weakening_empty : forall D mt Delta Gamma t T,
  D / mt / (nil, nil)     |- t is T ->
  D / mt / (Delta, Gamma) |- t is T.
Admitted.

Lemma substitution_preserves_typing_gamma : forall D mt Gamma id t u T U,
  D / mt / (nil, update Gamma id U) |- t is T ->
  D / mt / (nil, nil) |- u is U ->
  D / mt / (nil, Gamma) |- [id := u] t is T.
Admitted.

Lemma substitution_preserves_typing_delta : forall D mt Delta id t u T U,
  D / mt / (update Delta id U, nil) |- t is T ->
  D / mt / (nil, nil) |- u is U ->
  D / mt / (Delta, nil) |- [id := u] t is T.
Admitted.
*)

(* ************************************************************************** *)

Theorem deterministic_types_manual : forall D mt Delta Gamma t X Y,
  D / mt / (Delta, Gamma) |- t is X ->
  D / mt / (Delta, Gamma) |- t is Y ->
  X = Y.
Proof.
  intros D mt Delta Gamma t X Y HX HY.
  induction HX; inversion HY; subst.
  - apply IHHX2. apply H9.
  - apply IHHX2. apply H9.
  - reflexivity.
  - congruence.
  - apply IHHX2. apply H5.
  - reflexivity.
  - reflexivity.
  - congruence.
  - rewrite H4 in H. discriminate H. (* congruence *)
  - rewrite H4 in H. discriminate H. (* congruence *)
  - rewrite H4 in H. discriminate H. (* congruence *)
  - congruence.
  - rewrite H6 in H0. discriminate H0. (* congruence *)
  - rewrite H4 in H. discriminate H. (* congruence *)
  - rewrite H6 in H0. discriminate H0. (* congruence *)
  - congruence.
  - congruence.
Qed.

(* ************************************************************************** *)

(* TODO *)

(*
Open Scope string_scope.

Theorem typechecks : forall D m Delta program,
  D / Delta |= program ->
  D / m ; Delta / nil |- TM_Call "main" TM_Nil is TY_Void.
Proof.
  intros D Delta program H.
Admitted.

Close Scope string_scope.
*)

(* ************************************************************************** *)
(* ************************************************************************** *)

(*

- Tirei ArrayConstructor => Assim não tem como construir array de tamanho
dinâmico,
    mas whatever.
- Tirei cast, pq whatever. Só existia cast de Int para Float.
- Tirei Call de stat, pq pode por no Asg. Tão expressivo quanto.
- Deixei Ret em asg, por conta do Ret dentro de spawn.
- Mudei array pra só ter um elemento. Pq não sabia fazer a semântica
operacional.
- Não tem recursão né? a averiguar!
- | TM_AsgArr (arr : name) (i : exp) (rhs : exp) => array é name!!! coisas
como
    [[0]][0][0] = 0; são desnecessárias. Não acredito que perde
expressividade. é
    só usar variáveis intermediárias para indexar usando arrays
intermediários.

*)
