From Coq Require Import Strings.String.

Inductive map (A : Type) : Type :=
  | nil
  | cons (k : string) (v : A) (m : map A)
  .

Definition empty {A} := nil A.

Fixpoint update {A} (m : map A) k v :=
  match m with
  | nil _ => cons A k v (nil A)
  | cons _ k' v' m' =>
      if eqb k k'
        then cons A k  v  (update m' k v)
        else cons A k' v' (update m' k v)
  end.

Local Definition update' {A} m k v := cons A k v m.

Fixpoint lookup {A} m k : option A :=
  match m with
  | nil _ => None
  | cons _ k' v m' => if eqb k' k then Some v else lookup m' k
  end.

Theorem update_equivalence : forall {A} (m : map A) k v id,
  lookup (update m k v) id = lookup (update' m k v) id.
Proof.
  intros *. unfold update', update.
  induction m as [| k' v' m IH]; trivial.
  unfold lookup in *.
  destruct (eqb k k') eqn:E1.
  - apply eqb_eq in E1. subst. destruct (eqb k' id); trivial.
  - destruct (eqb k' id) eqn:E2; trivial.
    apply eqb_eq in E2. subst.
    destruct (eqb k id) eqn:E3; trivial; discriminate.
Qed.

Corollary update_equivalence_impl : forall {A} (m : map A) k k' v v',
  lookup (update m k' v') k = Some v <-> lookup (update' m k' v') k = Some v.
Proof.
  intros *. rewrite update_equivalence. split; trivial.
Qed.

Lemma lookup_update_k_eq : forall {A} (m : map A) k v,
  lookup (update m k v) k = Some v.
Proof.
  intros. rewrite update_equivalence.
  simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_k_neq : forall {A} (m : map A) k k' v,
  k' <> k ->
  lookup (update m k' v) k = lookup m k.
Proof.
  intros * H. rewrite update_equivalence.
  simpl. destruct eqb eqn:E; trivial.
  apply String.eqb_eq in E. contradiction.
Qed.

(* m includes m' *)
Local Definition includes_definition {A} (m m' : map A) :=
  forall k v, lookup m' k = Some v -> lookup m k = Some v.

Infix "includes" := includes_definition (at level 50, left associativity).

Lemma update_preserves_inclusion : forall {A} (m m' : map A) k v,
  m includes m' ->
  (update m k v) includes (update m' k v).
Proof.
  intros * ? k' ? H.
  unfold includes_definition in *. 
  rewrite update_equivalence in *.
  unfold lookup, update' in *.
  destruct m; destruct (eqb k k'); eauto.
Qed.

Lemma update_overwrite : forall {A} (m : map A) k v v',
  (update m k v) includes (update (update m k v') k v).
Proof.
  intros *. unfold includes_definition. intros k' ?.
  rewrite 2 update_equivalence.
  unfold lookup, update'.
  destruct m; intros H; destruct (eqb k k') eqn:E; trivial;
  rewrite update_equivalence in H;
  unfold lookup, update' in H;
  rewrite E in H; assumption.
Qed.

Lemma update_permutation : forall {A} (m : map A) k1 k2 v1 v2,
  k1 <> k2 ->
  (update' (update' m k1 v1) k2 v2) includes (update' (update' m k2 v2) k1 v1).
Proof.
  intros * Hneq. unfold includes_definition.
  induction m as [| ? ? ? IH]; intros k' v'.
  - unfold update', lookup.
    destruct (eqb k1 k') eqn:E1; trivial.
    destruct (eqb k2 k') eqn:E2; trivial.
    apply eqb_eq in E1. apply eqb_eq in E2. subst.
    contradiction.
  - specialize (IH k' v').
    destruct (eqb k1 k') eqn:E1.
    + apply eqb_eq in E1. subst.
      destruct (eqb k2 k') eqn:E2.
      * apply eqb_eq in E2. subst. rewrite 2 lookup_update_k_eq in *. trivial.
      * apply eqb_neq in E2.
        rewrite (lookup_update_k_neq _ _ _ _ E2).
        rewrite 2 lookup_update_k_eq in *.
        intros H. specialize (IH H).
        assumption.
    + apply eqb_neq in E1.
      rewrite (lookup_update_k_neq _ _ _ _ E1) in *.
      destruct (eqb k2 k') eqn:E2.
      * apply eqb_eq in E2. subst. rewrite 2 lookup_update_k_eq. trivial.
      * apply eqb_neq in E2.
        rewrite 2 (lookup_update_k_neq _ _ _ _ E2) in *.
        rewrite (lookup_update_k_neq _ _ _ _ E1) in *.
        trivial.
Qed.
