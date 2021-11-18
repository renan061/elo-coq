From Coq Require Import Strings.String.

Inductive map (A : Type) : Type :=
  | map_nil
  | map_cons (k : string) (v : A) (m : map A)
  .

Definition empty {A} := map_nil A.

Fixpoint update {A} (m : map A) k v :=
  match m with
  | map_nil _ => map_cons A k v (map_nil A)
  | map_cons _ k' v' m' =>
      if eqb k k'
        then map_cons A k  v  (update m' k v)
        else map_cons A k' v' (update m' k v)
  end.

Fixpoint lookup {A} m k : option A :=
  match m with
  | map_nil _ => None
  | map_cons _ k' v m' => if eqb k' k then Some v else lookup m' k
  end.

(* m includes m' *)
Local Definition includes' {A} (m m' : map A) :=
  forall k v, lookup m' k = Some v -> lookup m k = Some v.

Infix "includes" := includes' (at level 50, left associativity).

Local Definition update' {A} m k v := map_cons A k v m.

Local Theorem update_equivalence : forall {A} (m : map A) k v id,
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

Local Lemma lookup_update_k_eq' : forall {A} (m : map A) k v,
  lookup (update' m k v) k = Some v.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Local Lemma lookup_update_k_neq' : forall {A} (m : map A) k k' v,
  k' <> k ->
  lookup (update' m k' v) k = lookup m k.
Proof.
  intros * H. simpl. destruct eqb eqn:E; trivial.
  apply String.eqb_eq in E. contradiction.
Qed.

Local Lemma update_preserves_inclusion' : forall {A} (m m' : map A) k v,
  m includes m' ->
  (update' m k v) includes (update' m' k v).
Proof.
  intros *. unfold includes', lookup, update'.
  destruct m; intros * ? k'; destruct (eqb k k'); eauto.
Qed.

Local Lemma update_overwrite' : forall {A} (m : map A) k v v',
  (update' m k v) includes (update' (update' m k v') k v).
Proof.
  unfold includes', lookup, update'. intros ? ? ? ? ? k' ?.
  destruct m; intros H; destruct (eqb k k'); assumption.
Qed.

Local Lemma update_permutation' : forall {A} (m : map A) k1 k2 v1 v2,
  k1 <> k2 ->
  (update' (update' m k1 v1) k2 v2) includes (update' (update' m k2 v2) k1 v1).
Proof.
  intros * Hneq. unfold includes'.
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
      * apply eqb_eq in E2. subst. rewrite 2 lookup_update_k_eq' in *. trivial.
      * apply eqb_neq in E2.
        rewrite (lookup_update_k_neq' _ _ _ _ E2).
        rewrite 2 lookup_update_k_eq' in *.
        intros H. specialize (IH H).
        assumption.
    + apply eqb_neq in E1.
      rewrite (lookup_update_k_neq' _ _ _ _ E1) in *.
      destruct (eqb k2 k') eqn:E2.
      * apply eqb_eq in E2. subst. rewrite 2 lookup_update_k_eq'. trivial.
      * apply eqb_neq in E2.
        rewrite 2 (lookup_update_k_neq' _ _ _ _ E2) in *.
        rewrite (lookup_update_k_neq' _ _ _ _ E1) in *.
        trivial.
Qed.

Corollary lookup_update_k_eq : forall {A} (m : map A) k v,
  lookup (update m k v) k = Some v.
Proof.
  intros. rewrite update_equivalence. auto using lookup_update_k_eq'.
Qed.

Corollary lookup_update_k_neq : forall {A} (m : map A) k k' v,
  k' <> k ->
  lookup (update m k' v) k = lookup m k.
Proof.
  intros * H. rewrite update_equivalence. auto using lookup_update_k_neq'.
Qed.

Corollary update_preserves_inclusion : forall {A} (m m' : map A) k v,
  m includes m' ->
  (update m k v) includes (update m' k v).
Proof.
  intros. unfold includes'. intros *.
  rewrite 2 update_equivalence. apply update_preserves_inclusion'. assumption.
Qed.

Lemma update_overwrite : forall {A} (m : map A) k v v',
  (update m k v) includes (update (update m k v') k v).
Proof.
  unfold includes'. intros ? ? ? ? ? k' ?.
  rewrite 2 update_equivalence.
  unfold lookup, update'.
  destruct m; intros H; destruct (eqb k k') eqn:E; trivial;
  fold (@lookup A) in H; rewrite update_equivalence in H;
  unfold lookup, update' in H; rewrite E in H; assumption.
Qed.

Lemma update_permutation : forall {A} (m : map A) k1 k2 v1 v2,
  k1 <> k2 ->
  (update (update m k1 v1) k2 v2) includes (update (update m k2 v2) k1 v1).
Proof.
  intros * Hneq. unfold includes'.
  intros k v. rewrite 2 update_equivalence.
  generalize dependent v. generalize dependent k.
  induction m as [| ? ? ? IH]; intros k' v'.
  - unfold update', lookup.
    destruct (eqb k1 k') eqn:E1; destruct (eqb k2 k') eqn:E2.
    + apply eqb_eq in E1, E2. subst. contradiction.
    + apply eqb_eq in E1. subst.
      fold (@lookup A). rewrite update_equivalence.
      unfold update', lookup. rewrite eqb_refl. trivial.
    + apply eqb_eq in E2. subst.
      fold (@lookup A). rewrite update_equivalence.
      unfold update', lookup. rewrite eqb_refl. trivial.
    + fold (@lookup A). rewrite 2 update_equivalence.
      unfold update', lookup. rewrite E1, E2. trivial.
  - specialize (IH k' v').
    destruct (eqb k1 k') eqn:E1.
    + apply eqb_eq in E1. subst.
      destruct (eqb k2 k') eqn:E2.
      * apply eqb_eq in E2. subst. rewrite 2 lookup_update_k_eq' in *. trivial.
      * apply eqb_neq in E2.
        rewrite (lookup_update_k_neq' _ _ _ _ E2).
        rewrite update_equivalence.
        rewrite 2 lookup_update_k_eq' in *.
        trivial.
    + apply eqb_neq in E1.
      rewrite (lookup_update_k_neq' _ _ _ _ E1) in *.
      destruct (eqb k2 k') eqn:E2.
      * apply eqb_eq in E2. subst.
        rewrite update_equivalence.
        rewrite 2 lookup_update_k_eq'.
        trivial.
      * apply eqb_neq in E2.
        rewrite update_equivalence.
        rewrite 2 (lookup_update_k_neq' _ _ _ _ E2) in *.
        rewrite (lookup_update_k_neq _ _ _ _ E1) in *.
        trivial.
Qed.
