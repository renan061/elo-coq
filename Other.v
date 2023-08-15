

(* ------------------------------------------------------------------------- *)
(* mstep -- reflexive transitive closure                                     *)
(* ------------------------------------------------------------------------- *)

(* TODO: remove *)

Reserved Notation "m / t '==[' tc ']==>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).

Definition mtrace := list effect.

Inductive mmultistep : mem -> tm -> mtrace -> mem -> tm -> Prop :=
  | mmultistep_refl: forall m t,
    m / t ==[nil]==>* m / t

  | mmultistep_trans : forall m m' m'' t t' t'' tc eff,
    m  / t  ==[tc]==>* m'  / t'  ->
    m' / t' ==[eff]==> m'' / t'' ->
    m  / t  ==[eff :: tc]==>* m'' / t''

  where "m / t '==[' tc ']==>*' m' / t'" := (mmultistep m t tc m' t').

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma monotonic_nondecreasing_memory_length' : forall m m' eff t t',
  m / t ==[eff]==>* m' / t' ->
  #m <= #m'.
Proof.
  assert (forall m m' eff t t',
    m / t ==[eff]==> m' / t' ->
    length m <= length m'). {
    intros * Hmstep. inversion Hmstep; subst; eauto.
    - rewrite add_increments_length. eauto.
    - rewrite set_preserves_length. eauto.
  }
  intros * Hmmultistep. induction Hmmultistep; eauto using Nat.le_trans.
Qed.

Lemma alloc_increments_memory_length : forall m m' t t' ad v Tr,
  m / t ==[EF_Alloc ad v Tr]==> m' / t' ->
  #m' = S (#m).
Proof.
  intros. inv_mstep. eauto using add_increments_length.
Qed.

Lemma destruct_multistep' : forall tc eff m0 mF t0 tF,
  m0 / t0  ==[tc ++ eff :: nil]==>* mF / tF ->
  (exists m t, m0 / t0 ==[eff]==> m / t /\ m / t ==[tc]==>* mF / tF).
Proof.
  intros ?. induction tc as [| eff tc IH];
  intros * Hmultistep; inversion Hmultistep; subst.
  - eexists. eexists. inversion H3; subst. split; eauto using mmultistep.
  - specialize (IH _ _ _ _ _ H3) as [? [? [? ?]]].
    eexists. eexists. split; eauto using mmultistep.
Qed.

Theorem duplicate_alloc : forall m m' t t' tc ad v v' Tr Tr',
  ~ (m / t ==[EF_Alloc ad v Tr :: tc ++ EF_Alloc ad v' Tr' :: nil]==>* m' / t').
Proof.
  assert (not_Sn_le_n : forall n, ~ (S n <= n)). {
    unfold not. intros * F. induction n;
    eauto using le_S_n. inversion F.
  }
  unfold not. intros * Hmultistep.
  inversion Hmultistep; subst; clear Hmultistep;
  destruct tc; try discriminate.
  - match goal with H : _ / _ ==[_]==>* _ / _ |- _ =>
      rewrite app_nil_l in H; inversion H; subst
    end.
    match goal with
    H1 : _ / _ ==[_]==> _ / _,
    H2 : _ / _ ==[_]==> _ / _ |- _ =>
      inversion H1; inversion H2; subst;
      eapply alloc_increments_memory_length in H1;
      eapply alloc_increments_memory_length in H2
    end.
    lia.
  - match goal with
    H : _ / _ ==[_]==>* _ / _ |- _ =>
      eapply destruct_multistep' in H as [? [? [? Hmultistep']]]
    end.
    eapply monotonic_nondecreasing_memory_length' in Hmultistep'.
    match goal with
    H1 : _ / _ ==[_]==> _ / _,
    H2 : _ / _ ==[_]==> _ / _ |- _ =>
      inversion H1; inversion H2; subst
    end.
    match goal with
    | H1 : length ?x = length _, H2 : length _ <= length ?x |- _ =>
      rewrite H1 in H2;
      rewrite add_increments_length in H2
    end.
    lia.
Qed.
