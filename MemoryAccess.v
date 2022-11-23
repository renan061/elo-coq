From Coq Require Import Arith.
From Coq Require Import Program.Equality.

From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.

Inductive MemoryAccess (m : mem) : addr -> addr -> Prop :=
  | macc_refI : forall ad ad' T,
    m[ad] = <{ &ad' :: i&T }> ->
    MemoryAccess m ad ad'

  | macc_refM : forall ad ad' T,
    m[ad] = <{ &ad' :: &T }> ->
    MemoryAccess m ad ad'

  | macc_transI : forall ad ad' ad'' T,
    m[ad] = <{ &ad' :: i&T }> ->
    MemoryAccess m ad' ad'' ->
    MemoryAccess m ad ad''

  | macc_transM : forall ad ad' ad'' T,
    m[ad] = <{ &ad' :: &T }> ->
    MemoryAccess m ad' ad'' ->
    MemoryAccess m ad ad''
  .

Definition noloop_memory m := forall ad1 ad2,
  MemoryAccess m ad1 ad2 -> ad1 <> ad2.

Local Lemma aux1 : forall m ad ad',
  MemoryAccess m ad ad' ->
  (exists ad'' T, m[ad] = <{ &ad'' :: i&T}>) \/
  (exists ad'' T, m[ad] = <{ &ad'' ::  &T}>).
Proof.
  intros * Hmacc. inversion Hmacc; subst; solve [left; eauto | right; eauto].
Qed.

Local Lemma mem_add_macc : forall m v,
  forall_memory m (valid_accesses m) ->
  valid_accesses m v ->
  noloop_memory m ->
  noloop_memory (m +++ v).
Proof.
  intros * Hva1 Hva2 Hnoloop ad1 ad2 Hmacc.
  induction Hmacc.
  - assert (ad < length m \/ ad = length m) as [? | ?] by admit;
    subst; simpl_array; eauto using MemoryAccess.
    subst. intros ?. subst. eapply Nat.lt_irrefl. eauto using access.
  - assert (ad < length m \/ ad = length m) as [? | ?] by admit;
    subst; simpl_array; eauto using MemoryAccess.
    subst. intros ?. subst. eapply Nat.lt_irrefl. eauto using access.
  - assert (ad < length m \/ ad = length m) as [? | ?] by admit.
    + simpl_array.
      induction Hmacc.
      * rename ad0 into ad''.
        assert (ad'' < length m \/ ad'' = length m) as [? | ?] by admit.
        ** simpl_array. eauto using MemoryAccess.
        ** exfalso. subst.
           specialize (Hva1 ad (length m)).
           rewrite H in Hva1.
           eapply Nat.lt_irrefl. eauto using access.
      * rename ad0 into ad''.
        assert (ad'' < length m \/ ad'' = length m) as [? | ?] by admit.
        ** simpl_array. eauto using MemoryAccess.
        ** exfalso. subst.
           specialize (Hva1 ad (length m)).
           rewrite H in Hva1.
           eapply Nat.lt_irrefl. eauto using access.
      *



      assert (exists T, (m +++ v)[ad'] = <{ &ad'' :: i&T}>) as [T' ?] by admit.
      assert (ad' < length m \/ ad' = length m) as [? | ?] by admit.
      * simpl_array. eauto using MemoryAccess.
      * exfalso. subst.
        specialize (Hva1 ad (length m)).
        rewrite H in Hva1.
        eapply Nat.lt_irrefl. eauto using access.
    + subst. simpl_array.
      subst. intros ?. subst. eapply Nat.lt_irrefl. eauto using access.

Qed.

Local Lemma step_alloc_dag_memory_preservation : forall m t t' ad v,
  dag_memory m ->
  t --[EF_Alloc ad v]--> t' ->
  dag_memory (m +++ v).
Proof.
  intros * Hdag ?. induction_step; eauto. intros ad'.
  specialize (Hdag ad').
  
  clear Heqeff.
  
  intros F.

  induction F; eauto.
  - rename ad0 into ad''.
    decompose sum (lt_eq_lt_dec ad'' (length m)); subst.
    + simpl_array.
      assert (MemoryAccess m ad'' ad') by eauto using MemoryAccess.
Qed.

Theorem mstep_dag_memory_preservation : forall m m' t t' eff,
  dag_memory m ->
  m / t ==[eff]==> m' / t' ->
  dag_memory m'.
Proof.
  intros. inversion_mstep; trivial.
  - admit.
  - admit.
Qed.
