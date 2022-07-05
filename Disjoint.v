From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core0.
From Elo Require Import Access.
From Elo Require Import Compat.
From Elo Require Import WBA.
From Elo Require Import AccessProp.
From Elo Require Import NoLoc.

Definition disjoint_memory m ths := forall tid1 tid2 ad,
  access m (getTM ths tid1) ad ->
  tid1 <> tid2 ->
  ~ access m (getTM ths tid2) ad.

Local Lemma none_disjoint_memory_preservation : forall m m' ths t' tid,
  disjoint_memory m ths ->
  tid < length ths ->
  m / (getTM ths tid) ==[EF_None]==> m' / t' ->
  disjoint_memory m' (set ths tid t').
Proof.
  intros * ? ? Hmstep tid1 tid2 ? ? ?. inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
  - rewrite (get_set_neq TM_Nil); rewrite (get_set_eq TM_Nil) in *;
    eauto using mstep_none_inherits_access.
  - rewrite (get_set_eq TM_Nil); rewrite (get_set_neq TM_Nil) in *;
    eauto using mstep_none_preserves_not_access.
  - rewrite (get_set_neq TM_Nil) in *; eauto.
Qed.

Local Lemma load_disjoint_memory_preservation : forall m m' ths t' tid ad v,
  disjoint_memory m ths ->
  tid < length ths ->
  m / (getTM ths tid) ==[EF_Load ad v]==> m' / t' ->
  disjoint_memory m' (set ths tid t').
Proof.
  intros * ? ? Hmstep tid1 tid2 ? ? ?. inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
  - rewrite (get_set_neq TM_Nil); rewrite (get_set_eq TM_Nil) in *;
    eauto using mstep_load_inherits_access.
  - rewrite (get_set_eq TM_Nil); rewrite (get_set_neq TM_Nil) in *;
    eauto using mstep_load_preserves_not_access.
  - rewrite (get_set_neq TM_Nil) in *; eauto.
Qed.

Local Lemma alloc_disjoint_memory_preservation : forall m m' ths t' tid ad v,
  (forall tid, well_behaved_access m (getTM ths tid)) ->
  disjoint_memory m ths ->
  tid < length ths ->
  m / (getTM ths tid) ==[EF_Alloc ad v]==> m' / t' ->
  disjoint_memory m' (set ths tid t').
Proof.
  intros * Hwba Hdis ? Hmstep tid1 tid2 ad' ? ?. inversion Hmstep; subst.
  assert (~ access m (get TM_Nil ths tid1) (length m)).
  { intros F. specialize (Hwba tid1 (length m) F). lia. }
  assert (~ access m (get TM_Nil ths tid2) (length m)).
  { intros F. specialize (Hwba tid2 (length m) F). lia. }
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
  - rewrite (get_set_neq TM_Nil); rewrite (get_set_eq TM_Nil) in *; eauto.
    destruct (Nat.eq_dec ad' (length m)); subst;
    eauto using inaccessible_address_add_2, mstep_alloc_inherits_access.
  - rewrite (get_set_eq TM_Nil); rewrite (get_set_neq TM_Nil) in *; eauto.
    destruct (Nat.eq_dec ad' (length m)); subst; eauto;
    eauto using inaccessible_address_add_1, mstep_alloc_preserves_not_access.
  - rewrite (get_set_neq TM_Nil) in *; eauto.
    eauto using inaccessible_address_add_1, inaccessible_address_add_2.
Qed.

Local Lemma store_disjoint_memory_preservation : forall m m' ths t' tid ad v,
  disjoint_memory m ths ->
  tid < length ths ->
  m / (getTM ths tid) ==[EF_Store ad v]==> m' / t' ->
  disjoint_memory m' (set ths tid t').
Proof.
  intros * ? ? Hmstep tid1 tid2 ? ? ?. inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
  - rewrite (get_set_neq TM_Nil); rewrite (get_set_eq TM_Nil) in *;
    eauto 6 using mstep_store_address_access,
                  mstep_store_inherits_access,
                  inaccessible_address_set_2.
  - rewrite (get_set_eq TM_Nil); rewrite (get_set_neq TM_Nil) in *;
    eauto 6 using mstep_store_address_access,
                  mstep_store_preserves_not_access,
                  inaccessible_address_set_1.
  - rewrite (get_set_neq TM_Nil) in *;
    eauto 8 using mstep_store_address_access,
                  inaccessible_address_set_1,
                  inaccessible_address_set_2.
Qed.

Local Lemma disjoint_memory_preservation' : forall m m' ths t' tid eff,
  (forall tid, well_behaved_access m (getTM ths tid)) ->
  disjoint_memory m ths ->
  tid < length ths ->
  m / (getTM ths tid) ==[eff]==> m' / t' ->
  disjoint_memory m' (set ths tid t').
Proof.
  intros * ? ? ? Hmstep. inversion Hmstep; subst;
  eauto using none_disjoint_memory_preservation,
              alloc_disjoint_memory_preservation,
              load_disjoint_memory_preservation,
              store_disjoint_memory_preservation.
Qed.

Theorem disjoint_memory_preservation : forall m m' ths ths' tid eff,
  (forall tid, SpawnNoLoc (getTM ths tid)) ->
  (forall tid, well_behaved_access m (getTM ths tid)) ->
  disjoint_memory m ths ->
  tid < length ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  disjoint_memory m' ths'.
Proof.
  intros. inversion_cstep;
  eauto using disjoint_memory_preservation'.
  intros tid1 tid2 ad Hacc Hneq.
  decompose sum (lt_eq_lt_dec (length ths) tid2); subst.
  - rewrite (get_add_gt TM_Nil);
    try solve [rewrite set_preserves_length; trivial].
    intros ?. inversion_access.
  - erewrite <- set_preserves_length.
    rewrite (get_add_eq TM_Nil).
    eauto using noloc_then_not_access, noloc_for_block.
  - rewrite (get_add_lt TM_Nil);
    try solve [rewrite set_preserves_length; trivial].
    decompose sum (lt_eq_lt_dec (length ths) tid1); subst.
    + rewrite (get_add_gt TM_Nil) in Hacc;
      try solve [rewrite set_preserves_length; trivial].
      inversion_access.
    + erewrite <- set_preserves_length in Hacc.
      rewrite (get_add_eq TM_Nil) in Hacc.
      assert (~ access m' block ad) by 
        eauto using noloc_then_not_access, noloc_for_block.
      eauto.
    + rewrite (get_add_lt TM_Nil) in Hacc;
      try solve [rewrite set_preserves_length; trivial].
      destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
      * rewrite (get_set_neq TM_Nil); try lia.
        rewrite (get_set_eq TM_Nil) in *; trivial.
        eauto using step_spawn_inherits_access.
      * rewrite (get_set_eq TM_Nil); trivial.
        rewrite (get_set_neq TM_Nil) in *; trivial.
        eauto using step_spawn_preserves_not_access.
      * rewrite (get_set_neq TM_Nil); try lia.
        rewrite (get_set_neq TM_Nil) in *; try lia.
        eauto.
Qed.

