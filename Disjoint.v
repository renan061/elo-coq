From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import Compat.
From Elo Require Import AccessProp.
From Elo Require Import NoLoc.

Definition disjoint_memory m ths := forall tid1 tid2 ad,
  access m ths[tid1] ad ->
  tid1 <> tid2 ->
  ~ access m ths[tid2] ad.

Local Lemma none_disjoint_memory_preservation : forall m m' ths t' tid,
  disjoint_memory m ths ->
  tid < length ths ->
  m / ths[tid] ==[EF_None]==> m' / t' ->
  disjoint_memory m' ths[tid <- t'].
Proof.
  intros * ? ? Hmstep tid1 tid2 ? ? ?. inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
  - rewrite (get_set_neq TM_Unit); rewrite (get_set_eq TM_Unit) in *;
    eauto using mstep_none_inherits_access.
  - rewrite (get_set_eq TM_Unit); rewrite (get_set_neq TM_Unit) in *;
    eauto using mstep_none_preserves_not_access.
  - rewrite (get_set_neq TM_Unit) in *; eauto.
Qed.

Local Lemma load_disjoint_memory_preservation : forall m m' ths t' tid ad v,
  disjoint_memory m ths ->
  tid < length ths ->
  m / ths[tid] ==[EF_Read ad v]==> m' / t' ->
  disjoint_memory m' ths[tid <- t'].
Proof.
  intros * ? ? Hmstep tid1 tid2 ? ? ?. inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
  - rewrite (get_set_neq TM_Unit); rewrite (get_set_eq TM_Unit) in *;
    eauto using mstep_load_inherits_access.
  - rewrite (get_set_eq TM_Unit); rewrite (get_set_neq TM_Unit) in *;
    eauto using mstep_load_preserves_not_access.
  - rewrite (get_set_neq TM_Unit) in *; eauto.
Qed.

Local Lemma alloc_disjoint_memory_preservation : forall m m' ths t' tid ad v,
  (forall tid, valid_accesses m ths[tid]) ->
  disjoint_memory m ths ->
  tid < length ths ->
  m / ths[tid] ==[EF_Alloc ad v]==> m' / t' ->
  disjoint_memory m' ths[tid <- t'].
Proof.
  intros * Hwba Hdis ? Hmstep tid1 tid2 ad' ? ?. inversion Hmstep; subst.
  assert (~ access m (get TM_Unit ths tid1) (length m)).
  { intros F. specialize (Hwba tid1 (length m) F). lia. }
  assert (~ access m (get TM_Unit ths tid2) (length m)).
  { intros F. specialize (Hwba tid2 (length m) F). lia. }
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
  - rewrite (get_set_neq TM_Unit); rewrite (get_set_eq TM_Unit) in *; eauto.
    destruct (Nat.eq_dec ad' (length m)); subst;
    eauto using inaccessible_address_add_2, mstep_alloc_inherits_access.
  - rewrite (get_set_eq TM_Unit); rewrite (get_set_neq TM_Unit) in *; eauto.
    destruct (Nat.eq_dec ad' (length m)); subst; eauto;
    eauto using inaccessible_address_add_1, mstep_alloc_preserves_not_access.
  - rewrite (get_set_neq TM_Unit) in *; eauto.
    eauto using inaccessible_address_add_1, inaccessible_address_add_2.
Qed.

Local Lemma store_disjoint_memory_preservation : forall m m' ths t' tid ad v,
  disjoint_memory m ths ->
  tid < length ths ->
  m / ths[tid] ==[EF_Write ad v]==> m' / t' ->
  disjoint_memory m' ths[tid <- t'].
Proof.
  intros * ? ? Hmstep tid1 tid2 ? ? ?. inversion Hmstep; subst.
  destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto.
  - rewrite (get_set_neq TM_Unit); rewrite (get_set_eq TM_Unit) in *;
    eauto 6 using mstep_store_address_access,
                  mstep_store_inherits_access,
                  inaccessible_address_set_2.
  - rewrite (get_set_eq TM_Unit); rewrite (get_set_neq TM_Unit) in *;
    eauto 6 using mstep_store_address_access,
                  mstep_store_preserves_not_access,
                  inaccessible_address_set_1.
  - rewrite (get_set_neq TM_Unit) in *;
    eauto 8 using mstep_store_address_access,
                  inaccessible_address_set_1,
                  inaccessible_address_set_2.
Qed.

Local Lemma disjoint_memory_preservation' : forall m m' ths t' tid eff,
  (forall tid, valid_accesses m ths[tid]) ->
  disjoint_memory m ths ->
  tid < length ths ->
  m / ths[tid] ==[eff]==> m' / t' ->
  disjoint_memory m' ths[tid <- t'].
Proof.
  intros * ? ? ? Hmstep. inversion Hmstep; subst;
  eauto using none_disjoint_memory_preservation,
              alloc_disjoint_memory_preservation,
              load_disjoint_memory_preservation,
              store_disjoint_memory_preservation.
Qed.

Theorem disjoint_memory_preservation : forall m m' ths ths' tid eff,
  threads_property SpawnNoLoc ths ->
  threads_property (valid_accesses m) ths ->
  disjoint_memory m ths ->
  tid < length ths ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  disjoint_memory m' ths'.
Proof.
  intros. inversion_cstep;
  eauto using disjoint_memory_preservation'.
  intros tid1 tid2 ad Hacc Hneq.
  decompose sum (lt_eq_lt_dec (length ths) tid2); subst.
  - rewrite (get_add_gt TM_Unit);
    try solve [rewrite set_preserves_length; trivial].
    intros ?. inversion_access.
  - erewrite <- set_preserves_length.
    rewrite (get_add_eq TM_Unit).
    eauto using noloc_for_block, noloc_then_not_access.
  - rewrite (get_add_lt TM_Unit);
    try solve [rewrite set_preserves_length; trivial].
    decompose sum (lt_eq_lt_dec (length ths) tid1); subst.
    + rewrite (get_add_gt TM_Unit) in Hacc;
      try solve [rewrite set_preserves_length; trivial].
      inversion_access.
    + erewrite <- set_preserves_length in Hacc.
      rewrite (get_add_eq TM_Unit) in Hacc.
      assert (~ access m' block ad) by 
        eauto using noloc_for_block, noloc_then_not_access.
      eauto.
    + rewrite (get_add_lt TM_Unit) in Hacc;
      try solve [rewrite set_preserves_length; trivial].
      destruct (Nat.eq_dec tid tid1), (Nat.eq_dec tid tid2); subst; eauto;
      do 2 (rewrite_array TM_Unit);
      eauto using step_spawn_inherits_access, step_spawn_preserves_not_access.
Qed.

