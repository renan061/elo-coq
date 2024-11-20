From Elo Require Import Core.
From Elo Require Import Properties1.

From Elo Require Import NoUninitRefs.
From Elo Require Import UniqueInits.
From Elo Require Import UniqueCRs.
From Elo Require Import ConsistentInits.

(* ------------------------------------------------------------------------- *)
(* init-cr-exclusivity                                                       *)
(* ------------------------------------------------------------------------- *)

Definition init_cr_exclusivity (ths : threads) := forall ad tid1 tid2,
  (one_init ad ths[tid1] -> no_cr   ad ths[tid2]) /\
  (one_cr   ad ths[tid1] -> no_init ad ths[tid2]).

(* preservation ------------------------------------------------------------ *)

Lemma ice_preservation_none : forall ths tid t,
  forall_threads ths valid_blocks ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_none]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros * ? Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto;
  eauto using nocr_preservation_none, oneinit_inheritance_none;
  eauto using noinit_preservation_none, onecr_inheritance_none.
Qed.

Lemma ice_preservation_alloc : forall m ths tid t T,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 2.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  assert (forall tid, no_cr (#m) ths[tid]) by eauto using nocr_from_vad.
  split; intros; repeat omicron; auto; destruct (nat_eq_dec ad (#m)); subst;
  eauto using nocr_preservation_alloc, oneinit_inheritance_alloc;
  eauto using noinit_preservation_alloc, onecr_inheritance_alloc;
  exfalso; eauto using onecr_inheritance_alloc, nocr_onecr_contradiction.
Qed.

Theorem oneinit_from_insert : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (consistent_inits m) ->
  unique_initializers m ths ->
  (* --- *)
  ths[tid] --[e_insert ad te]--> t ->
  one_init ad ths[tid].
Proof.
  intros * ? ? Hui **.
  assert (Had   : ad < #m) by eauto using vad_insert_addr.
  assert (Hnone : m[ad].t = None) by eauto using insert_then_uninitialized.
  specialize (Hui ad Had) as [_ Hui]. specialize (Hui Hnone) as [tid' [? ?]].
  destruct (nat_eq_dec tid' tid); subst; trivial.
  exfalso. eauto using noinit_insert_contradiction.
Qed.

Theorem onecr_from_rel : forall m ths tid t ad,
  unique_critical_regions m ths ->
  (* --- *)
  ths[tid] --[e_rel ad]--> t ->
  one_cr ad ths[tid].
Proof.
  intros * Hucr **. specialize (Hucr ad) as [Hfalse Htrue].
  destruct (m[ad].X) eqn:?.
  - specialize (Htrue eq_refl) as [tid' [? ?]]; clear Hfalse.
    destruct (nat_eq_dec tid' tid); subst; trivial.
    exfalso. eauto using nocr_rel_contradiction.
  - specialize (Hfalse eq_refl); clear Htrue.
    exfalso. eauto using nocr_rel_contradiction.
Qed.

Lemma ice_preservation_insert : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  forall_threads ths (consistent_inits m) ->
  unique_initializers m ths ->
  unique_critical_regions m ths ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_insert ad te]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 5. rename ad into ad'.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; destruct (nat_eq_dec ad' ad); subst;
  eauto using nocr_preservation_insert, oneinit_inheritance_insert;
  eauto using noinit_preservation_insert, onecr_inheritance_insert;
  exfalso.
  - assert (one_init ad ths[tid2]) by eauto using oneinit_from_insert.
    assert (no_init ad t) by eauto using oneinit_to_noinit.
    eauto using noinit_oneinit_contradiction.
  - assert (one_init ad ths[tid1]) by eauto using oneinit_from_insert.
    assert (no_init ad t) by eauto using oneinit_to_noinit.
    eauto using noinit_oneinit_contradiction.
  - assert (one_cr ad ths[tid2]) by eauto using onecr_inheritance_insert.
    aspecialize. eauto using noinit_insert_contradiction.
  - aspecialize. eauto using noinit_insert_contradiction.
Qed.

Lemma ice_preservation_read : forall m ths tid t ad te,
  forall_memory m no_inits ->
  forall_memory m no_crs ->
  forall_threads ths valid_blocks ->
  (* --- *)
  m[ad].t = Some te ->
  init_cr_exclusivity ths ->
  ths[tid] --[e_read ad te]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros * Hnoinits Hnocrs ?. rename ad into ad'.
  intros Had' Hice ? ad tid1 tid2.
  specialize (Hnoinits ad' _ Had').
  specialize (Hnocrs ad' _ Had').
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto;
  eauto using nocr_preservation_read, oneinit_inheritance_read;
  eauto using noinit_preservation_read, onecr_inheritance_read.
Qed.

Lemma ice_preservation_write : forall ths tid t ad te,
  forall_threads ths valid_blocks ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_write ad te]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 1. rename ad into ad'.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; destruct (nat_eq_dec ad' ad); subst;
  eauto using nocr_preservation_write, oneinit_inheritance_write;
  eauto using noinit_preservation_write, onecr_inheritance_write.
Qed.

Lemma oneinit_then_uninitialized : forall ad m t,
  consistent_inits m t ->
  one_init ad t ->
  m[ad].t = None.
Proof.
  intros. induction t; invc_ci; invc_oneinit; auto.
Qed.

Lemma noref_from_oneinit : forall ad m ths tid,
  forall_threads ths (consistent_inits m) ->
  no_uninitialized_references m ths ->
  (* --- *)
  one_init ad ths[tid] ->
  forall_threads ths (no_ref ad).
Proof.
  intros * ? Hnur ?.
  assert (Hnone : m[ad].t = None) by eauto using oneinit_then_uninitialized.
  specialize (Hnur ad Hnone) as [_ ?]. assumption.
Qed.

Lemma ice_preservation_acq : forall m ths tid t ad te,
  forall_memory m no_inits ->
  forall_memory m no_crs ->
  forall_threads ths valid_blocks ->
  forall_threads ths (consistent_inits m) ->
  no_uninitialized_references m ths ->
  unique_initializers m ths ->
  (* --- *)
  m[ad].t = Some te ->
  init_cr_exclusivity ths ->
  ths[tid] --[e_acq ad te]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros * Hnoinits Hnocrs ? ? Hnur Hui. rename ad into ad'.
  intros Hsome Hice ? ad tid1 tid2.
  assert (m[ad'].t <> None) by auto.
  assert (Had : ad' < #m) by (lt_eq_gt ad' (#m); sigma; upsilon; eauto).
  specialize (Hnoinits ad' _ Hsome).
  specialize (Hnocrs ad' _ Hsome).
  specialize (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; destruct (nat_eq_dec ad' ad); subst;
  eauto using nocr_preservation_acq, oneinit_inheritance_acq;
  eauto using noinit_preservation_acq, onecr_inheritance_acq.
  - exfalso. eapply noref_acq_contradiction; eauto.
    assert (one_init ad ths[tid2]) by eauto using oneinit_inheritance_acq.
    eapply noref_from_oneinit; eauto.
  - exfalso. eapply noref_acq_contradiction; eauto.
    eapply noref_from_oneinit; eauto.
  - specialize (Hui ad Had) as [Hnone _]. aspecialize.
    eauto using noinit_preservation_acq.
  - specialize (Hui ad Had) as [Hnone _]. aspecialize.
    eauto.
Qed.

Lemma ice_preservation_rel : forall m ths tid t ad,
  unique_critical_regions m ths ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_rel ad]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 1. rename ad into ad'.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto;  destruct (nat_eq_dec ad' ad); subst;
  eauto using nocr_preservation_rel, oneinit_inheritance_rel;
  eauto using noinit_preservation_rel, onecr_inheritance_rel;
  eauto using onecr_from_rel;
  exfalso.
  - eauto using onecr_from_rel, noinit_preservation_rel,
      noinit_oneinit_contradiction.
  - eauto using onecr_from_rel, nocr_onecr_contradiction.
  - eauto using onecr_from_rel, onecr_to_nocr, nocr_onecr_contradiction.
Qed.

Lemma ice_preservation_spawn : forall ths tid t te,
  forall_threads ths valid_blocks ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  init_cr_exclusivity (ths[tid <- t] +++ te).
Proof.
  intros until 1.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  assert (no_init ad te) by eauto using noinit_spawn_term.
  assert (no_cr ad te) by eauto using nocr_spawn_term.
  split; intros; repeat omicron; auto; eauto using no_cr;
  eauto using nocr_preservation_spawn, oneinit_inheritance_spawn;
  eauto using noinit_preservation_spawn, onecr_inheritance_spawn;
  exfalso; eauto using noinit_oneinit_contradiction, nocr_onecr_contradiction.
Qed.

Theorem ice_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_inits ->
  forall_memory m1 no_crs ->
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 valid_blocks ->
  forall_threads ths1 (consistent_inits m1) ->
  no_uninitialized_references m1 ths1 ->
  unique_initializers m1 ths1 ->
  unique_critical_regions m1 ths1 ->
  (* --- *)
  init_cr_exclusivity ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  init_cr_exclusivity ths2.
Proof.
  intros. invc_cstep; try invc_mstep.
  - eauto using ice_preservation_none.
  - eauto using ice_preservation_alloc.
  - eauto using ice_preservation_insert.
  - eauto using ice_preservation_read.
  - eauto using ice_preservation_write.
  - eauto using ice_preservation_acq.
  - eauto using ice_preservation_rel.
  - eauto using ice_preservation_spawn.
Qed.

