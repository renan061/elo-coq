From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import ConsistentRegions.
From Elo Require Import Access.
From Elo Require Import AccessInheritance.
From Elo Require Import AccessExclusivity.

(* auxiliary ----------------------------------------------------------------*)

Local Lemma wtt_cr_acq_type : forall m t1 t2 ad' t',
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  t1 --[e_acq ad' t']--> t2 ->
  exists T, m[ad'].T = `x&T`.
Proof.
  intros * [T ?] **. gendep T. ind_tstep; intros;
  repeat invc_typeof; repeat invc_cr; eauto.
Qed.

(* preservation -------------------------------------------------------------*)

Local Lemma accexc_preservation_none : forall m ths tid t,
  acc_exclusivity m ths ->
  ths[tid] --[e_none]--> t ->
  acc_exclusivity m ths[tid <- t].
Proof.
  intros ** ? **.
  repeat omicron; try solve invc_acc; eauto using acc_inheritance_none.
Qed.

Local Lemma accexc_preservation_alloc : forall m ths tid t T,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  acc_exclusivity m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  acc_exclusivity (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros ** ? **. upsilon;
  repeat omicron; try solve invc_acc; eauto using acc_inheritance_alloc;
  exfalso; eauto using acc_vad_contradiction1.
Qed.

Local Lemma accexc_preservation_insert : forall m ths tid t ad' t' T',
  forall_threads ths (consistent_inits m) ->
  no_uninitialized_references m ths ->
  (* --- *)
  acc_exclusivity m ths ->
  ths[tid] --[e_insert ad' t' T']--> t ->
  acc_exclusivity m[ad'.t <- t'] ths[tid <- t].
Proof.
  intros ** ? **.
  assert (forall_program m ths (no_ref ad')) as [_ ?]
    by eauto using noref_from_insert.
  repeat omicron; upsilon; try invc_acc;
  eauto using acc_inheritance_insert;
  exfalso; eauto using acc_noref_contradiction.
Qed.

Local Lemma accexc_preservation_read : forall o m ths tid t t' ad',
  forall_threads_consistent_regions o ths ->
  forall_memory_consistent_regions  o m ->
  (* --- *)
  m[ad'].t = Some t' ->
  acc_exclusivity m ths ->
  ths[tid] --[e_read ad' t']--> t ->
  acc_exclusivity m ths[tid <- t].
Proof.
  intros * Hcreg Hmcreg ** ? **.
  repeat omicron; try invc_acc; eauto;
  destruct (acc_dec ad ths[tid2]); eauto.
  - specialize (Hcreg tid2).
    specialize (Hmcreg ad' t'); spec; specialize Hmcreg as [_ [_ Hmcreg]].
    specialize (Hmcreg T).

    admit.
  - admit.
Abort.

Local Lemma accexc_preservation_write : forall m ths tid t t' ad',
  acc_exclusivity m ths ->
  ths[tid] --[e_write ad' t']--> t ->
  acc_exclusivity m[ad'.t <- t'] ths[tid <- t].
Proof.
  intros ** ? **.
  repeat omicron; upsilon; try invc_acc; try discriminate;
  eauto using acc_inheritance_write.
Qed.

Local Lemma accexc_preservation_acq : forall m ths tid t t' ad',
  forall_threads ths well_typed_term ->
  forall_threads ths (consistent_references m) ->
  (* --- *)
  m[ad'].t = Some t' ->
  acc_exclusivity m ths ->
  ths[tid] --[e_acq ad' t']--> t ->
  acc_exclusivity m[ad'.X <- true] ths[tid <- t].
Proof.
  intros ** ? **.
  assert (exists T, m[ad'].T = `x&T`) as [T' ?] by eauto using wtt_cr_acq_type.
  repeat (omicron; try invc_acc); try invc_eq;
  eauto using acc_inheritance_acq.
Qed.

Local Lemma accexc_preservation_rel : forall m ths tid t ad',
  acc_exclusivity m ths ->
  ths[tid] --[e_rel ad']--> t ->
  acc_exclusivity m[ad'.X <- false] ths[tid <- t].
Proof.
  intros ** ? **.
  repeat (omicron; upsilon; try invc_acc); eauto.
  - destruct (acc_dec ad ths[tid2]); eauto. admit. (* t não pode ter accesso *)
  - admit.  (* t não pode ter accesso *)
Abort.

Local Lemma accexc_preservation_spawn : forall m ths tid t t',
  forall_threads ths (consistent_references m) ->
  forall_threads ths safe_spawns ->
  (* --- *)
  acc_exclusivity m ths ->
  ths[tid] --[e_spawn (#ths) t']--> t ->
  acc_exclusivity m (ths[tid <- t] +++ t').
Proof.
  intros ** ? **.
  assert (consistent_references m t') by eauto using cr_spawn_term.
  assert (no_wrefs t') by eauto using nowrefs_spawn_term.
  repeat (omicron; try invc_acc);
  eauto using acc_inheritance_spawn;
  exfalso; eauto using acc_nowrefs_contradiction.
Qed.

Theorem accexc_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistent_inits m1) ->
  forall_threads ths1 (consistent_references m1) ->
  forall_threads ths1 safe_spawns ->
  no_uninitialized_references m1 ths1 ->
  (* --- *)
  acc_exclusivity m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  acc_exclusivity m2 ths2.
Proof.
  intros. invc_cstep; try invc_mstep.
  - auto using accexc_preservation_none.
  - auto using accexc_preservation_alloc.
  - eauto using accexc_preservation_insert.
  - admit.
  - auto using accexc_preservation_write.
  - eauto using accexc_preservation_acq.
  - admit.
  - eauto using accexc_preservation_spawn.
Abort.

