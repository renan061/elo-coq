From Elo Require Import Array.
From Elo Require Import Sem.
From Elo Require Import SemExt.
From Elo Require Import Upsilon.

Lemma value_init_term : forall t1 t2 ad t,
  t1 --[e_init ad t]--> t2 ->
  value t.
Proof.
  intros. ind_tstep; eauto.
Qed.

Lemma value_write_term : forall t1 t2 ad t,
  t1 --[e_write ad t]--> t2 ->
  value t.
Proof.
  intros. ind_tstep; eauto.
Qed.

Theorem value_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_memory m2 value.
Proof.
  intros. invc_cstep; trivial. invc_mstep; trivial;
  intros ? ? ?; upsilon; eauto using value_init_term, value_write_term.
Qed.

