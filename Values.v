From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Sem.
From Elo Require Import SemExt.
From Elo Require Import Upsilon.

Lemma value_insert_term : forall t1 t2 ad t,
  t1 --[e_insert ad t]--> t2 ->
  value t.
Proof.
  intros. ind_tstep; auto.
Qed.

Lemma value_write_term : forall t1 t2 ad t,
  t1 --[e_write ad t]--> t2 ->
  value t.
Proof.
  intros. ind_tstep; auto.
Qed.

Lemma value_subst : forall x tx t,
  value t ->
  value <{[x := tx] t}>.
Proof.
  intros * H. invc H; simpl; try destruct _str_eq_dec; auto using value.
Qed.

Theorem value_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  forall_memory m2 value.
Proof.
  intros. invc_cstep; trivial. invc_mstep; trivial;
  intros ? ? ?; upsilon; eauto using value_insert_term, value_write_term.
Qed.

Theorem value_preservation_rstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  m1 \ ths1 ~~~[tid, e]~~> m2 \ ths2 ->
  forall_memory m2 value.
Proof.
  intros. invc_rstep; eauto using value_preservation_cstep.
  match goal with _ : _ \ _ ~~[_, _]~~> ?m \ ?ths |- _ =>
    assert (forall_memory m value) by eauto using value_preservation_cstep
  end.
  repeat intro; repeat omicron; upsilon; auto; eauto.
Qed.

Theorem value_preservation_ustep : forall m1 m2 ths1 ths2 tc,
  forall_memory m1 value ->
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  forall_memory m2 value.
Proof.
  intros. ind_ustep; eauto using value_preservation_rstep.
Qed.

