From Elo Require Import Sem.
From Elo Require Import SemExt.

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
