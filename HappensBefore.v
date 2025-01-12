From Coq Require Import Lists.List.

From Elo Require Import Core.

Inductive happens_before : trace -> Prop :=
  | hb_tid : forall tc tid e1 e2,
    happens_before ((tid, e2) :: tc +++ (tid, e1))

  | hb_rel_acq : forall tc tid1 tid2 ad t,
    happens_before ((tid2, e_acq ad t) :: tc +++ (tid1, e_rel ad))

  | hb_insert_acq : forall tc tid1 tid2 ad t1 t2,
    happens_before ((tid2, e_acq ad t2) :: tc +++ (tid1, e_insert ad t1))

  | hb_trans : forall tcA tcB ev1 ev2 ev3,
    happens_before (ev2 :: tcA +++ ev1) ->
    happens_before (ev3 :: tcB +++ ev2) ->
    happens_before (ev3 :: tcB ++ ev2 :: tcA +++ ev1)
  .

