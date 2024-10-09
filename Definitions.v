From Coq Require Import Lia.
From Coq Require Import Lists.List.

(* ------------------------------------------------------------------------- *)
(* has-var                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive hasvar (x : id) : tm  -> Prop :=
  | hasvar_new : forall T t,
    hasvar x t ->
    hasvar x <{new t : T}>

  | hasvar_load : forall t,
    hasvar x t ->
    hasvar x <{*t}>

  | hasvar_asg1 : forall t1 t2,
    hasvar x t1 ->
    hasvar x <{t1 := t2}>

  | hasvar_asg2 : forall t1 t2,
    hasvar x t2 ->
    hasvar x <{t1 := t2}>

  | hasvar_var :
    hasvar x <{var x}>

  | hasvar_fun : forall x' Tx t,
    x <> x' ->
    hasvar x t ->
    hasvar x <{fn x' Tx t}>

  | hasvar_call1 : forall t1 t2,
    hasvar x t1 ->
    hasvar x <{call t1 t2}>

  | hasvar_call2 : forall t1 t2,
    hasvar x t2 ->
    hasvar x <{call t1 t2}>

  | hasvar_acq1 : forall t1 t2,
    hasvar x t1 ->
    hasvar x <{acq t1 t2}>

  | hasvar_acq2 : forall t1 t2,
    hasvar x t2 ->
    hasvar x <{acq t1 t2}>

  | hasvar_cr : forall ad t,
    hasvar x t ->
    hasvar x <{cr ad t}>

  | hasvar_ptm : forall tid t,
    hasvar x t ->
    hasvar x <{ptm tid t}>

  | hasvar_spawn : forall t,
    hasvar x t ->
    hasvar x <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* happens-before                                                            *)
(* ------------------------------------------------------------------------- *)

Notation " tc '[' ev '].tid' " := (fst (tc[ev] or tc_default))
  (at level 9, ev at next level).

Notation " tc '[' ev '].eff' " := (snd (tc[ev] or tc_default))
  (at level 9, ev at next level).

Reserved Notation "evA '<<' evB 'in' tc" (at level 50).

Inductive happens_before (tc : trace) : nat -> nat -> Prop :=
  | hb_thread : forall evA evB,
    evA < evB ->
    tc[evA].tid = tc[evB].tid ->
    evA << evB in tc

  | hb_sync : forall evA evB tidA tidB ad t,
    evA < evB ->
    tc[evA].eff = e_rel tidA ad ->
    tc[evB].eff = e_acq tidB ad t ->
    evA << evB in tc

  | hb_spawn : forall evA evB tid t,
    evA < evB ->
    tc[evA].eff = e_spawn tid t ->
    tc[evB].tid = tid ->
    evA << evB in tc

  | hb_trans : forall evA evB evC,
    evA << evB in tc ->
    evB << evC in tc ->
    evA << evC in tc

  where "evA '<<' evB 'in' tc" := (happens_before tc evA evB).

(* ------------------------------------------------------------------------- *)
(* safety                                                                    *)
(* ------------------------------------------------------------------------- *)

(*
(* ad guards ad' in m *)
Definition guards ad ad' m := exists T,
  m[ad].ty = `x&T` /\ write_access ad' m m[ad].tm.

Definition guard_exclusivity m := forall ad1 ad2 ad,
  ad1 <> ad2 ->
  guards ad1 ad m ->
  ~ guards ad2 ad m.

Definition safe_memory_sharing1 m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  write_access ad m ths[tid1] ->
  ~ write_access ad m ths[tid2].

Definition safe_memory_sharing2 m ths := forall tid1 tid2 ad T,
  tid1 <> tid2 ->
  access ad m ths[tid1] ->
  access ad m ths[tid2] ->
  m[ad].ty = `w&T` ->
  exists ad', guards ad' ad m.
*)
