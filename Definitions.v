From Coq Require Import Lia.
From Coq Require Import Lists.List.

From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* access                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Ignores <spawn> blocks. *)
Inductive access (ad : addr) (m : mem) : tm -> Prop :=
  | acc_fun : forall x Tx t,
    access ad m t ->
    access ad m <{fn x Tx t}>

  | acc_call1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{call t1 t2}>

  | acc_call2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{call t1 t2}>

  | acc_mem : forall ad' T,
    ad <> ad' ->
    access ad m m[ad'].tm ->
    access ad m <{&ad' : T}>

  | acc_ref : forall T,
    access ad m <{&ad : T}>

  | acc_new : forall T t,
    access ad m t ->
    access ad m <{new t : T}>

  | acc_load : forall t,
    access ad m t ->
    access ad m <{*t}>

  | acc_asg1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{t1 := t2}>

  | acc_asg2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{t1 := t2}>

  | acc_acq1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{acq t1 t2}>

  | acc_acq2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{acq t1 t2}>

  | acc_cr : forall ad' t,
    access ad m t ->
    access ad m <{cr ad' t}>

  | acc_ptm : forall tid t,
    access ad m t ->
    access ad m <{ptm tid t}>
  .

(* ------------------------------------------------------------------------- *)
(* write-access                                                              *)
(* ------------------------------------------------------------------------- *)

(*
  The term can write to the address without need for synchronization.
  (It may not need synchronization because it already synchronized.)
*)
Inductive write_access (ad : addr) (m : mem) : tm  -> Prop :=
  | wacc_fun : forall x Tx t,
    write_access ad m t ->
    write_access ad m <{fn x Tx t}>

  | wacc_call1 : forall t1 t2,
    write_access ad m t1 ->
    write_access ad m <{call t1 t2}>

  | wacc_call2 : forall t1 t2,
    write_access ad m t2 ->
    write_access ad m <{call t1 t2}>

  | wacc_mem : forall ad' T,
    ad <> ad' ->
    write_access ad m (m[ad'].tm) ->
    write_access ad m <{&ad' : w&T}>

  | wacc_ref : forall T,
    write_access ad m <{&ad : w&T}>

  | wacc_new : forall T t,
    write_access ad m t ->
    write_access ad m <{new t : T}>

  | wacc_load : forall t,
    write_access ad m t ->
    write_access ad m <{*t}>

  | wacc_asg1 : forall t1 t2,
    write_access ad m t1 ->
    write_access ad m <{t1 := t2}>

  | wacc_asg2 : forall t1 t2,
    write_access ad m t2 ->
    write_access ad m <{t1 := t2}>

  | wacc_acq1 : forall t1 t2,
    write_access ad m t1 ->
    write_access ad m <{acq t1 t2}>

  | wacc_acq2 : forall t1 t2,
    write_access ad m t2 ->
    write_access ad m <{acq t1 t2}>

  | wacc_cr : forall ad' t,
    write_access ad m t ->
    write_access ad m <{cr ad' t}>

  | wacc_ptm : forall tid t,
    write_access ad m t ->
    write_access ad m <{ptm tid t}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-access                                                               *)
(* ------------------------------------------------------------------------- *)

Definition safe_access ad m t := access ad m t /\ ~ write_access ad m t.

(* ------------------------------------------------------------------------- *)
(* safe-term                                                                 *)
(* ------------------------------------------------------------------------- *)

(* A safe term has no "write" references. *)
Inductive safe_term : tm -> Prop :=
  | safe_term_unit :
    safe_term <{unit}>

  | safe_term_nat : forall n,
    safe_term <{nat n}>

  | safe_term_var : forall x,
    safe_term <{var x}>

  | safe_term_fun : forall x Tx t,
    safe_term t ->
    safe_term <{fn x Tx t}>

  | safe_term_call : forall t1 t2,
    safe_term t1 ->
    safe_term t2 ->
    safe_term <{call t1 t2}>

  | safe_term_refR : forall ad T,
    safe_term <{&ad : r&T}>

  | safe_term_refX : forall ad T,
    safe_term <{&ad : x&T}>

  | safe_term_new : forall T t,
    safe_term t ->
    safe_term <{new t : T}>

  | safe_term_load : forall t,
    safe_term t ->
    safe_term <{*t}>

  | safe_term_asg : forall t1 t2,
    safe_term t1 ->
    safe_term t2 ->
    safe_term <{t1 := t2}>

  | safe_term_acq : forall t1 t2,
    safe_term t1 ->
    safe_term t2 ->
    safe_term <{acq t1 t2}>

  | safe_term_cr : forall ad t,
    safe_term t ->
    safe_term <{cr ad t}>

  | safe_term_ptm : forall tid t,
    safe_term t ->
    safe_term <{ptm tid t}>

  | safe_term_spawn : forall t,
    safe_term t ->
    safe_term <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-boundaries                                                           *)
(* ------------------------------------------------------------------------- *)

(* A term is safely bounded if ... *)
Inductive safe_boundaries : tm -> Prop :=
  | safe_boundaries_unit :
    safe_boundaries <{unit}>

  | safe_boundaries_nat : forall n,
    safe_boundaries <{nat n}>

  | safe_boundaries_var : forall x,
    safe_boundaries <{var x}>

  | safe_boundaries_fun : forall x Tx t,
    safe_boundaries t ->
    safe_boundaries <{fn x Tx t}>

  | safe_boundaries_call : forall t1 t2,
    safe_boundaries t1 ->
    safe_boundaries t2 ->
    safe_boundaries <{call t1 t2}>

  | safe_boundaries_ref : forall ad T,
    safe_boundaries <{&ad : T}>

  | safe_boundaries_new : forall T t,
    safe_boundaries t ->
    safe_boundaries <{new t : T}>

  | safe_boundaries_load : forall t,
    safe_boundaries t ->
    safe_boundaries <{*t}>

  | safe_boundaries_asg : forall t1 t2,
    safe_boundaries t1 ->
    safe_boundaries t2 ->
    safe_boundaries <{t1 := t2}>

  | safe_boundaries_acq1 : forall t1 t2,
    ~ value t2 ->
    safe_boundaries t1 ->
    safe_boundaries t2 ->
    safe_boundaries <{acq t1 t2}>

  | safe_boundaries_acq2 : forall t1 t2,
    value t2 ->
    safe_term t2 ->
    safe_boundaries <{acq t1 t2}>

  | safe_boundaries_cr1 : forall ad t,
    ~ value t ->
    safe_boundaries t ->
    safe_boundaries <{cr ad t}>

  | safe_boundaries_cr2 : forall ad t,
    value t ->
    safe_term t ->
    safe_boundaries <{cr ad t}>

  | safe_boundaries_ptm : forall tid t,
    safe_boundaries t ->
    safe_boundaries <{ptm tid t}>

  | safe_boundaries_spawn : forall t,
    safe_term t ->
    safe_boundaries <{spawn t}>
  .

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

(*
(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

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
