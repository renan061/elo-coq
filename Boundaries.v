From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* safe-value                                                                *)
(* ------------------------------------------------------------------------- *)

Inductive safe_value : tm -> Prop :=
  | sv_unit :              safe_value <{unit       }>
  | sv_num  : forall n,    safe_value <{nat n      }>
  | sv_refR : forall ad T, safe_value <{&ad : `r&T`}>
  | sv_refX : forall ad T, safe_value <{&ad : `x&T`}>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _sval tt := match goal with H : safe_value _ |- _ => tt H end.

Ltac inv_sval  := _sval inv.
Ltac invc_sval := _sval invc.

(* ------------------------------------------------------------------------- *)
(* safe-boundaries                                                           *)
(* ------------------------------------------------------------------------- *)

Inductive safe_boundaries : tm -> Prop :=
  | sb_unit  :                  safe_boundaries <{unit      }>

  | sb_nat   : forall n,        safe_boundaries <{nat n     }>

  | sb_var   : forall x,        safe_boundaries <{var x     }>

  | sb_fun   : forall x Tx t,   safe_boundaries t  ->
                                safe_boundaries <{fn x Tx t }>

  | sb_call  : forall t1 t2,    safe_boundaries t1 ->
                                safe_boundaries t2 ->
                                safe_boundaries <{call t1 t2}>

  | sb_ref   : forall ad T,     safe_boundaries <{&ad : T   }>

  | sb_new   : forall T t,      safe_boundaries t  ->
                                safe_boundaries <{new t : T }>

  | sb_load  : forall t,        safe_boundaries t  ->
                                safe_boundaries <{*t        }>

  | sb_asg   : forall t1 t2,    safe_boundaries t1 ->
                                safe_boundaries t2 ->
                                safe_boundaries <{t1 := t2  }>

  | sb_acq   : forall t1 t2,    safe_boundaries t1 ->
                                safe_boundaries t2 ->
                                safe_boundaries <{acq t1 t2 }>

  | sb_cr1   : forall ad t,     ~ value t          ->
                                safe_boundaries t  ->
                                safe_boundaries <{cr ad t   }>

  | sb_cr2   : forall ad t,     value t            ->
                                safe_value t       ->
                                safe_boundaries <{cr ad t   }>

  | sb_spawn : forall t,        safe_boundaries t  ->
                                safe_boundaries <{spawn t   }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _sb tt :=
  match goal with
  | H : safe_boundaries <{unit     }>   |- _ => clear H
  | H : safe_boundaries <{nat _    }>   |- _ => clear H
  | H : safe_boundaries <{var _    }>   |- _ => clear H
  | H : safe_boundaries <{fn _ _ _ }>   |- _ => tt H
  | H : safe_boundaries <{call _ _ }>   |- _ => tt H
  | H : safe_boundaries <{& _ : _  }>   |- _ => clear H
  | H : safe_boundaries <{new _ : _}>   |- _ => tt H
  | H : safe_boundaries <{* _      }>   |- _ => tt H
  | H : safe_boundaries <{_ := _   }>   |- _ => tt H
  | H : safe_boundaries <{acq _  _ }>   |- _ => tt H
  | H : safe_boundaries <{cr _ _   }>   |- _ => tt H
  | H : safe_boundaries <{spawn _  }>   |- _ => tt H
  end.

Ltac inv_sb  := _sb inv.
Ltac invc_sb := _sb invc.

(* preservation ------------------------------------------------------------ *)

(* TODO *)
