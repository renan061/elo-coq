From Elo Require Import Core.

From Elo Require Import Properties.

(* ------------------------------------------------------------------------- *)
(* safe-newx                                                                 *)
(* ------------------------------------------------------------------------- *)

Inductive safe_newx : tm -> Prop :=
  | snx_unit  :                safe_newx <{unit         }>
  | snx_nat   : forall n,      safe_newx <{nat n        }>
  | snx_var   : forall x,      safe_newx <{var x        }>
  | snx_fun   : forall x Tx t, safe_newx t  ->
                               safe_newx <{fn x Tx t    }>
  | snx_call  : forall t1 t2,  safe_newx t1 ->
                               safe_newx t2 ->
                               safe_newx <{call t1 t2   }>
  | snx_ref   : forall ad T,   safe_newx <{&ad : T      }>
  | snx_newR   : forall t T,   safe_newx t  ->
                               safe_newx <{new t : r&T  }>
  | snx_newX   : forall t T,   no_wrefs t         ->
                               safe_newx t  ->
                               safe_newx <{new t : x&T  }>
  | snx_newW   : forall t T,   safe_newx t  ->
                               safe_newx <{new t : w&T  }>
  | snx_init  : forall ad t T, safe_newx t  ->
                               safe_newx <{init ad t : T}>
  | snx_load  : forall t,      safe_newx t  ->
                               safe_newx <{*t           }>
  | snx_asg   : forall t1 t2,  safe_newx t1 ->
                               safe_newx t2 ->
                               safe_newx <{t1 := t2     }>
  | snx_acq   : forall t1 t2,  safe_newx t1 ->
                               safe_newx t2 ->
                               safe_newx <{acq t1 t2    }>
  | snx_cr    : forall ad t,   safe_newx t  ->
                               safe_newx <{cr ad t      }>
  | snx_spawn : forall t,      safe_newx t  ->
                               safe_newx <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _snx tt :=
  match goal with
  | H : safe_newx <{unit        }>   |- _ => clear H
  | H : safe_newx <{nat _       }>   |- _ => clear H
  | H : safe_newx <{var _       }>   |- _ => clear H
  | H : safe_newx <{fn _ _ _    }>   |- _ => tt H
  | H : safe_newx <{call _ _    }>   |- _ => tt H
  | H : safe_newx <{& _ : _     }>   |- _ => clear H
  | H : safe_newx <{new _ : _   }>   |- _ => tt H
  | H : safe_newx <{init _ _ : _}>   |- _ => tt H
  | H : safe_newx <{* _         }>   |- _ => tt H
  | H : safe_newx <{_ := _      }>   |- _ => tt H
  | H : safe_newx <{acq _  _    }>   |- _ => tt H
  | H : safe_newx <{cr _ _      }>   |- _ => tt H
  | H : safe_newx <{spawn _     }>   |- _ => tt H
  end.

Ltac inv_snx  := _snx inv.
Ltac invc_snx := _snx invc.

(* preservation ------------------------------------------------------------ *)

(* TODO *)

