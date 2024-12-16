From Coq Require Import Lia.
From Coq Require Import List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

(* ------------------------------------------------------------------------- *)
(* consistent-regions                                                        *)
(* ------------------------------------------------------------------------- *)

Inductive todo2 (o : owners) (s : stack region) (R : region) : tm -> Prop :=
  | creg_unit  :                      todo2 o s R <{unit           }>
  | creg_nat   : forall n,            todo2 o s R <{nat n          }>
  | creg_var   : forall x,            todo2 o s R <{var x          }>
  | creg_fun   : forall x Tx t,       todo2 o s R t   ->
                                      todo2 o s R <{fn x Tx t      }>
  | creg_call  : forall t1 t2,        todo2 o s R t1  ->
                                      todo2 o s R t2  ->
                                      todo2 o s R <{call t1 t2     }>
  | creg_refR  : forall ad T,         todo2 o s R <{&ad : r&T      }>
  | creg_refX  : forall ad T,         todo2 o s R <{&ad : x&T      }>
  | creg_refW  : forall ad T,         R = o[ad] or R_any           ->
                                      todo2 o s R <{&ad : w&T      }>
  | creg_new   : forall t T,          todo2 o s R t   ->
                                      todo2 o s R <{new t : T      }>
  | creg_initR : forall ad t T,       todo2 o s R t   ->
                                      todo2 o s R <{init ad t : r&T}>
  | creg_initX : forall s' R' ad t T, R' = R_monitor ad            ->
                                      s' = push s R'               ->  
                                      todo2 o s' R' t ->
                                      todo2 o s R <{init ad t : x&T}>
  | creg_initW : forall ad t T,       R = o[ad] or R_any           ->
                                      todo2 o s R t   ->
                                      todo2 o s R <{init ad t : w&T}>
  | creg_load  : forall t,            todo2 o s R t   ->
                                      todo2 o s R <{*t             }>
  | creg_asg   : forall t1 t2,        todo2 o s R t1  ->
                                      todo2 o s R t2  ->
                                      todo2 o s R <{t1 := t2       }>
  | creg_acq   : forall t1 x t2,      todo2 o s R t1  ->
                                      todo2 o s R t2  ->
                                      todo2 o s R <{acq t1 x t2    }>
  | creg_cr    : forall s' R' ad t,   R' = R_monitor ad            ->
                                      s' = push s R'               -> 
                                      todo2 o s' R' t ->
                                      todo2 o s R <{cr ad t        }>
  | creg_spawn : forall t,            todo2 o s R t   ->
                                      todo2 o s R <{spawn t        }>
  .

