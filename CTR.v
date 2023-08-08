From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* consistently-typed-references                                             *)
(* ------------------------------------------------------------------------- *)

Inductive consistently_typed_references (m : mem) : tm -> Prop :=
  | ctr_unit :
    consistently_typed_references m <{unit}> 

  | ctr_num : forall n,
    consistently_typed_references m <{N n}>

  | ctr_refM : forall T ad,
    empty |-- m[ad].tm is T ->
    m[ad].typ = <{{ &T }}> ->
    consistently_typed_references m <{&ad :: &T}>

  | ctr_refI : forall T ad,
    empty |-- m[ad].tm is <{{ Immut T }}> ->
    m[ad].typ = <{{ i&T }}> ->
    consistently_typed_references m <{&ad :: i&T}>

  | ctr_new : forall T t,
    consistently_typed_references m t ->
    consistently_typed_references m <{new T t}> 

  | ctr_load : forall t,
    consistently_typed_references m t ->
    consistently_typed_references m <{*t}> 

  | ctr_asg : forall t1 t2,
    consistently_typed_references m t1 ->
    consistently_typed_references m t2 ->
    consistently_typed_references m <{t1 = t2}> 

  | ctr_var : forall x,
    consistently_typed_references m <{var x}>

  | ctr_fun : forall x Tx t,
    consistently_typed_references m t ->
    consistently_typed_references m <{fn x Tx t}>

  | ctr_call : forall t1 t2,
    consistently_typed_references m t1 ->
    consistently_typed_references m t2 ->
    consistently_typed_references m <{call t1 t2}> 

  | ctr_seq : forall t1 t2,
    consistently_typed_references m t1 ->
    consistently_typed_references m t2 ->
    consistently_typed_references m <{t1; t2}>

  | ctr_spawn : forall t,
    consistently_typed_references m t ->
    consistently_typed_references m <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_ctr tactic :=
  match goal with
  (* irrelevant for unit *)
  (* irrelevant for num  *)
  | H : consistently_typed_references _ <{& _ :: _}> |- _ => tactic H
  | H : consistently_typed_references _ <{new _ _ }> |- _ => tactic H
  | H : consistently_typed_references _ <{* _     }> |- _ => tactic H
  | H : consistently_typed_references _ <{_ = _   }> |- _ => tactic H
  (* irrelevant for var  *)
  | H : consistently_typed_references _ <{fn _ _ _}> |- _ => tactic H
  | H : consistently_typed_references _ <{call _ _}> |- _ => tactic H
  | H : consistently_typed_references _ <{_ ; _   }> |- _ => tactic H
  | H : consistently_typed_references _ <{spawn _ }> |- _ => tactic H
  end.

Ltac inv_ctr := match_ctr inv.

Ltac invc_ctr := match_ctr invc.

