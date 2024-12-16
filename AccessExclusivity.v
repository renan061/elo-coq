From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Access.
From Elo Require Import XAccess.

(* ------------------------------------------------------------------------- *)
(* exclusivity promises                                                      *)
(* ------------------------------------------------------------------------- *)

Definition acc_exclusivity (m : mem) (ths : threads) := forall ad tid1 tid2 T,
  m[ad].T = `w&T` ->
  access ad ths[tid1] ->
  access ad ths[tid2] ->
  tid1 = tid2.

(* Two different threads cannot have xaccess to an address over the same adx. *)
Definition xacc_exclusivity1 (m : mem) (ths : threads) :=
  forall adx ad tid1 tid2 T,
    m[ad].T = `w&T` ->
    tid1 <> tid2 ->
    xaccess adx ad ths[tid1] ->
    xaccess adx ad ths[tid2] ->
    False.

(* 
  A thread cannot have xaccess to an address with two distinct adxs.
  Same goes for two distinct threads.
*)
Definition xacc_exclusivity2 (m : mem) (ths : threads) :=
  forall adx1 adx2 ad tid1 tid2 T,
    m[ad].T = `w&T` ->
    adx1 <> adx2 ->
    xaccess adx1 ad ths[tid1] ->
    xaccess adx2 ad ths[tid2] ->
    False.

(* 
  A thread cannot have xaccess to an address while a thread has access.
*)
Definition xacc_acc_exclusivity (m : mem) (ths : threads) :=
  forall adx ad tid1 tid2 T,
    m[ad].T = `w&T` ->
    xaccess adx ad ths[tid2] ->
    access ad ths[tid1] ->
    False.

