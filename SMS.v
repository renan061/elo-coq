From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import UnsafeAccess.

Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access ad m ths[tid2] ->
  ~ unsafe_access ad m ths[tid1].

