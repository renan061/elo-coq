From Elo Require Import Core.


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

