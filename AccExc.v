From Elo Require Import Core.

From Elo Require Import AccessCore.
From Elo Require Import AccessExclusivity.

(* preservation -------------------------------------------------------------*)

Local Lemma accexc_preservation_none : forall m ths tid t,
  acc_exclusivity m ths ->
  ths[tid] --[e_none]--> t ->
  acc_exclusivity m ths[tid <- t].
Proof.
  intros ** ad tid1 tid2 T Had Hacc1 Hacc2.
  repeat omicron; try solve invc_acc; eauto.
  - admit.
  - admit.
  - admit.
Qed.

Theorem accexc_preservation : forall m1 m2 ths1 ths2 tid e,
  acc_exclusivity m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  acc_exclusivity m2 ths2.
Proof.
  intros. invc_cstep; try invc_mstep.
  -
Qed.
