From Elo Require Import Core.

From Elo Require Import Blocks.
From Elo Require Import Inits.
From Elo Require Import CriticalRegions.

(* ------------------------------------------------------------------------- *)
(* init-cr-exclusivity                                                       *)
(* ------------------------------------------------------------------------- *)

Definition init_cr_exclusivity (m : mem) (ths : threads) := forall ad tid1 tid2,
  (one_init ad ths[tid1] -> no_cr   ad ths[tid2]) /\
  (one_cr   ad ths[tid1] -> no_init ad ths[tid2]).

(* preservation ------------------------------------------------------------ *)

Lemma ice_preservation_none : forall m ths tid t,
  forall_threads ths valid_blocks ->
  (* --- *)
  init_cr_exclusivity m ths ->
  ths[tid] --[e_none]--> t ->
  init_cr_exclusivity m ths[tid <- t].
Proof.
  intros * ? Hice ? ad tid1 tid2.
  specialize (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron;
  eauto using nocr_preservation_none, oneinit_inheritance_none;
  eauto using noinit_preservation_none, onecr_inheritance_none.
Qed.
