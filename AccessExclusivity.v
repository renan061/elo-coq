From Elo Require Import Core.

From Elo Require Import Properties1.
From Elo Require Import Properties2.

From Elo Require Import AccessCore.

(* ------------------------------------------------------------------------- *)
(* exclusivity promises                                                      *)
(* ------------------------------------------------------------------------- *)

Definition acc_exclusivity (m : mem) (ths : threads) := forall ad tid1 tid2 T,
  m[ad].T = `w&T` ->
  access ad m ths[tid1] ->
  access ad m ths[tid2] ->
  tid1 = tid2.

(* Two different threads cannot have xaccess to an address over the same adx. *)
Definition xacc_exclusivity1 (m : mem) (ths : threads) :=
  forall adx ad tid1 tid2 T,
    m[ad].T = `w&T` ->
    tid1 <> tid2 ->
    xaccess adx ad m ths[tid1] ->
    xaccess adx ad m ths[tid2] ->
    False.

(* 
  A thread cannot have xaccess to an address with two distinct adxs.
  Same goes for two distinct threads.
*)
Definition xacc_exclusivity2 (m : mem) (ths : threads) :=
  forall adx1 adx2 ad tid1 tid2 T,
    m[ad].T = `w&T` ->
    adx1 <> adx2 ->
    xaccess adx1 ad m ths[tid1] ->
    xaccess adx2 ad m ths[tid2] ->
    False.

(* 
  A thread cannot have xaccess to an address while a thread has access.
*)
Definition xacc_acc_exclusivity (m : mem) (ths : threads) :=
  forall adx ad tid1 tid2 T,
    m[ad].T = `w&T` ->
    xaccess adx ad m ths[tid2] ->
    access ad m ths[tid1] ->
    False.

(* ------------------------------------------------------------------------- *)
(* xacc-exclusivity1 preservation                                            *)
(* ------------------------------------------------------------------------- *)

Theorem xaccexc1_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths2 (valid_addresses m2) ->
  unique_initializers m2 ths2 ->
  unique_critical_regions m2 ths2 ->
  init_cr_exclusivity ths2 ->
  (* --- *)
  xacc_exclusivity1 m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  xacc_exclusivity1 m2 ths2.
Proof.
  intros * ? Hui Hucr Hice.
  intros ** adx ad tid1 tid2 T Hptyp Hneq Hxacc1 Hxacc2.
  destruct (Hice adx tid1 tid2) as [? ?].
  assert (Hadx : adx < #m2) by eauto using xacc_adx_bounds.
  assert ((one_init adx ths2[tid1]) \x/ (one_cr adx ths2[tid1]))
    as [[? | ?] ?] by eauto using oneinit_xor_onecr_from_xacc;
  assert ((one_init adx ths2[tid2]) \x/ (one_cr adx ths2[tid2]))
    as [[? | ?] ?] by eauto using oneinit_xor_onecr_from_xacc.
  - eauto using ui_oneinit_contradiction.
  - eauto using nocr_onecr_contradiction.
  - eauto using noinit_oneinit_contradiction.
  - eauto using ucr_onecr_contradiction.
Qed.

