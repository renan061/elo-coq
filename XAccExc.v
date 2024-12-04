From Elo Require Import Core.

From Elo Require Import Properties1.
From Elo Require Import Properties2.

From Elo Require Import AccessCore.
From Elo Require Import AccessInheritance.
From Elo Require Import AccessExclusivity.

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
  assert (Hadx : adx < #m2) by eauto using xacc_vad_adx_bounds.
  assert ((one_init adx ths2[tid1]) \x/ (one_cr adx ths2[tid1]))
    as [[? | ?] ?] by eauto using oneinit_xor_onecr_from_xacc;
  assert ((one_init adx ths2[tid2]) \x/ (one_cr adx ths2[tid2]))
    as [[? | ?] ?] by eauto using oneinit_xor_onecr_from_xacc.
  - eauto using ui_oneinit_contradiction.
  - eauto using nocr_onecr_contradiction.
  - eauto using noinit_oneinit_contradiction.
  - eauto using ucr_onecr_contradiction.
Qed.

(* ------------------------------------------------------------------------- *)
(* xacc-exclusivity2 preservation                                            *)
(* ------------------------------------------------------------------------- *)

Local Lemma xaccexc2_preservation_none : forall m ths tid t,
  forall_threads ths valid_blocks ->
  (* --- *)
  xacc_exclusivity2 m ths ->
  ths[tid] --[e_none]--> t ->
  xacc_exclusivity2 m ths[tid <- t].
Proof.
  intros ** ? **.
  repeat (omicron; try solve invc_xacc); eauto using xacc_inheritance_none.
Qed.

Local Lemma xaccexc2_preservation_alloc : forall m ths tid t T,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  xacc_exclusivity2 m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  xacc_exclusivity2 (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros ** ? **.
  assert (valid_addresses (m +++ (None, T, false)) t)
    by eauto using vad_preservation_alloc.
  upsilon.
  - repeat (omicron; eauto using xacc_vad_ad_contradiction1).
    admit. (* Here *)
  - repeat omicron; try solve invc_xacc.
    + destruct (nat_eq_dec (#m) adx1), (nat_eq_dec (#m) adx2); subst.
      * eauto.
      * admit. (* Here *)
      * admit. (* Here *)
      * eauto using xacc_inheritance_alloc.
    + assert (adx1 < #m) by eauto using xacc_vad_adx_bounds.
      destruct (nat_eq_dec (#m) adx2); subst.
      * admit. (* Here *)
      * eauto using xacc_inheritance_alloc. 
    + assert (adx2 < #m) by eauto using xacc_vad_adx_bounds.
      destruct (nat_eq_dec (#m) adx1); subst.
      * admit. (* Here *)
      * eauto using xacc_inheritance_alloc. 
    + eauto.
Abort.

Local Lemma xaccexc2_preservation_insert : forall m ths tid t ad' t',
  forall_threads ths (consistent_inits m) ->
  no_uninitialized_references m ths ->
  (* --- *)
  xacc_exclusivity2 m ths ->
  ths[tid] --[e_insert ad' t']--> t ->
  xacc_exclusivity2 m[ad'.t <- t'] ths[tid <- t].
Proof.
  intros ** ? **.
  assert (forall_program m ths (no_ref ad')) as [? ?]
    by eauto using noref_from_insert.
  repeat (omicron; try solve invc_xacc); eauto using xacc_inheritance_insert.
Qed.

Theorem xaccexc2_preservation : forall m1 m2 ths1 ths2 tid e,
  (* --- *)
  xacc_exclusivity2 m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  xacc_exclusivity2 m2 ths2.
Proof.
  intros. invc_cstep; try invc_mstep.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Abort.
