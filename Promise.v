From Elo Require Import Core.

From Elo Require Import Properties1.

From Elo Require Import NoRef.
From Elo Require Import NoWRef.
From Elo Require Import NoUninitRefs.
From Elo Require Import ConsistentInits.
From Elo Require Import ConsistentRefs.
From Elo Require Import InitCRExclusivity.

From Elo Require Import AccessCore.
From Elo Require Import PointerTypes.
From Elo Require Import Inheritance.
From Elo Require Import SafeNewX.

(* ------------------------------------------------------------------------- *)
(* exclusivity-promise                                                       *)
(* ------------------------------------------------------------------------- *)

(*
xaccess adx ad m t ->
one_cr adx t.

no_cr adx t ->
xaccess adx ad m t ->
False.

write ----------------------- read

Definition exclusivity_promise0 (m : mem) (ths : threads) :=
  forall adx ad tid1 tid2 T,
    tid1 <> tid2 ->
    m[ad].T = `w&T` ->
    xaccess adx ad m ths[tid1] ->
    xaccess adx ad m ths[tid2] ->
    False.

Definition exclusivity_promise0 (m : mem) (ths : threads) :=
  forall adx ad tid1 tid2 T,
    adx <> adx' ->
    m[ad].T = `w&T` ->
    xaccess adx  ad m ths[tid1] ->
    xaccess adx' ad m ths[tid2] ->
    False.
*)

Definition exclusivity_promise (m : mem) (ths : threads) :=
  forall adx ad tid1 tid2 T,
    m[ad].T = `w&T` ->
    xaccess adx ad m ths[tid2] ->
    access ad m ths[tid1] ->
    False.

(* preservation ------------------------------------------------------------ *)

Local Lemma ep_preservation_none : forall m ths tid t,
  forall_threads ths valid_blocks ->
  (* --- *)
  exclusivity_promise m ths ->
  ths[tid] --[e_none]--> t ->
  exclusivity_promise m ths[tid <- t].
Proof.
  intros. intros until 3. repeat omicron; try solve [invc_acc || invc_xacc];
  eauto using acc_inheritance_none, xacc_inheritance_none.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma noref_xacc_contradiction : forall m t adx ad,
  forall_memory m (no_ref ad) ->
  no_ref ad t ->
  xaccess adx ad m t ->
  False.
Proof.
  intros * ? ? H. induction H; invc_noref; eauto using noref_acc_contradiction.
Qed.

Lemma vad_nacc_length : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  access (#m) m t ->
  False.
Proof.
  intros until 2. intros Hacc. induction Hacc; invc_vad; auto; eauto.
Qed.

Lemma vad_nxacc_length : forall adx m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  xaccess adx (#m) m t ->
  False.
Proof.
  intros until 2. intros Hxacc.
  induction Hxacc; invc_vad; eauto using vad_nacc_length.
Qed.

Lemma acc_nowref_contradiction : forall ad m t T,
  forall_memory m value ->
  forall_memory m (consistent_references m) ->
  consistent_references m t ->
  (* --- *)
  m[ad].T = `w&T` ->
  access ad m t ->
  no_wrefs t ->
  False.
Proof.
  intros * ? ? ? ? Hacc ?.
  induction Hacc; invc_cr; invc_nowrefs; eauto. invc_eq.
  assert (write_access ad m t0) by (eapply ptyp_wacc_correlation; eauto).
  eauto using wacc_safe_contradiction.
Qed.

Lemma alloc_xacc_contradiciton : forall adx ad m t1 t2 T Te,
  forall_memory m value ->
  forall_memory m (consistent_references m) ->
  consistent_references m t1 ->
  (* --- *)
  m[ad].T = `w&T` ->
  safe_newx t1 ->
  t1 --[e_alloc adx Te]--> t2 ->
  xaccess adx ad m t2 ->
  one_init adx t2 ->
  no_cr    adx t2 ->
  False.
Proof.
  intros. ind_tstep; invc_cr; invc_snx; invc_xacc; invc_oneinit; invc_nocr;
  eauto;
  eauto using xacc_noinit_nocr_contradiction;
  eauto using noinit_inheritance_alloc, noinit_to_oneinit,
    noinit_oneinit_contradiction.
  eauto using acc_nowref_contradiction.
Qed.

Local Lemma ep_preservation_alloc : forall m ths tid t T,
  forall_memory m value ->
  forall_memory m (consistent_references m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  forall_threads ths (consistent_references m) ->
  forall_threads ths safe_newx ->
  no_uninitialized_references m ths ->
  init_cr_exclusivity ths ->
  (* --- *)
  exclusivity_promise m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  exclusivity_promise (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros until 7. intros Hice. intros Hep Htstep.
  assert (Hvad' : valid_addresses (m +++ (None, T, false)) t)
    by eauto using vad_preservation_alloc.
  assert
    (Hnur' : no_uninitialized_references (m +++ (None, T, false)) ths[tid <- t])
    by eauto using nur_preservation_alloc.
  rename T into T'.
  intros until 3. upsilon.
  - assert (Hm : (m +++ (None, `w&T`, false))[#m].t = None) by (sigma; trivial).
    specialize (Hnur' (#m) Hm) as [? Hths].
    repeat omicron; try solve [invc_acc || invc_xacc].
    + specialize (Hths tid2). sigma. eauto using noref_acc_contradiction.
    + specialize (Hths tid1). sigma. eauto using noref_acc_contradiction.
    + specialize (Hths tid1). sigma. eauto using noref_acc_contradiction.
    + specialize (Hths tid1). sigma. eauto using noref_acc_contradiction.
  - repeat omicron; try solve [invc_acc || invc_xacc].
    + destruct (nat_eq_dec (#m) adx); subst.
      * assert (xaccess (#m) ad m t) by eauto using xacc_inheritance_mem_add.
        assert (no_init (#m) ths[tid2]) by eauto using noinit_from_vad.
        assert (one_init (#m) t) by eauto using noinit_to_oneinit.
        eapply ice_preservation_alloc in Hice; eauto.
        specialize (Hice (#m) tid2 tid2) as [? ?]; sigma.
        eauto using alloc_xacc_contradiciton.
      * eauto using acc_inheritance_alloc, xacc_inheritance_alloc.
    + eauto using acc_inheritance_alloc, xacc_inheritance_mem_add.
    + destruct (nat_eq_dec (#m) adx); subst.
      * assert (xaccess (#m) ad m t) by eauto using xacc_inheritance_mem_add.
        assert (no_init (#m) ths[tid2]) by eauto using noinit_from_vad.
        assert (one_init (#m) t) by eauto using noinit_to_oneinit.
        eapply ice_preservation_alloc in Hice; eauto.
        specialize (Hice (#m) tid2 tid2) as [? ?]; sigma.
        eauto using alloc_xacc_contradiciton.
      * eauto using xacc_inheritance_alloc, acc_inheritance_mem_add.
    + eauto using acc_inheritance_mem_add, xacc_inheritance_mem_add.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma insert_acc_xacc_contradiction : forall adx ad m t t1 t2,
  forall_memory m (no_ref ad) ->
  no_ref ad t1 ->
  t1 --[e_insert ad t]--> t2 ->
  access ad m[ad.t <- t] t2 ->
  xaccess adx ad m[ad.t <- t] t2 ->
  False.
Proof.
  intros. ind_tstep; invc_noref; invc_acc; invc_xacc;
  eauto using acc_inheritance_mem_set1, noref_acc_contradiction;
  eauto using xacc_inheritance_mem_set1, noref_xacc_contradiction.
Qed.

Local Lemma ep_preservation_insert : forall m ths tid t ad te,
  forall_threads ths (consistent_inits m) ->
  no_uninitialized_references m ths ->
  (* --- *)
  exclusivity_promise m ths ->
  ths[tid] --[e_insert ad te]--> t ->
  exclusivity_promise m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 2. rename ad into ad'.
  intros Hep Htstep adx ad tid1 tid2 T Had Hxacc Hacc.
  assert (forall_program m ths (no_ref ad')) as [? ?]
    by eauto using noref_from_insert.
  repeat omicron; upsilon; try solve [invc Had | invc_acc | invc_xacc].
  - eauto using insert_acc_xacc_contradiction.
  - eauto using acc_inheritance_insert, xacc_inheritance_insert.
  - eauto using xacc_inheritance_mem_set1, noref_xacc_contradiction.
  - eauto using acc_inheritance_insert, xacc_inheritance_mem_set1.
  - eauto using acc_inheritance_mem_set1, noref_acc_contradiction.
  - eauto using acc_inheritance_mem_set1, xacc_inheritance_insert.
  - eauto using xacc_inheritance_mem_set1, noref_xacc_contradiction.
  - eauto using acc_inheritance_mem_set1, xacc_inheritance_mem_set1.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma ep_preservation_read : forall m ths tid t ad te,
  forall_memory m value ->
  forall_memory m valid_blocks ->
  forall_threads ths well_typed_term ->
  (* --- *)
  m[ad].t = Some te ->
  exclusivity_promise m ths ->
  ths[tid] --[e_read ad te]--> t ->
  exclusivity_promise m ths[tid <- t].
Proof.
  intros until 4. rename ad into ad'.
  intros Hep Htstep adx ad tid1 tid2 T Had Hxacc Hacc.
  repeat omicron; try solve [invc_acc | invc_xacc];
  eauto using acc_inheritance_read, xacc_inheritance_read.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma ep_preservation_write : forall m ths tid t ad te,
  exclusivity_promise m ths ->
  ths[tid] --[e_write ad te]--> t ->
  exclusivity_promise m[ad.t <- te] ths[tid <- t].
Proof.
  intros *. rename ad into ad'.
  intros Hep Htstep adx ad tid1 tid2 T Had Hxacc Hacc.
  repeat omicron; upsilon; try solve [invc Had | invc_acc | invc_xacc].
  - destruct (acc_dec ad m ths[tid2]), (xacc_dec adx ad m ths[tid2]); eauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.

