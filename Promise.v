From Elo Require Import Core.
From Elo Require Import Properties.

From Elo Require Import AccessCore.
From Elo Require Import Inheritance.

(* ------------------------------------------------------------------------- *)
(* exclusivity-promise                                                       *)
(* ------------------------------------------------------------------------- *)

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

Local Lemma noref_acc_contradiction : forall m t ad,
  forall_memory m (no_ref ad) ->
  no_ref ad t ->
  access ad m t ->
  False.
Proof.
  intros * ? ? H. induction H; invc_noref; eauto.
Qed.

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

Lemma xacc_noinit_nocr_contradiction : forall adx ad m t,
  no_init adx t ->
  no_cr   adx t ->
  xaccess adx ad m t ->
  False.
Proof.
  intros. induction t; invc_noinit; inv_nocr; invc_xacc; eauto.
Qed.

Lemma todo : forall ad m t T,
  consistent_references m t ->
  (* --- *)
  m[ad].T = `w&T` ->
  access ad m t ->
  no_wrefs t ->
  False.
Proof.
  intros * ? ? Hacc ?. induction Hacc; invc_cr; invc_nowrefs; eauto.
  admit. (* Aqui tem que fazer as tretas de poiter type,
  mas dessa vez sem write_access, só com m[ad].T = w&T *)
Abort.

Lemma todo : forall ad m t T1 T2,
  m[ad].T = `w&T1` ->
  no_cr (#m) t ->
  one_init (#m) t ->
  no_wrefs t ->
  xaccess (#m) ad (m +++ (None, T2, false)) t ->
  False.
Proof.
  intros * ? ? ? ? Hxacc. induction Hxacc;
  try solve [
    invc_nowrefs; invc_nocr; inv_oneinit;
    eauto using xacc_noinit_nocr_contradiction
  ].
  invc_nowrefs. invc_nocr. invc_oneinit; eauto.
  - invc_oneinit.
  - 
Abort.







Local Lemma ep_preservation_alloc : forall m ths tid t T,
  forall_threads ths (valid_addresses m) ->
  no_uninitialized_references m ths ->
  (* --- *)
  exclusivity_promise m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  exclusivity_promise (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros * Hvad Hnur Hep Htstep.
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
      * assert (no_init (#m) ths[tid2]) by eauto using vad_noinit_ad.
        assert (one_init (#m) t) by eauto using noinit_to_oneinit.
      * eauto using acc_inheritance_alloc, xacc_inheritance_alloc.
    + eauto using acc_inheritance_alloc, xacc_inheritance_mem_add.
    + destruct (nat_eq_dec (#m) adx); subst.
      * admit.
      * eauto using xacc_inheritance_alloc, acc_inheritance_mem_add.
    + eauto using acc_inheritance_mem_add, xacc_inheritance_mem_add.
Qed.

