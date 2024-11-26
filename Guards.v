From Elo Require Import Core.

From Elo Require Import Properties1.
From Elo Require Import Properties2.

From Elo Require Import AccessCore.
From Elo Require Import NotAccess.
From Elo Require Import NotXAccess.
From Elo Require Import AccessInheritance.

(* ------------------------------------------------------------------------- *)
(* guards                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition guards (adx ad : addr) (m : mem) (t : tm) := 
  exists T, m[adx].t = Some t /\ m[adx].T = `x&T` /\ access ad m t.

(* inheritance lemmas ------------------------------------------------------ *)

Lemma guards_inheritance_mem_add : forall adx ad m t T,
  guards adx ad (m +++ (None, T, false)) t ->
  guards adx ad m t.
Proof.
  intros * [T' [? [? ?]]]. exists T'.
  upsilon; eauto. repeat split; eauto using acc_inheritance_mem_add.
Qed.

Lemma guards_inheritance_mem_set : forall adx ad ad' m t t' T',
  m[ad'].T = `w&T'` ->
  (* --- *)
  (guards adx ad m[ad'.t <- t'] t) \/ (xaccess) ->
  guards adx ad m t.
Proof.
  intros * ? Hacc [T [? [? ?]]]. exists T. upsilon.
  - omicron; upsilon; eauto. invc_eq.
  - sigma. repeat split; trivial. destruct Hacc;
    eauto using acc_inheritance_mem_set2, acc_inheritance_mem_set3.
Qed.

Lemma guards_inheritance_mem_acq : forall adx ad ad' m t,
  guards adx ad m[ad'.X <- true] t ->
  guards adx ad m t.
Proof.
  intros * [T [? [? ?]]]. exists T.
  upsilon; repeat split; eauto using acc_inheritance_mem_acq.
Qed.

Lemma guards_inheritance_mem_rel : forall adx ad ad' m t,
  guards adx ad m[ad'.X <- false] t ->
  guards adx ad m t.
Proof.
  intros * [T [? [? ?]]]. exists T.
  upsilon; repeat split; eauto using acc_inheritance_mem_rel.
Qed.

(* ------------------------------------------------------------------------- *)
(* guard-exclusivity                                                         *)
(* ------------------------------------------------------------------------- *)

Definition guard_exclusivity (m : mem) := forall adx1 adx2 ad t1 t2,
  guards adx1 ad m t1 ->
  guards adx2 ad m t2 ->
  adx1 = adx2.

(* preservation lemmas ----------------------------------------------------- *)

Corollary gexc_mem_add : forall m T,
  guard_exclusivity m ->
  guard_exclusivity (m +++ (None, T, false)).
Proof.
  intros. intros until 2. eauto using guards_inheritance_mem_add.
Qed.

Corollary gexc_mem_set : forall m ad' t' T,
  m[ad'].T = `w&T` ->
  (* --- *)
  guard_exclusivity m ->
  guard_exclusivity m[ad'.t <- t'].
Proof.
  intros * ? ? adx1 adx2 ad t Hg1 Hg2.
Abort.

Corollary gexc_mem_acq : forall ad m,
  guard_exclusivity m ->
  guard_exclusivity m[ad.X <- true].
Proof.
  intros. intros until 2. eauto using guards_inheritance_mem_acq.
Qed.

Corollary gexc_mem_rel : forall ad m,
  guard_exclusivity m ->
  guard_exclusivity m[ad.X <- false].
Proof.
  intros. intros until 2. eauto using guards_inheritance_mem_rel.
Qed.

(* preservation ------------------------------------------------------------ *)

Lemma wtt_ci_write_type : forall m t1 t2 ad' t',
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  exists T, m[ad'].T = `w&T`.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_cr; eauto.
Qed.

Lemma acc_from_write : forall ad' m t t' ths tid,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (consistent_inits m) ->
  forall_threads ths (consistent_references m) ->
  unique_initializers m ths ->
  unique_critical_regions m ths ->
  init_cr_exclusivity ths ->
  (* --- *)
  ~ access ad' m ths[tid] ->
  ths[tid] --[e_write ad' t']--> t ->
  exists adx, xaccess adx ad' m ths[tid].
Proof.
  intros * Hvad Hci Hcr Hui Hucr Hice **.
  (*
  assert (forall adx,
    adx < #m ->
    no_init adx ths[tid] \/ one_init adx ths[tid]
  ) by eauto using noinit_or_oneinit_from_ui.
  assert (forall adx,
    no_cr adx ths[tid] \/ one_cr adx ths[tid]
  ) by eauto using nocr_or_onecr_from_ucr.
  *)
  specialize (Hvad tid). specialize (Hci tid). specialize (Hcr tid).
  ind_tstep; inv_vad; repeat invc_ci; repeat invc_cr; invc_nacc;
  try solve [destruct IHtstep as [adx Hxacc]; eauto using access, xaccess].
  - admit.
  - admit.
  - admit.
  - admit.
  - repeat aspecialize. destruct (acc_dec ad' m t); eauto using xaccess.
    repeat aspecialize. destruct IHtstep as [adx Hxacc].
    exists adx. destruct (nat_eq_dec adx ad); subst; eauto using xaccess.
    eapply xacc_cr_eq. exfalso.
Abort.

Lemma acc_or_xacc_from_write : forall ad' m t t' ths tid,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (consistent_inits m) ->
  forall_threads ths (consistent_references m) ->
  unique_initializers m ths ->
  init_cr_exclusivity ths ->
  (* --- *)
  ths[tid] --[e_write ad' t']--> t ->
  (access ad' m ths[tid]) \/ (exists adx, xaccess adx ad' m ths[tid]).
Proof.
  intros * Hvad Hci Hcr Hui Hice **.
  specialize (Hvad tid). specialize (Hci tid). specialize (Hcr tid).
  ind_tstep; inv_vad; repeat invc_ci; repeat invc_cr;
  try destruct IHtstep as [Hacc | [adx Hxacc]];
  eauto using access, xaccess.
  - assert (ad' <> ad) by admit (* by m[ad].t = None, while m[ad'].t <> None*).
    right. exists adx.
    eapply xacc_initX_neq; trivial.
    intros ?; subst.
    specialize (Hui ad H3) as [_ Hone]. aspecialize.
    (*
    (*
    specialize (Hone tid).
    destruct (nat_eq_dec adx ad); subst; eauto using access, xaccess.
    admit.
    *)
    (*
    specialize (Hui ad). aspecialize.
    specialize Hui as [_ Hnone]. aspecialize.
    specialize Hnone as [tid' [Hone Hnone]].
    *)
  - admit. (* by wtt *)
  - assert (ad' <> ad) by admit (* by asg type*).
    right. exists adx. eapply xacc_cr_neq; eauto.
    *)
Abort.

Local Lemma gexc_preservation_write : forall m t1 t2 ad' t',
  well_typed_term t1 ->
  valid_addresses m t1 ->
  consistent_references m t1 ->
  (* --- *)
  guard_exclusivity m ->
  t1 --[e_write ad' t']--> t2 ->
  guard_exclusivity m[ad'.t <- t'].
Proof.
  intros. intros adx1 adx2 ad tx1 tx2 Hg1 Hg2.
  assert (ad' < #m) by eauto using vad_write_addr.
  assert (exists T', m[ad'].T = `w&T'`) as [T' ?]
    by eauto using wtt_ci_write_type.
  eapply H2.
  - eapply guards_inheritance_mem_set; eauto. clear Hg2.
    specialize Hg1 as [T [Hsome [Hptyp Hacc]]].
    repeat (upsilon || sigma); eauto; try invc_eq.
    eapply Decidable.not_and; eauto using acc_dec; intros [? ?].
Abort.

Theorem gexc_preservation : forall m1 m2 ths1 ths2 tid e,
  guard_exclusivity m1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  guard_exclusivity m2.
Proof.
  intros. invc_cstep; try invc_mstep;
  eauto using gexc_mem_add, gexc_mem_acq, gexc_mem_rel.
  - admit.
  - admit.
Abort.

(* ------------------------------------------------------------------------- *)
(* guards                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition guards (adx ad : addr) (m : mem) (ths : threads) := 
  forall tx1, guards adx ad m tx1 \/ exists tid, xaccess adx ad m ths[tid].

acc m[...] t ->
acc m t



(* ------------------------------------------------------------------------- *)
(* xguard-exclusivity                                                         *)
(* ------------------------------------------------------------------------- *)

Definition xguard_exclusivity (m : mem) (ths : threads) := forall adx1 adx2 ad,
  xguards adx1 ad m ths ->
  xguards adx2 ad m ths ->
  adx1 = adx2.

(* preservation ------------------------------------------------------------ *)

Lemma write_typeX_contradiction : forall m t1 t2 ad' t' T,
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  m[ad'].T = `x&T` ->
  t1 --[e_write ad' t']--> t2 ->
  False.
Proof.
  intros * [T' ?] **. gendep T. gendep T'.
  ind_tstep; intros; repeat invc_typeof; repeat invc_cr; eauto.
Qed.

Local Lemma acc_trans : forall ad1 ad2 m t1 t2,
  m[ad2].t = Some t2 ->
  access ad1 m t2 ->
  access ad2 m t1 ->
  access ad1 m t1.
Proof.
  intros * ? ? Hacc. induction Hacc; eauto using access;
  match goal with |- access ?ad1 _ <{& ?ad2 : _}> =>
    destruct (nat_eq_dec ad1 ad2); subst; eauto using access
  end.
Qed.

Local Lemma xgexc_preservation_write : forall ad' t' t m ths tid,
  forall_threads ths well_typed_term ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (consistent_references m) ->
  (* --- *)
  xguard_exclusivity m ths ->
  ths[tid] --[e_write ad' t']--> t ->
  xguard_exclusivity m [ad'.t <- t'] ths[tid <- t].
Proof.
  intros until 3. intros Hxexc Htstep adx1 adx2 ad Hxg1 Hxg2.
  assert (ad' < #m) by eauto using vad_write_addr.
  specialize (Hxexc adx1 adx2 ad).
  destruct Hxg1 as [[t1 [T1 [Hsome1 [Hptyp1 Hacc1]]]] | ?],
           Hxg2 as [[t2 [T2 [Hsome2 [Hptyp2 Hacc2]]]] | ?].
  - repeat (sigma || upsilon); trivial.
    + exfalso. eauto using write_typeX_contradiction.
    + exfalso. eauto using write_typeX_contradiction.
    + eapply Hxexc.
      * left. exists t1. exists T1. repeat split; trivial. 
        destruct (acc_dec ad m t'); eauto using acc_inheritance_mem_set2.
        destruct (acc_dec ad' m t1); eauto using acc_inheritance_mem_set3.
        destruct (nat_eq_dec ad' ad); subst; trivial.
        clear H3; clear H4; clear Hptyp2; clear Hacc2.
        eapply (acc_trans ad ad' m t1); trivial.
        eapply ; eauto.
Qed.

Theorem xgexc_preservation : forall m1 m2 ths1 ths2 tid e,
  xguard_exclusivity m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  xguard_exclusivity m2 ths2.
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

