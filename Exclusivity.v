From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import ConsistentTerm.

(* ------------------------------------------------------------------------- *)
(* init-cr-exclusivity                                                       *)
(* ------------------------------------------------------------------------- *)

Definition init_cr_exclusivity (ths : threads) := forall ad tid1 tid2,
  (one_init ad ths[tid1] -> no_cr   ad ths[tid2]) /\
  (one_cr   ad ths[tid1] -> no_init ad ths[tid2]).

(* auxiliary --------------------------------------------------------------- *)

Theorem oneinit_from_insert : forall m ths tid t ad' t' T',
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_term m) ->
  unique_initializers m ths ->
  (* --- *)
  ths[tid] --[e_insert ad' t' T']--> t ->
  one_init ad' ths[tid].
Proof.
  intros * ? ? Hui **.
  assert (Had'  : ad' < #m) by eauto using vtm_insert_address.
  assert (Hnone : m[ad'].t = None) by eauto using insert_then_uninitialized.
  specialize (Hui ad' Had') as [_ Hui]. specialize (Hui Hnone) as [tid' [? ?]].
  nat_eq_dec tid' tid; trivial.
  exfalso. eauto using noinit_insert_contradiction.
Qed.

Theorem onecr_from_rel : forall m ths tid t ad,
  unique_critical_regions m ths ->
  (* --- *)
  ths[tid] --[e_rel ad]--> t ->
  one_cr ad ths[tid].
Proof.
  intros * Hucr **. specialize (Hucr ad) as [Hfalse Htrue].
  destruct (m[ad].X) eqn:?.
  - specialize (Htrue eq_refl) as [tid' [? ?]]; clear Hfalse.
    nat_eq_dec tid' tid; trivial.
    exfalso. eauto using nocr_rel_contradiction.
  - specialize (Hfalse eq_refl); clear Htrue.
    exfalso. eauto using nocr_rel_contradiction.
Qed.

(* preservation ------------------------------------------------------------ *)

Lemma ice_preservation_none : forall m ths tid t,
  forall_threads ths (valid_term m) ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_none]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros * ? Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto;
  eauto using nocr_preservation_none, oneinit_inheritance_none;
  eauto using noinit_preservation_none, onecr_inheritance_none.
Qed.

Lemma ice_preservation_alloc : forall m ths tid t T,
  forall_threads ths (valid_term m) ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 1. intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  assert (forall tid, no_cr (#m) ths[tid]) by eauto using nocr_from_vtm1.
  split; intros; repeat omicron; auto; nat_eq_dec (#m) ad;
  eauto using nocr_preservation_alloc, oneinit_inheritance_alloc;
  eauto using noinit_preservation_alloc, onecr_inheritance_alloc;
  exfalso; eauto using onecr_inheritance_alloc, nocr_onecr_contradiction.
Qed.

Lemma ice_preservation_insert : forall m ths tid t ad' t' T',
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_term m) ->
  unique_initializers m ths ->
  unique_critical_regions m ths ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_insert ad' t' T']--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 4. intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; nat_eq_dec ad' ad;
  eauto using nocr_preservation_insert, oneinit_inheritance_insert;
  eauto using noinit_preservation_insert, onecr_inheritance_insert;
  exfalso.
  - assert (one_init ad ths[tid2]) by eauto using oneinit_from_insert.
    assert (no_init ad t) by eauto using oneinit_to_noinit.
    eauto using noinit_oneinit_contradiction.
  - assert (one_init ad ths[tid1]) by eauto using oneinit_from_insert.
    assert (no_init ad t) by eauto using oneinit_to_noinit.
    eauto using noinit_oneinit_contradiction.
  - assert (one_cr ad ths[tid2]) by eauto using onecr_inheritance_insert.
    eauto using noinit_insert_contradiction.
  - eauto using noinit_insert_contradiction.
Qed.

Lemma ice_preservation_read : forall m ths tid t ad' t',
  no_inits t' ->
  no_crs   t' ->
  forall_threads ths (valid_term m) ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_read ad' t']--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 3. intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto;
  eauto using nocr_preservation_read, oneinit_inheritance_read;
  eauto using noinit_preservation_read, onecr_inheritance_read.
Qed.

Lemma ice_preservation_write : forall m ths tid t ad te,
  forall_threads ths (valid_term m) ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_write ad te]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 1. rename ad into ad'.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; nat_eq_dec ad' ad;
  eauto using nocr_preservation_write, oneinit_inheritance_write;
  eauto using noinit_preservation_write, onecr_inheritance_write.
Qed.

Lemma oneinit_then_uninitialized : forall ad m t,
  consistent_term m t ->
  one_init ad t ->
  m[ad].t = None.
Proof.
  intros. induction t; invc_ctm; invc_oneinit; auto.
Qed.

Lemma noref_from_oneinit : forall ad m ths tid,
  forall_threads ths (consistent_term m) ->
  no_uninitialized_references m ths ->
  (* --- *)
  one_init ad ths[tid] ->
  forall_threads ths (no_ref ad).
Proof.
  intros * ? Hnur ?.
  assert (Hnone : m[ad].t = None) by eauto using oneinit_then_uninitialized.
  specialize (Hnur ad Hnone) as [_ ?]. assumption.
Qed.

Lemma ice_preservation_acq : forall m ths tid t ad' t',
  no_inits t' ->
  no_crs   t' ->
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_term m) ->
  no_uninitialized_references m ths ->
  unique_initializers m ths ->
  (* --- *)
  m[ad'].t = Some t' ->
  init_cr_exclusivity ths ->
  ths[tid] --[e_acq ad' t']--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 5. intros Hui ? Hice ? ad tid1 tid2.
  assert (m[ad'].t <> None) by auto.
  assert (Had : ad' < #m) by (lt_eq_gt ad' (#m); sigma; upsilon; eauto).
  specialize (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; nat_eq_dec ad' ad;
  eauto using nocr_preservation_acq, oneinit_inheritance_acq;
  eauto using noinit_preservation_acq, onecr_inheritance_acq.
  - exfalso. eapply noref_acq_contradiction; eauto.
    assert (one_init ad ths[tid2]) by eauto using oneinit_inheritance_acq.
    eapply noref_from_oneinit; eauto.
  - exfalso. eapply noref_acq_contradiction; eauto.
    eapply noref_from_oneinit; eauto.
  - specialize (Hui ad Had) as [Hnone _]. spec.
    eauto using noinit_preservation_acq.
  - specialize (Hui ad Had) as [Hnone _]. spec.
    eauto.
Qed.

Lemma ice_preservation_rel : forall m ths tid t ad,
  unique_critical_regions m ths ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_rel ad]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 1. rename ad into ad'.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; nat_eq_dec ad' ad;
  eauto using nocr_preservation_rel, oneinit_inheritance_rel;
  eauto using noinit_preservation_rel, onecr_inheritance_rel;
  eauto using onecr_from_rel;
  exfalso.
  - eauto using onecr_from_rel, noinit_preservation_rel,
      noinit_oneinit_contradiction.
  - eauto using onecr_from_rel, nocr_onecr_contradiction.
  - eauto using onecr_from_rel, onecr_to_nocr, nocr_onecr_contradiction.
Qed.

Lemma ice_preservation_spawn : forall m ths tid t te,
  forall_threads ths (valid_term m) ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  init_cr_exclusivity (ths[tid <- t] +++ te).
Proof.
  intros until 1.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  assert (no_init ad te) by eauto using noinit_spawn_term.
  assert (no_cr ad te) by eauto using nocr_spawn_term.
  split; intros; repeat omicron; auto; eauto using no_cr;
  eauto using nocr_preservation_spawn, oneinit_inheritance_spawn;
  eauto using noinit_preservation_spawn, onecr_inheritance_spawn;
  exfalso; eauto using noinit_oneinit_contradiction, nocr_onecr_contradiction.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem ice_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1      value                ->
  forall_program m1 ths1 (valid_term m1)      ->
  forall_program m1 ths1 (consistent_term m1) ->
  no_uninitialized_references m1 ths1         ->
  unique_initializers m1 ths1                 ->
  unique_critical_regions m1 ths1             ->
  (* --- *)
  init_cr_exclusivity ths1                    ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2           ->
  init_cr_exclusivity ths2.
Proof.
  intros * ? [? ?] [? ?] **. invc_cstep; try invc_mstep.
  - eauto using ice_preservation_none.
  - eauto using ice_preservation_alloc.
  - eauto using ice_preservation_insert.
  - eauto 8 using noinits_from_value, nocrs_from_value, ice_preservation_read.
  - eauto using ice_preservation_write.
  - eauto 8 using noinits_from_value, nocrs_from_value, ice_preservation_acq.
  - eauto using ice_preservation_rel.
  - eauto using ice_preservation_spawn.
Qed.

Theorem ice_preservation_rstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1      value                ->
  forall_program m1 ths1 (valid_term m1)      ->
  forall_program m1 ths1 (consistent_term m1) ->
  no_uninitialized_references m1 ths1         ->
  unique_initializers m1 ths1                 ->
  unique_critical_regions m1 ths1             ->
  (* --- *)
  init_cr_exclusivity ths1                    ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2          ->
  init_cr_exclusivity ths2.
Proof.
  intros. invc_ostep; eauto using ice_preservation_cstep.
Qed.

Theorem ice_preservation_base : forall t,
  no_inits t ->
  no_crs   t ->
  init_cr_exclusivity (base_t t).
Proof.
  unfold base_t. repeat intro. split; intro; simpl;
  repeat (destruct tid2; eauto using no_init, no_cr).
Qed.

(* ------------------------------------------------------------------------- *)
(* term-init-cr-exc                                                          *)
(* ------------------------------------------------------------------------- *)

Definition term_init_cr_exc (t : tm) := forall ad,
  (no_init ad t \/ one_init ad t) /\
  (no_cr   ad t \/ one_cr   ad t) /\
  (one_init ad t -> no_cr   ad t) /\
  (one_cr   ad t -> no_init ad t).

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_tice :=
  intros * H; try match goal with |- _ /\ _ => split end; intros ad';
  specialize (H ad') as [[? | ?] [[? | ?] [? ?]]]; repeat split; repeat spec;
  try inv_oneinit; try inv_onecr; try inv_nocr; try inv_noinit; auto; intros ?;
  exfalso; eauto using noinit_oneinit_contradiction, nocr_onecr_contradiction. 

Local Lemma inv_tice_seq : forall t1 t2,
  term_init_cr_exc <{t1; t2}> ->
  term_init_cr_exc t1 /\ term_init_cr_exc t2.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_fun : forall x Tx t,
  term_init_cr_exc <{fn x Tx t}> ->
  term_init_cr_exc t.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_call : forall t1 t2,
  term_init_cr_exc <{call t1 t2}> ->
  term_init_cr_exc t1 /\ term_init_cr_exc t2.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_new : forall t T,
  term_init_cr_exc <{new t : T}> ->
  term_init_cr_exc t.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_init : forall ad t T,
  term_init_cr_exc <{init ad t : T}> ->
  term_init_cr_exc t.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_load : forall t,
  term_init_cr_exc <{*t}> ->
  term_init_cr_exc t.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_asg : forall t1 t2,
  term_init_cr_exc <{t1 := t2}> ->
  term_init_cr_exc t1 /\ term_init_cr_exc t2.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_acq : forall t1 x t2,
  term_init_cr_exc <{acq t1 x t2}> ->
  term_init_cr_exc t1 /\ term_init_cr_exc t2.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_cr : forall ad t,
  term_init_cr_exc <{cr ad t}> ->
  term_init_cr_exc t.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_spawn : forall t,
  term_init_cr_exc <{spawn t}> ->
  term_init_cr_exc t.
Proof. solve_inv_tice. Qed.

Ltac invc_tice :=
  match goal with
  | H : term_init_cr_exc <{unit        }> |- _ => clear H
  | H : term_init_cr_exc <{nat _       }> |- _ => clear H
  | H : term_init_cr_exc <{_; _        }> |- _ => eapply inv_tice_seq   in H
  | H : term_init_cr_exc <{var _       }> |- _ => clear H
  | H : term_init_cr_exc <{fn _ _ _    }> |- _ => eapply inv_tice_fun   in H
  | H : term_init_cr_exc <{call _ _    }> |- _ => eapply inv_tice_call  in H
  | H : term_init_cr_exc <{& _ : _     }> |- _ => clear H
  | H : term_init_cr_exc <{new _ : _   }> |- _ => eapply inv_tice_new   in H
  | H : term_init_cr_exc <{init _ _ : _}> |- _ => eapply inv_tice_init  in H
  | H : term_init_cr_exc <{* _         }> |- _ => eapply inv_tice_load  in H
  | H : term_init_cr_exc <{_ := _      }> |- _ => eapply inv_tice_asg   in H
  | H : term_init_cr_exc <{acq _ _ _   }> |- _ => eapply inv_tice_acq   in H
  | H : term_init_cr_exc <{cr _ _      }> |- _ => eapply inv_tice_cr    in H
  | H : term_init_cr_exc <{spawn _     }> |- _ => eapply inv_tice_spawn in H
  end;
  repeat match goal with
  | H : term_init_cr_exc _ /\ term_init_cr_exc _ |- _ => destruct H
  end.

(* ------------------------------------------------------------------------- *)

Theorem tice_from_ice : forall m ths,
  forall_threads ths (valid_term m) ->
  unique_initializers m ths ->
  unique_critical_regions m ths ->
  (* --- *)
  init_cr_exclusivity ths ->
  forall_threads ths term_init_cr_exc.
Proof.
  intros * ? Hui Hucr Hice tid ad. specialize (Hice ad tid tid) as [? ?].
  eauto 6 using noinit_or_oneinit_from_ui, nocr_or_onecr_from_ucr.
Qed.

