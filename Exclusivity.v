From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import ConsistentTerm.

(* ------------------------------------------------------------------------- *)
(* init-cr-exclusivity                                                       *)
(* ------------------------------------------------------------------------- *)

Definition init_cr_exclusivity (ths : threads) := forall ad tid1 tid2,
  (one_init ad ths[tid1] -> no_cr   ad ths[tid2]) /\
  (one_cr   ad ths[tid1] -> no_init ad ths[tid2]).

(* theorems ---------------------------------------------------------------- *)

Theorem oneinit_from_init : forall m ths tid t ad' t',
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_term m) ->
  unique_initializers m ths ->
  (* --- *)
  ths[tid] --[e_init ad' t']--> t ->
  one_init ad' ths[tid].
Proof.
  intros * ? ? Hui **.
  assert (Had'  : ad' < #m) by eauto using vtm_init_address.
  assert (Hnone : m[ad'].t = None) by eauto using init_then_uninitialized.
  specialize (Hui ad' Had') as [_ Hui]. specialize (Hui Hnone) as [tid' [? ?]].
  nat_eq_dec tid' tid; trivial.
  exfalso. eauto using noinit_init_contradiction.
Qed.

Theorem onecr_from_rel : forall m ths tid t ad',
  mutual_exclusion m ths ->
  (* --- *)
  ths[tid] --[e_rel ad']--> t ->
  one_cr ad' ths[tid].
Proof.
  intros * Huhg **. specialize (Huhg ad') as [Hfalse Htrue].
  destruct (m[ad'].X) eqn:?.
  - specialize (Htrue eq_refl) as [tid' [[? ?] Hnhg]]; clear Hfalse.
    nat_eq_dec tid' tid; trivial.
    specialize (Hnhg tid). spec. destruct Hnhg as [? | [? ?]]; trivial.
    exfalso. eauto using nocr_rel_contradiction.
  - specialize (Hfalse eq_refl); clear Htrue.
    specialize (Hfalse tid) as [? | [? ?]]; trivial.
    exfalso. eauto using nocr_rel_contradiction.
Qed.

Theorem holding_from_rel : forall m ths tid t ad',
  forall_threads ths (valid_term m) ->
  mutual_exclusion m ths            ->
  (* --- *)
  ths[tid] --[e_rel ad']--> t ->
  holding ad' ths[tid].
Proof.
  intros * Hmu **.
  assert (one_cr ad' ths[tid]) by eauto using onecr_from_rel.
  assert (no_reacq ad' ths[tid]) by (eapply noreacq_from_effect; eauto; eauto).
  split; trivial.
Qed.

Theorem onecr_from_wrel : forall m ths tid t ad',
  forall_threads ths (consistent_waits WR_none) ->
  mutual_exclusion m ths                        ->
  (* --- *)
  ths[tid] --[e_wrel ad']--> t ->
  one_cr ad' ths[tid].
Proof.
  intros * ? Hmu **. specialize (Hmu ad') as [Hfalse Htrue].
  destruct (m[ad'].X); spec.
  - specialize Htrue as [tid' [[? ?] Hnhg]].
    nat_eq_dec tid' tid; trivial.
    specialize (Hnhg tid). spec. destruct Hnhg as [? | [? ?]]; trivial.
    exfalso. eauto using nocr_wrel_contradiction.
  - specialize (Hfalse tid) as [? | [? ?]]; trivial.
    exfalso. eauto using nocr_wrel_contradiction.
Qed.

Theorem holding_from_wrel : forall m ths tid t ad',
  forall_threads ths (valid_term m)             ->
  forall_threads ths (consistent_waits WR_none) ->
  mutual_exclusion m ths                        ->
  (* --- *)
  ths[tid] --[e_wrel ad']--> t ->
  holding ad' ths[tid].
Proof.
  intros * Hmu **.
  assert (one_cr ad' ths[tid]) by eauto using onecr_from_wrel.
  assert (no_reacq ad' ths[tid]) by (eapply noreacq_from_effect; eauto; eauto).
  split; trivial.
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

Lemma ice_preservation_init : forall m ths tid t ad' t',
  forall_threads ths (valid_term m) ->
  forall_threads ths (consistent_term m) ->
  unique_initializers m ths ->
  mutual_exclusion m ths ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_init ad' t']--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros until 4. intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; nat_eq_dec ad' ad;
  eauto using nocr_preservation_init, oneinit_inheritance_init;
  eauto using noinit_preservation_init, onecr_inheritance_init;
  exfalso.
  - assert (one_init ad ths[tid2]) by eauto using oneinit_from_init.
    assert (no_init ad t) by eauto using oneinit_to_noinit.
    eauto using noinit_oneinit_contradiction.
  - assert (one_init ad ths[tid1]) by eauto using oneinit_from_init.
    assert (no_init ad t) by eauto using oneinit_to_noinit.
    eauto using noinit_oneinit_contradiction.
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
  mutual_exclusion m ths ->
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
  eauto using onecr_from_rel, noinit_preservation_rel.
Qed.

Lemma ice_preservation_wacq : forall ths tid t ad,
  init_cr_exclusivity ths ->
  ths[tid] --[e_wacq ad]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros *. rename ad into ad'.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; nat_eq_dec ad' ad;
  eauto using nocr_preservation_wacq, oneinit_inheritance_wacq;
  eauto using noinit_preservation_wacq, onecr_inheritance_wacq.
Qed.

Lemma ice_preservation_wrel : forall ths tid t ad,
  init_cr_exclusivity ths ->
  ths[tid] --[e_wrel ad]--> t ->
  init_cr_exclusivity ths[tid <- t].
Proof.
  intros *. rename ad into ad'.
  intros Hice ? ad tid1 tid2.
  destruct (Hice ad tid1 tid2) as [? ?].
  split; intros; repeat omicron; auto; nat_eq_dec ad' ad;
  eauto using nocr_preservation_wrel, oneinit_inheritance_wrel;
  eauto using noinit_preservation_wrel, onecr_inheritance_wrel.
Qed.

Lemma ice_preservation_spawn : forall m ths tid t te,
  forall_threads ths (valid_term m) ->
  (* --- *)
  init_cr_exclusivity ths ->
  ths[tid] --[e_spawn te]--> t ->
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
  mutual_exclusion m1 ths1                    ->
  (* --- *)
  init_cr_exclusivity ths1                    ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2           ->
  init_cr_exclusivity ths2.
Proof.
  intros * ? [? ?] [? ?] **. invc_cstep; try invc_mstep.
  - eauto using ice_preservation_none.
  - eauto using ice_preservation_alloc.
  - eauto using ice_preservation_init.
  - eauto 8 using noinits_from_value, nocrs_from_value, ice_preservation_read.
  - eauto using ice_preservation_write.
  - eauto 8 using noinits_from_value, nocrs_from_value, ice_preservation_acq.
  - eauto using ice_preservation_rel.
  - eauto using ice_preservation_wacq.
  - eauto using ice_preservation_wrel.
  - eauto using ice_preservation_spawn.
Qed.

Theorem ice_preservation_base : forall t,
  no_inits t ->
  no_crs   t ->
  init_cr_exclusivity (base t).
Proof.
  unfold base. repeat intro. split; intro; simpl;
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
  intros * H; repeat match goal with |- _ /\ _ => split end; intros ad';
  specialize (H ad') as [[? | ?] [[? | ?] [? ?]]]; repeat split; repeat spec;
  try inv_oneinit; try inv_onecr; try inv_nocr; try inv_noinit; auto; intro;
  exfalso; eauto using noinit_oneinit_contradiction, nocr_onecr_contradiction. 

Local Lemma inv_tice_plus : forall t1 t2,
  term_init_cr_exc <{t1 + t2}> ->
  term_init_cr_exc t1 /\ term_init_cr_exc t2.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_monus : forall t1 t2,
  term_init_cr_exc <{t1 - t2}> ->
  term_init_cr_exc t1 /\ term_init_cr_exc t2.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_seq : forall t1 t2,
  term_init_cr_exc <{t1; t2}> ->
  term_init_cr_exc t1.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_if : forall t1 t2 t3,
  term_init_cr_exc <{if t1 then t2 else t3 end}> ->
  term_init_cr_exc t1.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_call : forall t1 t2,
  term_init_cr_exc <{call t1 t2}> ->
  term_init_cr_exc t1 /\ term_init_cr_exc t2.
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
  term_init_cr_exc t1.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_cr : forall ad t,
  term_init_cr_exc <{cr ad t}> ->
  term_init_cr_exc t.
Proof. solve_inv_tice. Qed.

Local Lemma inv_tice_wait : forall t,
  term_init_cr_exc <{wait t}> ->
  term_init_cr_exc t.
Proof. solve_inv_tice. Qed.

Ltac invc_tice :=
  match goal with
  | H : term_init_cr_exc <{unit        }> |- _ => clear H
  | H : term_init_cr_exc <{nat _       }> |- _ => clear H
  | H : term_init_cr_exc <{_ + _       }> |- _ => eapply inv_tice_plus  in H
  | H : term_init_cr_exc <{_ - _       }> |- _ => eapply inv_tice_monus in H
  | H : term_init_cr_exc <{_; _        }> |- _ => eapply inv_tice_seq   in H
  | H : term_init_cr_exc (tm_if _ _ _  )  |- _ => eapply inv_tice_if    in H
  | H : term_init_cr_exc (tm_while _ _ )  |- _ => clear H
  | H : term_init_cr_exc <{var _       }> |- _ => clear H
  | H : term_init_cr_exc <{fn _ _ _    }> |- _ => clear H
  | H : term_init_cr_exc <{call _ _    }> |- _ => eapply inv_tice_call  in H
  | H : term_init_cr_exc <{& _ : _     }> |- _ => clear H
  | H : term_init_cr_exc <{new _ : _   }> |- _ => clear H
  | H : term_init_cr_exc <{init _ _ : _}> |- _ => eapply inv_tice_init  in H
  | H : term_init_cr_exc <{* _         }> |- _ => eapply inv_tice_load  in H
  | H : term_init_cr_exc <{_ := _      }> |- _ => eapply inv_tice_asg   in H
  | H : term_init_cr_exc <{acq _ _ _   }> |- _ => eapply inv_tice_acq   in H
  | H : term_init_cr_exc <{cr _ _      }> |- _ => eapply inv_tice_cr    in H
  | H : term_init_cr_exc <{spawn _     }> |- _ => clear H
  end;
  repeat match goal with
  | H : term_init_cr_exc _ /\ term_init_cr_exc _ |- _ => destruct H
  end.

(* theorems ---------------------------------------------------------------- *)

Theorem tice_from_ice : forall m ths,
  forall_threads ths (valid_term m) ->
  unique_initializers m ths ->
  mutual_exclusion m ths ->
  (* --- *)
  init_cr_exclusivity ths ->
  forall_threads ths term_init_cr_exc.
Proof.
  intros * ? Hui Hmu Hice tid ad. specialize (Hice ad tid tid) as [? ?];
  repeat split; eauto;
  eauto 6 using noinit_or_oneinit_from_ui, nocr_or_onecr_from_mu.
Qed.

Theorem nocr_from_acq : forall m ths tid t ad' t',
  forall_memory  m   value          ->
  forall_memory  m   (valid_term m) ->
  term_init_cr_exc ths[tid]         ->
  term_init_cr_exc t                ->
  (* --- *)
  m[ad'].t = Some t'                ->
  ths[tid] --[e_acq ad' t']--> t    ->
  no_cr ad' ths[tid].
Proof.
  intros * ? ? Htice1 Htice2 **.
  specialize (Htice1 ad') as [_ [[Hnocr1 | Honecr1] _]]; trivial.
  specialize (Htice2 ad') as [_ [[Hnocr2 | Honecr2] _]];
  exfalso; eauto using nocrs_from_value, nocr_acq_contradiction,
    onecr_to_onecr_contradiction.
Qed.

Theorem initialized_from_wacq : forall m ths tid t ad',
  forall_threads ths (valid_term m)             ->
  forall_threads ths (consistent_waits WR_none) ->
  unique_initializers m ths                     ->
  mutual_exclusion m ths                        ->
  init_cr_exclusivity ths                       ->
  (* --- *)
  ths[tid] --[e_wacq ad']--> t ->
  exists t', m[ad'].t = Some t'.
Proof.
  intros * ? ? Hui ? Hice **.
  assert (Had' : ad' < #m) by eauto using vtm_wacq_address.
  assert (one_cr ad' ths[tid]) by eauto using onecr_from_wacq.
  destruct (Hui ad' Had') as [Hsome Hnone].
  opt_dec (m[ad'].t); spec.
  - specialize (Hnone) as [tid' [? _]].
    specialize (Hice ad' tid tid') as [_ ?].
    exfalso. eauto using noinit_oneinit_contradiction.
  - destruct (m[ad'].t); auto; eauto.
Qed.

