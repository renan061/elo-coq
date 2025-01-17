From Elo Require Import Core.

From Elo Require Import NoRef.
From Elo Require Import ValidTerm.

(* ------------------------------------------------------------------------- *)
(* no-uninitialized-references                                               *)
(* ------------------------------------------------------------------------- *)

Definition no_uninitialized_references (m : mem) (ths : threads) :=
  forall ad, m[ad].t = None -> forall_program m ths (no_ref ad).

(* theorems ---------------------------------------------------------------- *)

Theorem write_then_initialized : forall m ths tid t ad' t',
  no_uninitialized_references m ths ->
  (* --- *)
  ths[tid] --[e_write ad' t']--> t ->
  m[ad'].t <> None.
Proof.
  intros * Hnur ? Had. specialize (Hnur ad' Had) as [? ?].
  eauto using noref_write_contradiction.
Qed.

Theorem acq_then_initialized : forall m ths tid t ad' t',
  no_uninitialized_references m ths ->
  (* --- *)
  ths[tid] --[e_acq ad' t']--> t ->
  m[ad'].t <> None.
Proof.
  intros * Hnur ? Had. specialize (Hnur ad' Had) as [? ?].
  eauto using noref_acq_contradiction.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma nur_mem_region : forall m ths ad R,
  no_uninitialized_references m ths ->
  no_uninitialized_references m[ad.R <- R] ths.
Proof.
  intros * H. intros ad' ?. specialize (H ad').
  repeat omicron; upsilon; destruct H; trivial;
  split; repeat intro; repeat omicron; upsilon; auto; eauto.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac simpl_nur :=
  intros ** ? ?;
  try match goal with _ : forall_threads _ (valid_term ?m) |- _ =>
    match goal with
    | _ : _ --[e_init  ?ad _]--> _ |- _ => assert (ad < #m)
    | _ : _ --[e_write ?ad _]--> _ |- _ => assert (ad < #m)
    end;
    eauto using vtm_init_address, vtm_write_address
  end;
  upsilon;
  match goal with
  | Hnur : no_uninitialized_references ?m _, Had  : ?m[?ad].t = None |- _ =>
    specialize (Hnur ad Had) as Hnoref; clear Hnur
  end;
  match goal with
  | Hnoref : forall_program _ _ (no_ref _) |- _ =>
    assert (Htemp := Hnoref); specialize Htemp as [Hnoref1 Hnoref2]
  end;
  upsilon.

Lemma nur_preservation_none : forall m ths tid t,
  no_uninitialized_references m ths ->
  ths[tid] --[e_none]--> t ->
  no_uninitialized_references m ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_none.
Qed.

Lemma nur_preservation_alloc : forall m ths tid t T R,
  no_uninitialized_references m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  no_uninitialized_references (m +++ new_cell T R) ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_alloc.
Qed.

Lemma nur_preservation_init : forall m ths tid t ad' t',
  forall_threads ths (valid_term m) ->
  (* --- *)
  no_uninitialized_references m ths ->
  ths[tid] --[e_init ad' t']--> t ->
  no_uninitialized_references m[ad'.t <- t'] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_init_term, noref_preservation_init.
Qed.

Lemma nur_preservation_read : forall m ths tid t ad' t',
  m[ad'].t = Some t' ->
  no_uninitialized_references m ths ->
  ths[tid] --[e_read ad' t']--> t ->
  no_uninitialized_references m ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_read.
Qed.

Lemma nur_preservation_write : forall m ths tid t ad' t',
  forall_threads ths (valid_term m) ->
  (* --- *)
  no_uninitialized_references m ths ->
  ths[tid] --[e_write ad' t']--> t ->
  no_uninitialized_references m[ad'.t <- t'] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_write_term, noref_preservation_write.
Qed.

Lemma nur_preservation_acq : forall m ths tid t ad' t',
  m[ad'].t = Some t' ->
  no_uninitialized_references m ths ->
  ths[tid] --[e_acq ad' t']--> t ->
  no_uninitialized_references m[ad'.X <- true] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_acq.
Qed.

Lemma nur_preservation_rel : forall m ths tid t ad',
  no_uninitialized_references m ths ->
  ths[tid] --[e_rel ad']--> t ->
  no_uninitialized_references m[ad'.X <- false] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_rel.
Qed.

Lemma nur_preservation_wacq : forall m ths tid t ad',
  no_uninitialized_references m ths ->
  ths[tid] --[e_wacq ad']--> t ->
  no_uninitialized_references m[ad'.X <- true] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_wacq.
Qed.

Lemma nur_preservation_wrel : forall m ths tid t ad',
  no_uninitialized_references m ths ->
  ths[tid] --[e_wrel ad']--> t ->
  no_uninitialized_references m[ad'.X <- false] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_wrel.
Qed.

Lemma nur_preservation_spawn : forall m ths tid t t',
  no_uninitialized_references m ths ->
  ths[tid] --[e_spawn t']--> t ->
  no_uninitialized_references m (ths[tid <- t] +++ t').
Proof.
  simpl_nur. eauto using noref_preservation_spawn, noref_preservation_spawned.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem nur_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_term m1) ->
  (* --- *)
  no_uninitialized_references m1 ths1 ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  no_uninitialized_references m2 ths2.
Proof.
  intros * [_ ?] **. invc_cstep; try invc_mstep.
  - eauto using nur_preservation_none.
  - sigma. upsilon. eauto using nur_preservation_alloc.
  - eauto using nur_preservation_init.
  - eauto using nur_preservation_read.
  - eauto using nur_preservation_write.
  - eauto using nur_preservation_acq.
  - eauto using nur_preservation_rel.
  - eauto using nur_preservation_wacq.
  - eauto using nur_preservation_wrel.
  - eauto using nur_preservation_spawn.
Qed.

Theorem nur_preservation_base : forall t,
  no_refs t ->
  (* --- *)
  no_uninitialized_references nil (base t).
Proof.
  unfold base. repeat intro. split; repeat intro; upsilon.
  omicron; auto using no_ref. 
Qed.

