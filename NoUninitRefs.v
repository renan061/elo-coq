From Elo Require Import Core.

From Elo Require Import ValidAddresses.
From Elo Require Import NoRef.

(* ------------------------------------------------------------------------- *)
(* no-uninitialized-references                                               *)
(* ------------------------------------------------------------------------- *)

Definition no_uninitialized_references (m : mem) (ths : threads) :=
  forall ad, m[ad].t = None -> forall_program m ths (no_ref ad).

(* theorems ---------------------------------------------------------------- *)

Theorem write_then_initialized : forall m ths tid t ad te,
  no_uninitialized_references m ths ->
  (* --- *)
  ths[tid] --[e_write ad te]--> t ->
  m[ad].t <> None.
Proof.
  intros * Hnur ? Had. specialize (Hnur ad Had) as [? ?].
  eauto using noref_write_contradiction.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac simpl_nur :=
  intros ** ? ?;
  try match goal with _ : forall_threads _ (valid_addresses ?m) |- _ =>
    match goal with
    | _ : _ --[e_insert ?ad _ _]--> _ |- _ => assert (ad < #m)
    | _ : _ --[e_write  ?ad _  ]--> _ |- _ => assert (ad < #m)
    end;
    eauto using vad_insert_address, vad_write_address
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

Lemma nur_preservation_alloc : forall m ths tid t T,
  no_uninitialized_references m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  no_uninitialized_references (m +++ (None, T, false)) ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_alloc.
Qed.

Lemma nur_preservation_insert : forall m ths tid t ad' t' T',
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  no_uninitialized_references m ths ->
  ths[tid] --[e_insert ad' t' T']--> t ->
  no_uninitialized_references m[ad'.t <- t'] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_insert_term, noref_preservation_insert.
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
  forall_threads ths (valid_addresses m) ->
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

Lemma nur_preservation_spawn : forall m ths tid t t',
  no_uninitialized_references m ths ->
  ths[tid] --[e_spawn (#ths) t']--> t ->
  no_uninitialized_references m (ths[tid <- t] +++ t').
Proof.
  simpl_nur. eauto using noref_preservation_spawn, noref_preservation_spawned.
Qed.

Theorem nur_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_addresses m1) ->
  (* --- *)
  no_uninitialized_references m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  no_uninitialized_references m2 ths2.
Proof.
  intros * [_ ?] **. invc_cstep; try invc_mstep.
  - eauto using nur_preservation_none.
  - eauto using nur_preservation_alloc.
  - eauto using nur_preservation_insert.
  - eauto using nur_preservation_read.
  - eauto using nur_preservation_write.
  - eauto using nur_preservation_acq.
  - eauto using nur_preservation_rel.
  - eauto using nur_preservation_spawn.
Qed.

