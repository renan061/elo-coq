From Elo Require Import Core.

From Elo Require Import Preservation_.

(* ------------------------------------------------------------------------- *)
(* valid-addresses                                                           *)
(* ------------------------------------------------------------------------- *)

(* Addresses are valid if they are within the bounds of the memory. *)
Inductive valid_addresses (m : mem) : tm -> Prop :=
  | vad_unit :
    valid_addresses m <{unit}>

  | vad_nat : forall n,
    valid_addresses m <{nat n}>

  | vad_var : forall x,
    valid_addresses m <{var x}>

  | vad_fun : forall x T t,
    valid_addresses m t ->
    valid_addresses m <{fn x T t}>

  | vad_call : forall t1 t2,
    valid_addresses m t1 ->
    valid_addresses m t2 ->
    valid_addresses m <{call t1 t2}>

  | vad_ref : forall ad T,
    ad < #m ->
    valid_addresses m <{&ad : T}>

  | vad_new : forall t T,
    valid_addresses m t ->
    valid_addresses m <{new t : T}>

  | vad_load : forall t,
    valid_addresses m t ->
    valid_addresses m <{*t}>

  | vad_asg : forall t1 t2,
    valid_addresses m t1 ->
    valid_addresses m t2 ->
    valid_addresses m <{t1 := t2}>

  | vad_acq : forall t1 t2,
    valid_addresses m t1 ->
    valid_addresses m t2 ->
    valid_addresses m <{acq t1 t2}>

  | vad_cr : forall ad t,
    ad < #m ->
    valid_addresses m t ->
    valid_addresses m <{cr ad t}>

  | vad_ptm : forall tid t,
    valid_addresses m t ->
    valid_addresses m <{ptm tid t}>

  | vad_spawn : forall t,
    valid_addresses m t ->
    valid_addresses m <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* tactics                                                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac _vad tt :=
  match goal with
  (* irrelevant for unit, nat, and var *)
  | H : valid_addresses _ <{fn _ _ _ }> |- _ => tt H
  | H : valid_addresses _ <{call _ _ }> |- _ => tt H
  | H : valid_addresses _ <{& _ : _  }> |- _ => tt H
  | H : valid_addresses _ <{new _ : _}> |- _ => tt H
  | H : valid_addresses _ <{* _      }> |- _ => tt H
  | H : valid_addresses _ <{_ := _   }> |- _ => tt H
  | H : valid_addresses _ <{acq _ _  }> |- _ => tt H
  | H : valid_addresses _ <{cr _ _   }> |- _ => tt H
  | H : valid_addresses _ <{ptm _ _  }> |- _ => tt H
  | H : valid_addresses _ <{spawn _  }> |- _ => tt H
  end.

Ltac inv_vad  := _vad inv.
Ltac invc_vad := _vad invc.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma vad_subst : forall m t tx x,
  valid_addresses m tx ->
  valid_addresses m t ->
  valid_addresses m <{[x := tx] t}>.
Proof.
  intros.
  induction t; try inv_vad; eauto using valid_addresses;
  simpl; destruct str_eq_dec; eauto using valid_addresses.
Qed.

Lemma vad_mem_add : forall m t tT,
  valid_addresses m t ->
  valid_addresses (m +++ tT) t.
Proof.
  intros.
  induction t; try invc_vad; eauto using valid_addresses.
  - eapply vad_ref. Array.simpl_lengths. eauto.
  - eapply vad_cr; eauto. Array.simpl_lengths. eauto.
Qed.

Lemma vad_mem_set : forall m t ad tT,
  valid_addresses m t ->
  valid_addresses m[ad <- tT] t.
Proof.
  intros.
  induction t; try inv_vad; eauto using valid_addresses.
  - eapply vad_ref. Array.simpl_lengths. eauto.
  - eapply vad_cr; eauto. Array.simpl_lengths. eauto.
Qed.

Lemma vad_mem_ptm : forall m otid1 otid2 ad t T,
  forall_memory m (valid_addresses m) ->
  m[ad].tm = <{ptm otid1 t}> ->
  valid_addresses m[ad <- (<{ptm otid2 t}>, T)] t.
Proof.
  intros * Hmvad Hptm.
  specialize (Hmvad ad). simpl in Hmvad.
  rewrite Hptm in Hmvad. invc_vad. eauto using vad_mem_set.
Qed.

(* none -------------------------------------------------------------------- *)

Lemma vad_preservation_none : forall m t1 t2,
  valid_addresses m t1 ->
  t1 --[e_none]--> t2 ->
  valid_addresses m t2.
Proof.
  intros.
  ind_tstep; inv_vad; eauto using valid_addresses.
  inv_vad. eauto using vad_subst.
Qed.

(* alloc ------------------------------------------------------------------- *)

Lemma vad_preservation_mem_alloc : forall m t1 t2 t T,
  valid_addresses m t1 ->
  (* --- *)
  forall_memory m (valid_addresses m) ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  forall_memory (m +++ (t, T)) (valid_addresses (m +++ (t, T))).
Proof.
  intros.
  ind_tstep; inv_vad; eauto;
  intros ?; Array.sga; eauto using vad_mem_add, valid_addresses.
Qed.

Lemma vad_preservation_alloc : forall m t1 t2 t T,
  valid_addresses m t1 ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  valid_addresses (m +++ (t, T)) t2.
Proof.
  intros.
  ind_tstep; inv_vad; eauto using vad_mem_add, valid_addresses.
  - eapply vad_ref; Array.simpl_lengths; eauto.
  - eapply vad_ref; Array.simpl_lengths; eauto.
  - eapply vad_ref; Array.simpl_lengths; eauto.
  - eapply vad_cr; eauto. Array.simpl_lengths; eauto.
Qed.

Lemma vad_preservation_unt_alloc : forall m t1 t2 t ad te T,
  valid_addresses m t ->
  t1 --[e_alloc ad te T]--> t2 ->
  valid_addresses (m +++ (te, T)) t.
Proof.
  eauto using vad_mem_add.
Qed.

(* read -------------------------------------------------------------------- *)

Lemma vad_preservation_read : forall m t1 t2 ad,
  forall_memory m (valid_addresses m) ->
  (* --- *)
  valid_addresses m t1 ->
  t1 --[e_read ad m[ad].tm]--> t2 ->
  valid_addresses m t2.
Proof.
  intros.
  ind_tstep; inv_vad; eauto using valid_addresses.
Qed.

(* write ------------------------------------------------------------------- *)

Lemma vad_preservation_mem_write : forall m t1 t2 ad te T,
  valid_addresses m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (valid_addresses m) ->
  t1 --[e_write ad te T]--> t2 ->
  forall_memory m[ad <- (te, T)] (valid_addresses m[ad <- (te, T)]).
Proof.
  intros.
  ind_tstep; inv_vad; eauto. 
  intros ad'. Array.sgs; eauto using vad_mem_set.
Qed.

Lemma vad_preservation_write : forall m t1 t2 ad t T,
  valid_addresses m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  valid_addresses (m[ad <- (t, T)]) t2.
Proof.
  intros.
  ind_tstep; inv_vad; eauto using vad_mem_set, valid_addresses.
  eapply vad_cr; eauto. Array.simpl_lengths. trivial.
Qed.

Lemma vad_preservation_unt_write : forall m t1 t2 tu ad t T,
  valid_addresses m tu ->
  t1 --[e_write ad t T]--> t2 ->
  valid_addresses m[ad <- (t, T)] tu.
Proof.
  eauto using vad_mem_set.
Qed.

(* acq --------------------------------------------------------------------- *)

Lemma vad_preservation_mem_acq : forall m1 m2 t1 t2 otid1 otid2 t tid ad T,
  valid_addresses m1 t1 ->
  (* --- *)
  ad < #m1 ->
  m1[ad].tm = <{ptm otid1 t}> ->
  m2 = m1[ad <- (<{ptm otid2 t}>, T)] ->
  (* --- *)
  forall_memory m1 (valid_addresses m1) ->
  t1 --[e_acq tid ad t]--> t2 ->
  forall_memory m2 (valid_addresses m2).
Proof.
  intros.
  ind_tstep; invc_vad; eauto. 
  intros ad'. Array.sgs; eauto using vad_mem_set, vad_mem_ptm, valid_addresses.
Qed.

Lemma vad_preservation_acq : forall m t1 t2 otid1 otid2 t tid ad T,
  forall_memory m (valid_addresses m) ->
  (* --- *)
  ad < #m ->
  m[ad].tm = <{ptm otid1 t}> ->
  (* --- *)
  valid_addresses m t1 ->
  t1 --[e_acq tid ad t]--> t2 ->
  valid_addresses m[ad <- (<{ptm otid2 t}>, T)] t2.
Proof.
  intros.
  ind_tstep; inv_vad; eauto using vad_mem_set, valid_addresses;
  repeat invc_vad; eapply vad_cr;
  eauto using vad_subst, vad_mem_set, vad_mem_ptm;
  Array.simpl_lengths; eauto.
Qed.

Lemma vad_preservation_unt_acq : forall m t1 t2 tu otid1 otid2 t tid ad T,
  forall_memory m (valid_addresses m) ->
  (* --- *)
  ad < #m ->
  m[ad].tm = <{ptm otid1 t}> ->
  (* --- *)
  valid_addresses m tu ->
  t1 --[e_acq tid ad t]--> t2 ->
  valid_addresses m[ad <- (<{ptm otid2 t}>, T)] tu.
Proof.
  eauto using vad_mem_set.
Qed.

(* rel --------------------------------------------------------------------- *)

Lemma vad_preservation_mem_rel : forall m m' t1 t2 otid1 otid2 t tid ad T,
  valid_addresses m t1 ->
  (* --- *)
  ad < #m ->
  m[ad].tm = <{ptm otid1 t}> ->
  m' = m[ad <- (<{ptm otid2 t}>, T)] ->
  (* --- *)
  forall_memory m (valid_addresses m) ->
  t1 --[e_rel tid ad]--> t2 ->
  forall_memory m' (valid_addresses m').
Proof.
  intros. ind_tstep; invc_vad; eauto. 
  intros ?. Array.sgs; eauto using vad_mem_set, vad_mem_ptm, valid_addresses.
Qed.

Lemma vad_preservation_rel : forall m t1 t2 otid1 otid2 t tid ad T,
  forall_memory m (valid_addresses m) ->
  (* --- *)
  ad < #m ->
  m[ad].tm = <{ptm otid1 t}> ->
  (* --- *)
  valid_addresses m t1 ->
  t1 --[e_rel tid ad]--> t2 ->
  valid_addresses m[ad <- (<{ptm otid2 t}>, T)] t2.
Proof.
  intros.
  ind_tstep; inv_vad; eauto using vad_mem_set, valid_addresses.
  eapply vad_cr; eauto. Array.simpl_lengths; trivial.
Qed.

Lemma vad_preservation_unt_rel : forall m t1 t2 tu otid1 otid2 t tid ad T,
  forall_memory m (valid_addresses m) ->
  (* --- *)
  ad < #m ->
  m[ad].tm = <{ptm otid1 t}> ->
  (* --- *)
  valid_addresses m tu ->
  t1 --[e_rel tid ad]--> t2 ->
  valid_addresses m[ad <- (<{ptm otid2 t}>, T)] tu.
Proof.
  eauto using vad_mem_set.
Qed.

(* spawn ------------------------------------------------------------------- *)

Lemma vad_preservation_spawn : forall m t1 t2 tid t,
  valid_addresses m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_addresses m t2.
Proof.
  intros. ind_tstep; inv_vad; eauto using valid_addresses.
Qed.

Lemma vad_preservation_spawned : forall m t1 t2 tid t,
  valid_addresses m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_addresses m t.
Proof.
  intros. ind_tstep; inv_vad; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem vad_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_addresses m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (valid_addresses m2).
Proof.
  split_preservation.
  - eauto using vad_preservation_none.
  - eauto using vad_preservation_mem_alloc.
  - eauto using vad_preservation_alloc.
  - eauto using vad_preservation_unt_alloc.
  - eauto using vad_preservation_read.
  - eauto using vad_preservation_mem_write.
  - eauto using vad_preservation_write.
  - eauto using vad_preservation_unt_write.
  - eauto using vad_preservation_mem_acq.
  - eauto using vad_preservation_acq.
  - eauto using vad_preservation_unt_acq.
  - eauto using vad_preservation_mem_rel.
  - eauto using vad_preservation_rel.
  - eauto using vad_preservation_unt_rel.
  - eauto using vad_preservation_spawn.
  - eauto using vad_preservation_spawned.
  - eauto using valid_addresses.
Qed.

(* ------------------------------------------------------------------------- *)

Corollary vad_cstep_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (valid_addresses m2).
Proof.
  intros.
  assert (forall_program m2 ths2 (valid_addresses m2))
    by eauto using vad_preservation.
  destruct_forall_program. assumption.
Qed.
