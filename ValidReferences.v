From Elo Require Import Core.

From Elo Require Import ValidAddresses.

(* ------------------------------------------------------------------------- *)
(* valid_references                                                          *)
(* ------------------------------------------------------------------------- *)

Inductive valid_references (m : mem) : tm -> Prop :=
  | vr_unit :
    valid_references m <{unit}> 

  | vr_nat : forall n,
    valid_references m <{nat n}>

  | vr_var : forall x,
    valid_references m <{var x}>

  | vr_fun : forall x Tx t,
    valid_references m t ->
    valid_references m <{fn x Tx t}>

  | vr_call : forall t1 t2,
    valid_references m t1 ->
    valid_references m t2 ->
    valid_references m <{call t1 t2}> 

  | vr_refR : forall T ad,
    m[ad].ty = `r&T` ->
    valid_references m <{&ad : r&T}>

  | vr_refX : forall T ad,
    m[ad].ty = `x&T` ->
    valid_references m <{&ad : x&T}>

  | vr_refW : forall T ad,
    m[ad].ty = `w&T` ->
    valid_references m <{&ad : w&T}>

  | vr_new : forall T t,
    valid_references m t ->
    valid_references m <{new t : T}> 

  | vr_load : forall t,
    valid_references m t ->
    valid_references m <{*t}> 

  | vr_asg : forall t1 t2,
    valid_references m t1 ->
    valid_references m t2 ->
    valid_references m <{t1 := t2}> 

  | vr_acq : forall t1 t2,
    valid_references m t1 ->
    valid_references m t2 ->
    valid_references m <{acq t1 t2}>

  | vr_cr : forall ad t,
    valid_references m t ->
    valid_references m <{cr ad t}>

  | vr_ptm : forall tid t,
    valid_references m t ->
    valid_references m <{ptm tid t}>

  | vr_spawn : forall t,
    valid_references m t ->
    valid_references m <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* tactics                                                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac _vr tt :=
  match goal with
  (* irrelevant for unit, nat, and var *)
  | H : valid_references _ <{fn _ _ _ }> |- _ => tt H
  | H : valid_references _ <{call _ _ }> |- _ => tt H
  | H : valid_references _ <{& _ : _  }> |- _ => tt H
  | H : valid_references _ <{new _ : _}> |- _ => tt H
  | H : valid_references _ <{* _      }> |- _ => tt H
  | H : valid_references _ <{_ := _   }> |- _ => tt H
  | H : valid_references _ <{acq _ _  }> |- _ => tt H
  | H : valid_references _ <{cr _ _   }> |- _ => tt H
  | H : valid_references _ <{ptm _ _  }> |- _ => tt H
  | H : valid_references _ <{spawn _  }> |- _ => tt H
  end.

Ltac inv_vr  := _vr inv.
Ltac invc_vr := _vr invc.

(* ------------------------------------------------------------------------- *)
(* auxiliary lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

Local Lemma vr_tstep_alloc_term : forall m t1 t2 ad t T,
  valid_references m t1 ->
  t1 --[e_alloc ad t T ]--> t2 ->
  valid_references m t.
Proof.
  intros. ind_tstep; inv_vr; eauto using valid_references.
Qed.

Local Lemma vr_tstep_write_term : forall m t1 t2 ad t T,
  valid_references m t1 ->
  t1 --[e_write ad t T ]--> t2 ->
  valid_references m t.
Proof.
  intros. ind_tstep; inv_vr; eauto.
Qed.

(*
Local Lemma vr_write_effect : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  t1 --[e_write ad t T]--> t2 ->
  exists Tm, T = `w&Tm`
          /\ empty |-- t is Tm
          /\ empty |-- m[ad].tm is Tm
          /\ m[ad].ty = `w&Tm`.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  ind_tstep; intros; inv_typeof; inv_vr; eauto.
  inv_typeof. inv_vr. eauto.
Qed.

Local Lemma vr_rel_effect : forall m t1 t2 otid ad,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  t1 --[e_rel otid ad]--> t2 ->
  exists T, empty |-- m[ad].tm is `x&T`
         /\ m[ad].ty = `x&T`.
Proof.
  intros * [T' ?] **. generalize dependent T'.
  ind_tstep; intros; invc_typeof; invc_vr; eauto.
  repeat clean. eexists.
Abort.
*)

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma vr_subst : forall m t tx x,
  valid_references m tx ->
  valid_references m t ->
  valid_references m <{[x := tx] t}>.
Proof.
  intros.
  induction t; try inv_vr; eauto using valid_references;
  simpl; destruct str_eq_dec; eauto using valid_references.
Qed.

Lemma vr_mem_add : forall m t tT,
  valid_addresses m t ->
  (* --- *)
  valid_references m t ->
  valid_references (m +++ tT) t.
Proof.
  intros.
  induction t; eauto using valid_references;
  inv_vad; inv_vr; eauto using valid_references;
  (eapply vr_refR || eapply vr_refX || eapply vr_refW);
  simpl_array; assumption.
Qed.

Lemma vr_mem_setX : forall m t te ad T,
  ad < #m ->
  empty |-- te is T ->
  m[ad].ty = `x&T` ->
  (* --- *)
  valid_references m t ->
  valid_references m[ad <- (te, `x&T`)] t.
Proof.
  intros.
  induction t; eauto using valid_references;
  invc_vr; eauto using valid_references;
  (eapply vr_refR || eapply vr_refX || eapply vr_refW);
  Array.sgs; trivial;
  match goal with H1 : _[?ad1].ty = _, H2 : _[?ad2].ty = _ |- _ =>
    rewrite H1 in H2; inv H2
  end;
  trivial.
Qed.

Lemma vr_mem_setW : forall m t te ad T,
  ad < #m ->
  empty |-- te is T ->
  m[ad].ty = `w&T` ->
  (* --- *)
  valid_references m t ->
  valid_references m[ad <- (te, `w&T`)] t.
Proof.
  intros.
  induction t; eauto using valid_references;
  invc_vr; eauto using valid_references;
  (eapply vr_refR || eapply vr_refX || eapply vr_refW);
  Array.sgs; trivial;
  match goal with H1 : _[?ad1].ty = _, H2 : _[?ad2].ty = _ |- _ =>
    rewrite H1 in H2; inv H2
  end;
  trivial.
Qed.

Local Lemma vr_mem_ptm : forall m otid1 otid2 ad t T,
  ad < #m ->
  empty |-- t is T ->
  m[ad].ty = `x&T` ->
  (* --- *)
  forall_memory m (valid_references m) ->
  m[ad].tm = <{ptm otid1 t}> ->
  valid_references m[ad <- (<{ptm otid2 t}>, `x&T`)] t.
Proof.
  intros * ? ? ? H Hptm.
  specialize (H ad). simpl in H.
  rewrite Hptm in H. invc_vr.
  eauto using type_of, vr_mem_setX.
Qed.

(* none -------------------------------------------------------------------- *)

Lemma vr_preservation_none : forall m t1 t2,
  valid_references m t1 ->
  t1 --[e_none]--> t2 ->
  valid_references m t2.
Proof.
  intros.
  ind_tstep; inv_vr; eauto using valid_references.
  inv_vr. eauto using vr_subst.
Qed.

(* alloc ------------------------------------------------------------------- *)

Lemma vr_preservation_mem_alloc : forall m t1 t2 t T,
  well_typed_term t1 ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t1 ->
  valid_references m t1 ->
  (* --- *)
  forall_memory m (valid_references m) ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  forall_memory (m +++ (t, T)) (valid_references (m +++ (t, T))).
Proof.
  intros ** ad.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
  eauto using vr_mem_add, valid_references; (* optimization *)
  eauto using vr_mem_add, vr_tstep_alloc_term.
Qed.

Lemma vr_preservation_alloc : forall m t1 t2 t T,
  well_typed_term t1 ->
  valid_addresses m t1 ->
  (* --- *)
  valid_references m t1 ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  valid_references (m +++ (t, T)) t2.
Proof.
  intros * [T ?] **. generalize dependent T.
  ind_tstep; intros; inv_vr; inv_typeof; inv_vad;
  eauto using vr_mem_add, valid_references;
  (eapply vr_refR || eapply vr_refX || eapply vr_refW);
  simpl_array; eauto using type_of, empty_eq_safe_empty.
Qed.

Lemma vr_preservation_unt_alloc : forall m t1 t2 tu ad t T,
  valid_addresses m tu ->
  (* --- *)
  valid_references m tu ->
  t1 --[e_alloc ad t T]--> t2 ->
  valid_references (m +++ (t, T)) tu.
Proof.
  intros.
  ind_tstep; eauto using vr_mem_add, valid_references.
Qed.

(* read -------------------------------------------------------------------- *)

Lemma vr_preservation_read : forall m t1 t2 ad,
  valid_references m m[ad].tm ->
  (* --- *)
  valid_references m t1 ->
  t1 --[e_read ad m[ad].tm]--> t2 ->
  valid_references m t2.
Proof.
  intros.
  ind_tstep; inv_vr; eauto using valid_references.
Qed.

(* write ------------------------------------------------------------------- *)

Lemma vr_preservation_mem_write : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (valid_references m) ->
  t1 --[e_write ad t T]--> t2 ->
  forall_memory m[ad <- (t, T)] (valid_references m[ad <- (t, T)]).
Proof.
  intros ** ?.
  assert (Hctwe : exists Tm, T = `w&Tm`
    /\ empty |-- t is Tm
    /\ empty |-- m[ad].tm is Tm
    /\ m[ad].ty = `w&Tm`)
    by eauto using vr_write_effect.
  decompose record Hctwe; subst.
  Array.sgs; eauto using vr_mem_setW, vr_tstep_write_term.
Qed.

Lemma vr_preservation_write : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  (* --- *)
  ad < #m ->
  valid_references m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  valid_references (m[ad <- (t, T)]) t2.
Proof.
  intros.
  assert (Hctwe : exists Tm, T = `w&Tm`
    /\ empty |-- t is Tm
    /\ empty |-- m[ad].tm is Tm
    /\ m[ad].ty = `w&Tm`)
    by eauto using vr_write_effect.
  decompose record Hctwe; subst.
  ind_tstep; intros; invc_wtt; invc_vr;
  eauto using vr_mem_setW, valid_references.
Qed.

Lemma vr_preservation_unt_write : forall m t1 t2 tu ad t T,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  valid_references m tu ->
  t1 --[e_write ad t T]--> t2 ->
  valid_references m[ad <- (t, T)] tu.
Proof.
  intros.
  assert (Hctwe : exists Tm, T = `w&Tm`
    /\ empty |-- t is Tm
    /\ empty |-- m[ad].tm is Tm
    /\ m[ad].ty = `w&Tm`)
    by eauto using vr_write_effect.
  decompose record Hctwe; subst.
  eauto using vr_mem_setW.
Qed.

(* acq --------------------------------------------------------------------- *)

(* TODO *)

(* rel --------------------------------------------------------------------- *)

Lemma vr_preservation_mem_rel : forall m1 m2 t1 t2 otid1 otid2 t tid ad,
  forall_memory m1 well_typed_term ->
  well_typed_term t1 ->
  valid_references m1 t1 ->
  (* --- *)
  ad < #m1 ->
  m1[ad].tm = <{ptm otid1 t}> ->
  m2 = m1[ad <- (<{ptm otid2 t}>, m1[ad].ty)] ->
  (* --- *)
  forall_memory m1 (valid_references m1) ->
  t1 --[e_rel tid ad]--> t2 ->
  forall_memory m2 (valid_references m2).
Proof.
  intros.
  ind_tstep; invc_wtt; invc_vr; eauto.
  intros ?. Array.sgs.
  - repeat clean; simpl.
    eapply vr_ptm.
    eapply vr_mem_setX'; trivial.
    + admit.
    + admit.
    + admit.
  - repeat clean.
  (*
  specialize (Hmvad ad'). simpl in *.
  rewrite Hptm in Hmvad. invc Hmvad.
  eauto using vad_mem_set, valid_addresses.
  *)
Abort.

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

Lemma vr_preservation_spawn : forall m t1 t2 tid t,
  valid_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_references m t2.
Proof.
  intros. ind_tstep; inv_vr; eauto using valid_references.
Qed.

Lemma vr_preservation_spawned : forall m t1 t2 tid t,
  valid_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_references m t.
Proof.
  intros. ind_tstep; inv_vr; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem vr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  forall_program m1 ths1 (valid_addresses m1) ->
  (* --- *)
  forall_program m1 ths1 (valid_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (valid_references m2).
Proof.
  split_preservation.
  - eauto using vr_preservation_none.
  - eauto using vr_preservation_mem_alloc.
  - eauto using vr_preservation_alloc.
  - eauto using vr_preservation_unt_alloc.
  - eauto using vr_preservation_read.
  - eauto using vr_preservation_mem_write.
  - eauto using vr_preservation_write.
  - eauto using vr_preservation_unt_write.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - eauto using vr_preservation_spawn.
  - eauto using vr_preservation_spawned.
  - eauto using valid_references.
Qed.

(* ------------------------------------------------------------------------- *)

Corollary vr_cstep_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   well_typed_term ->
  forall_threads ths1 well_typed_term ->
  forall_memory  m1   (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  (* --- *)
  forall_memory m1 (valid_references m1) ->
  forall_threads ths1 (valid_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (valid_references m2).
Proof.
  intros.
  assert (forall_program m2 ths2 (valid_references m2))
    by (eapply vr_preservation; eauto).
  destruct_forall_program. assumption.
Qed.



