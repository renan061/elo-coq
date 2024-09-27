From Elo Require Import Core.
From Elo Require Import Properties.

From Elo Require Import SimpleLemmas.

(* simpl forall-threads *)
Ltac simplfths := 
  match goal with
  | |- forall_threads _[_ <- _] _          => intros tid'; Array.sgs
  | |- forall_threads (_[_ <- _] +++ _) _  => intros tid'; Array.sgas
  end.

Ltac destruct_forall_program :=
  progress (repeat (
    match goal with H : forall_program _ _ _ |- _ => destruct H end
  )).

Ltac split_preservation := 
  intros;
  match goal with
  (* vad | ctr | ss *)
  | H : forall_program ?m1 ?ths1 (?P ?m1),
    _ : ?m1 / ?ths1 ~~[_, _]~~> ?m2 / ?ths2
     |- forall_program ?m2 ?ths2 (?P ?m2) =>
    destruct_forall_program;
    invc_cstep; try invc_mstep; trivial; split; try simplfths; trivial
  (* ss *)
  | H : forall_program ?m1 ?ths1 ?P,
    _ : ?m1 / ?ths1 ~~[_, _]~~> ?m2 / ?ths2
     |- forall_program ?m2 ?ths2 ?P =>
    destruct_forall_program;
    invc_cstep; try invc_mstep; split; try simplfths; trivial
  (* nacc | nuacc *)
  | _ : ?ad  < #?m1,
    _ : ?tid < #?ths1,
    H : ~ ?P ?ad ?m1 ?ths1[?tid],
    _ : ?m1 / ?ths1 ~~[?tid', _]~~> ?m2 / ?ths2
     |- ~ ?P ?ad ?m2 ?ths2[?tid]  =>
    invc_cstep; try invc_mstep; try simpl_array; Array.sgs; trivial
  (* sms *)
  | _ : ?P ?m1 ?ths1,
    _ : ?m1 / ?ths1 ~~[_, _]~~> ?m2 / ?ths2
     |- ?P ?m2 ?ths2 =>
    invc_cstep; try invc_mstep
  end.

(* ------------------------------------------------------------------------- *)
(* value                                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem value_preservation : forall m m' ths ths' tid e,
  forall_memory m value ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_memory m' value.
Proof.
  assert (forall t t' ad te T, t --[e_alloc ad te T]--> t' -> value te)
    by (intros; ind_tstep; eauto using value). 
  assert (forall t t' ad te T, t --[e_write ad te T]--> t' -> value te)
    by (intros; ind_tstep; eauto). 
  intros. inv_cstep; trivial. inv_mstep; trivial;
  (eapply forall_array_add || eapply forall_array_set); eauto using value.
Qed.

(* ------------------------------------------------------------------------- *)
(* valid-addresses                                                           *)
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
  induction t; try inv_vad; eauto using valid_addresses.
  eapply vad_ref. rewrite add_increments_length. eauto.
Qed.

Lemma vad_mem_set : forall m t ad tT,
  valid_addresses m t ->
  valid_addresses m[ad <- tT] t.
Proof.
  intros.
  induction t; try inv_vad; eauto using valid_addresses.
  eapply vad_ref. rewrite set_preserves_length. assumption.
Qed.

Local Lemma vad_ptm : forall m otid1 otid2 ad t T,
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
  ind_tstep; inv_vad; eauto using vad_mem_add, valid_addresses;
  eapply vad_ref; rewrite add_increments_length; eauto.
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
  intros ad'. Array.sgs; eauto using vad_mem_set, vad_ptm, valid_addresses.
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
  ind_tstep; inv_vad; eauto using vad_mem_set, valid_addresses.
  repeat invc_vad. eauto using vad_subst, vad_mem_set, vad_ptm, valid_addresses.
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
  intros ?. Array.sgs; eauto using vad_mem_set, vad_ptm, valid_addresses.
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
  intros. split_preservation.
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

(* ------------------------------------------------------------------------- *)
(* consistently-typed-references                                             *)
(* ------------------------------------------------------------------------- *)

Lemma ctr_subst : forall m t tx x,
  consistently_typed_references m tx ->
  consistently_typed_references m t ->
  consistently_typed_references m <{[x := tx] t}>.
Proof.
  intros.
  induction t; try inv_ctr; eauto using consistently_typed_references;
  simpl; destruct str_eq_dec; eauto using consistently_typed_references.
Qed.

Lemma ctr_mem_add : forall m t tT,
  valid_addresses m t ->
  (* --- *)
  consistently_typed_references m t ->
  consistently_typed_references (m +++ tT) t.
Proof.
  intros.
  induction t; eauto using consistently_typed_references;
  inv_vad; inv_ctr; eauto using consistently_typed_references;
  (eapply ctr_refR || eapply ctr_refX || eapply ctr_refW);
  simpl_array; assumption.
Qed.

Lemma ctr_mem_setX : forall m t te ad T,
  ad < #m ->
  empty |-- te is T ->
  m[ad].ty = `x&T` ->
  (* --- *)
  consistently_typed_references m t ->
  consistently_typed_references m[ad <- (te, `x&T`)] t.
Proof.
  intros.
  induction t; eauto using consistently_typed_references;
  invc_ctr; eauto using consistently_typed_references;
  (eapply ctr_refR || eapply ctr_refX || eapply ctr_refW);
  Array.sgs; trivial;
  match goal with H1 : _[?ad1].ty = _, H2 : _[?ad2].ty = _ |- _ =>
    rewrite H1 in H2; inv H2
  end;
  trivial.
Qed.

Lemma ctr_mem_setW : forall m t te ad T,
  ad < #m ->
  empty |-- te is T ->
  m[ad].ty = `w&T` ->
  (* --- *)
  consistently_typed_references m t ->
  consistently_typed_references m[ad <- (te, `w&T`)] t.
Proof.
  intros.
  induction t; eauto using consistently_typed_references;
  invc_ctr; eauto using consistently_typed_references;
  (eapply ctr_refR || eapply ctr_refX || eapply ctr_refW);
  Array.sgs; trivial;
  match goal with H1 : _[?ad1].ty = _, H2 : _[?ad2].ty = _ |- _ =>
    rewrite H1 in H2; inv H2
  end;
  trivial.
Qed.

Local Lemma ctr_ptm : forall m otid1 otid2 ad t T,
  ad < #m ->
  empty |-- t is T ->
  m[ad].ty = `x&T` ->
  (* --- *)
  forall_memory m (consistently_typed_references m) ->
  m[ad].tm = <{ptm otid1 t}> ->
  consistently_typed_references m[ad <- (<{ptm otid2 t}>, `x&T`)] t.
Proof.
  intros * ? ? ? H Hptm.
  specialize (H ad). simpl in H.
  rewrite Hptm in H. invc_ctr.
  eauto using type_of, ctr_mem_setX.
Qed.

(* none -------------------------------------------------------------------- *)

Lemma ctr_preservation_none : forall m t1 t2,
  consistently_typed_references m t1 ->
  t1 --[e_none]--> t2 ->
  consistently_typed_references m t2.
Proof.
  intros.
  ind_tstep; inv_ctr; eauto using consistently_typed_references.
  inv_ctr. eauto using ctr_subst.
Qed.

(* alloc ------------------------------------------------------------------- *)

Lemma ctr_preservation_mem_alloc : forall m t1 t2 t T,
  well_typed_term t1 ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t1 ->
  consistently_typed_references m t1 ->
  (* --- *)
  forall_memory m (consistently_typed_references m) ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  forall_memory (m +++ (t, T)) (consistently_typed_references (m +++ (t, T))).
Proof.
  intros ** ad.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
  eauto using ctr_mem_add, consistently_typed_references; (* optimization *)
  eauto using ctr_mem_add, ctr_tstep_alloc_term.
Qed.

Lemma ctr_preservation_alloc : forall m t1 t2 t T,
  well_typed_term t1 ->
  valid_addresses m t1 ->
  (* --- *)
  consistently_typed_references m t1 ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  consistently_typed_references (m +++ (t, T)) t2.
Proof.
  intros * [T ?] **. generalize dependent T.
  ind_tstep; intros; inv_ctr; inv_typeof; inv_vad;
  eauto using ctr_mem_add, consistently_typed_references;
  (eapply ctr_refR || eapply ctr_refX || eapply ctr_refW);
  simpl_array; eauto using type_of, empty_eq_safe_empty.
Qed.

Lemma ctr_preservation_unt_alloc : forall m t1 t2 tu ad t T,
  valid_addresses m tu ->
  (* --- *)
  consistently_typed_references m tu ->
  t1 --[e_alloc ad t T]--> t2 ->
  consistently_typed_references (m +++ (t, T)) tu.
Proof.
  intros.
  ind_tstep; eauto using ctr_mem_add, consistently_typed_references.
Qed.

(* read -------------------------------------------------------------------- *)

Lemma ctr_preservation_read : forall m t1 t2 ad,
  consistently_typed_references m m[ad].tm ->
  (* --- *)
  consistently_typed_references m t1 ->
  t1 --[e_read ad m[ad].tm]--> t2 ->
  consistently_typed_references m t2.
Proof.
  intros.
  ind_tstep; inv_ctr; eauto using consistently_typed_references.
Qed.

(* write ------------------------------------------------------------------- *)

Lemma ctr_preservation_mem_write : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  consistently_typed_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (consistently_typed_references m) ->
  t1 --[e_write ad t T]--> t2 ->
  forall_memory m[ad <- (t, T)] (consistently_typed_references m[ad <- (t, T)]).
Proof.
  intros ** ?.
  assert (Hctwe : exists Tm, T = `w&Tm`
    /\ empty |-- t is Tm
    /\ empty |-- m[ad].tm is Tm
    /\ m[ad].ty = `w&Tm`)
    by eauto using consistently_typed_write_effect.
  decompose record Hctwe; subst.
  Array.sgs; eauto using ctr_mem_setW, ctr_tstep_write_term.
Qed.

Lemma ctr_preservation_write : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  (* --- *)
  ad < #m ->
  consistently_typed_references m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  consistently_typed_references (m[ad <- (t, T)]) t2.
Proof.
  intros.
  assert (Hctwe : exists Tm, T = `w&Tm`
    /\ empty |-- t is Tm
    /\ empty |-- m[ad].tm is Tm
    /\ m[ad].ty = `w&Tm`)
    by eauto using consistently_typed_write_effect.
  decompose record Hctwe; subst.
  ind_tstep; intros; inv_wtt; inv_ctr;
  eauto using ctr_mem_setW, consistently_typed_references.
Qed.

Lemma ctr_preservation_unt_write : forall m t1 t2 tu ad t T,
  well_typed_term t1 ->
  consistently_typed_references m t1 ->
  (* --- *)
  ad < #m ->
  consistently_typed_references m tu ->
  t1 --[e_write ad t T]--> t2 ->
  consistently_typed_references m[ad <- (t, T)] tu.
Proof.
  intros.
  assert (Hctwe : exists Tm, T = `w&Tm`
    /\ empty |-- t is Tm
    /\ empty |-- m[ad].tm is Tm
    /\ m[ad].ty = `w&Tm`)
    by eauto using consistently_typed_write_effect.
  decompose record Hctwe; subst.
  eauto using ctr_mem_setW.
Qed.

(* acq --------------------------------------------------------------------- *)

(* TODO *)

(* rel --------------------------------------------------------------------- *)

Lemma ctr_preservation_mem_rel : forall m1 m2 t1 t2 otid1 otid2 t tid ad T,
  well_typed_term t1 ->
  consistently_typed_references m1 t1 ->
  (* --- *)
  ad < #m1 ->
  m1[ad].tm = <{ptm otid1 t}> ->
  m2 = m1[ad <- (<{ptm otid2 t}>, `x&T`)] ->
  (* --- *)
  forall_memory m1 (consistently_typed_references m1) ->
  t1 --[e_rel tid ad]--> t2 ->
  forall_memory m2 (consistently_typed_references m2).
Proof.
  intros. subst.
  assert (Hctwe : exists Tm, T = `w&Tm`
    /\ empty |-- t is Tm
    /\ empty |-- m[ad].tm is Tm
    /\ m[ad].ty = `w&Tm`)
    by eauto using consistently_typed_write_effect.
  decompose record Hctwe; subst.


  ind_tstep; invc_ctr; eauto. 
  intros ?. Array.sgs.
  - repeat clean. simpl.
    eapply ctr_mem_setX; eauto.
  - admit.
  specialize (Hmvad ad'). simpl in *.
  rewrite Hptm in Hmvad. invc Hmvad.
  eauto using vad_mem_set, valid_addresses.
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

Lemma ctr_preservation_spawn : forall m t1 t2 tid t,
  consistently_typed_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistently_typed_references m t2.
Proof.
  intros. ind_tstep; inv_ctr; eauto using consistently_typed_references.
Qed.

Lemma ctr_preservation_spawned : forall m t1 t2 tid t,
  consistently_typed_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistently_typed_references m t.
Proof.
  intros. ind_tstep; inv_ctr; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem ctr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  forall_program m1 ths1 (valid_addresses m1) ->
  (* --- *)
  forall_program m1 ths1 (consistently_typed_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (consistently_typed_references m2).
Proof.
  split_preservation.
  - eauto using ctr_preservation_none.
  - eauto using ctr_preservation_mem_alloc.
  - eauto using ctr_preservation_alloc.
  - eauto using ctr_preservation_unt_alloc.
  - eauto using ctr_preservation_read.
  - eauto using ctr_preservation_mem_write.
  - eauto using ctr_preservation_write.
  - eauto using ctr_preservation_unt_write.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - eauto using ctr_preservation_spawn.
  - eauto using ctr_preservation_spawned.
  - eauto using consistently_typed_references.
Qed.

(* ------------------------------------------------------------------------- *)

Corollary ctr_cstep_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   well_typed_term ->
  forall_threads ths1 well_typed_term ->
  forall_memory  m1   (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  (* --- *)
  forall_memory m1 (consistently_typed_references m1) ->
  forall_threads ths1 (consistently_typed_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (consistently_typed_references m2).
Proof.
  intros.
  assert (forall_program m2 ths2 (consistently_typed_references m2))
    by (eapply ctr_preservation; eauto).
  destruct_forall_program. assumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* safe-spawns                                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma hasvar_subst : forall x t tx,
  ~ (has_var x t) ->
  ([x := tx] t) = t.
Proof.
  intros * Hnhv **. induction t; simpl; trivial;
  try (destruct string_eq_dec; subst; trivial);
  solve
    [ progress (repeat match goal with H : _ -> _ = _ |- _ => rewrite H end);
      trivial; intros ?; eauto using has_var
    | exfalso; eauto using has_var
    ].
Qed.

Local Lemma hasvar_typing : forall Gamma x t T,
  has_var x t ->
  Gamma x = None ->
  ~ (Gamma |-- t is T).
Proof.
  intros * ? Heq Htype.
  induction_type; inv_hasvar; eauto using ctx_eqv_safe_lookup.
  - rewrite Heq in *. discriminate.
  - rewrite lookup_update_neq in IHHtype; eauto.
Qed.

Local Lemma nomut_safe_value : forall Gamma x t tx T Tx,
  value tx ->
  empty |-- tx is Tx ->
  safe Gamma[x <== Tx] |-- t is T ->
  has_var x t ->
  no_mut v.
Proof.
  intros * Hval **.
  inv Hval; inv_type; eauto using no_mut;
  exfalso; eapply hasvar_typing; eauto;
  unfold safe; rewrite lookup_update_eq; reflexivity.
Qed.

Local Lemma ss_subst : forall Gamma x t v T Tx,
  value v ->
  empty |-- v is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  (* --- *)
  safe_spawns v ->
  safe_spawns t ->
  safe_spawns ([x := v] t).
Proof.
  intros * ? ? ? ? Hss.
  generalize dependent Gamma. generalize dependent T. generalize dependent Tx.
  induction Hss; intros; invc_type;
  simpl; eauto using safe_spawns;
  try solve [destruct string_eq_dec;
             eauto using safe_spawns,
                         ctx_eqv_typing,
                         MapEquivalence.update_permutation].
  eapply ss_spawn. destruct (hasvar_dec x t).
  - eauto using nomut_safe_value, (must_subst (fun _ t => no_mut t) nil).
  - erewrite hasvar_subst; assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ss_preservation_mem_alloc : forall m t t' v T,
  forall_memory m safe_spawns ->
  safe_spawns t ->
  t --[e_Alloc (#m) v T]--> t' ->
  forall_memory (m +++ (v, T)) safe_spawns.
Proof.
  intros. unfold forall_memory.
  eauto using forall_array_add, ss_tstep_alloc_value, safe_spawns.
Qed.

Lemma ss_preservation_mem_write : forall m t t' ad v T,
  forall_memory m safe_spawns ->
  safe_spawns t ->
  t --[e_Write ad v T]--> t' ->
  forall_memory m[ad <- (v, T)] safe_spawns.
Proof.
  intros. unfold forall_memory.
  eauto using forall_array_set, ss_tstep_write_value, safe_spawns.
Qed.

Lemma ss_preservation_spawned : forall t1 t2 t,
  safe_spawns t1 ->
  t1 --[e_Spawn t]--> t2 ->
  safe_spawns t.
Proof.
  intros. induction_tstep; inv_ss; eauto using nomut_then_ss.
Qed.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_ss_preservation :=
  match goal with
  | H1 : forall_threads ?ths well_typed_term,
    H2 : forall_threads ?ths safe_spawns,
    _  : ?ths[?tid] --[_]--> _ 
      |- _ =>
    destruct (H1 tid) as [T' ?]; specialize (H2 tid); generalize dependent T';
    induction_tstep; intros; inv_type; inv_ss; eauto using safe_spawns
  end.

Theorem ss_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  (* --- *)
  forall_program m1 ths1 safe_spawns ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 safe_spawns.
Proof.
  split_preservation.
  - (* spawn     *) solve_ss_preservation.
  - (* spawned   *) eauto using ss_preservation_spawned.
  - (* unit      *) eauto using safe_spawns.
  - (* mem_alloc *) eauto using ss_preservation_mem_alloc.
  - (* alloc     *) solve_ss_preservation.
  - (* read      *) solve_ss_preservation.
  - (* mem_write *) eauto using ss_preservation_mem_write.
  - (* write     *) solve_ss_preservation.
  - (* none      *) solve_ss_preservation.
                    invc_type. invc_ss. eauto using ss_subst.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma nacc_mem_add : forall m t ad tT,
  ~ access (#m) m t ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad (m +++ tT) t.
Proof.
  intros ** Hacc.
  induction Hacc; do 2 inv_nacc; eauto.
  Array.sga; eauto.
Qed.

Lemma nacc_mem_set1 : forall m t ad ad' v T,
  ~ access ad m v ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad m[ad' <- (v, T)] t.
Proof.
  assert (forall m ad ad' v,
    access ad m[ad' <- v] m[ad' <- v][ad'].tm -> ad' < #m). {
      intros * H. decompose sum (lt_eq_lt_dec ad' (#m)); subst; trivial;
      simpl_array; simpl in *; inv_acc.
  }
  (* main proof *)
  intros ** Hacc. 
  induction Hacc; eauto using access.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  destruct (nat_eq_dec ad' ad''); subst;
  try (assert (ad'' < #m) by eauto);
  simpl_array; eauto using access.
Qed.

Lemma nacc_mem_set2 : forall m t ad ad' v T,
  ~ access ad' m t ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad m[ad' <- (v, T)] t.
Proof.
  intros ** Hacc.
  induction Hacc; do 2 inv_nacc; eauto using access.
  simpl_array. eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_none : forall m t1 t2 ad,
  ~ access ad m t1 ->
  t1 --[e_None]--> t2 ->
  ~ access ad m t2.
Proof.
  intros.
  induction_tstep; inv_nacc; eauto with acc.
  inv_nacc. eauto using (may_subst (access ad)).
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_alloc : forall m t1 t2 ad v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t1 ->
  (* --- *)
  ad < #m ->
  ~ access ad m t1 ->
  t1 --[e_Alloc (#m) v T]--> t2 ->
  ~ access ad (m +++ (v, T)) t2.
Proof.
  intros.
  induction_tstep; inv_vad; inv_nacc;
  eauto using nacc_mem_add, nacc_vad_length with acc.
  eapply nacc_ref; try lia. simpl_array.
  eauto using nacc_mem_add, nacc_vad_length.
Qed.

Lemma nacc_preservation_unt_alloc : forall m t1 t2 t ad ad' v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  ~ access ad m t ->
  t1 --[e_Alloc ad' v T]--> t2 ->
  ~ access ad (m +++ (v, T)) t.
Proof.
  eauto using nacc_mem_add, nacc_vad_length.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_read : forall m t1 t2 ad ad',
  ~ access ad m t1 ->
  t1 --[e_Read ad' m[ad'].tm]--> t2 ->
  ~ access ad m t2.
Proof.
  intros. induction_tstep; inv_nacc; eauto with acc. inv_nacc. assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_write : forall m t1 t2 ad ad' v T,
  ~ access ad m t1 ->
  t1 --[e_Write ad' v T]--> t2 ->
  ~ access ad (m[ad' <- (v, T)]) t2.
Proof.
  intros.
  assert (~ access ad m v) by eauto using nacc_tstep_write_value;
  induction_tstep; inv_nacc; eauto using nacc_mem_set1 with acc.
Qed.

Lemma nacc_preservation_unt_write : forall m t1 t2 t ad ad' v T,
  well_typed_term t1 ->
  (access ad' m t -> ~ unsafe_access ad' m t1) ->
  (* --- *)
  ~ access ad m t ->
  t1 --[e_Write ad' v T]--> t2 ->
  ~ access ad m[ad' <- (v, T)] t.
Proof.
  intros * ? Hsms **.
  eapply nacc_mem_set2; eauto.
  assert (unsafe_access ad' m t1) by eauto using tstep_write_requires_uacc.
  intros ?. eapply Hsms; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nacc_preservation_spawn : forall m t1 t2 t ad,
  ~ access ad m t1 ->
  t1 --[e_Spawn t]--> t2 ->
  ~ access ad m t2.
Proof.
  intros ** ?. induction_tstep; try inv_nacc; inv_acc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem nacc_preservation : forall m1 m2 ths1 ths2 ad tid tid' e,
  forall_memory m1 (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 well_typed_term ->
  safe_memory_sharing m1 ths1 ->
  (* --- *)
  ad < #m1 ->
  tid < #ths1 ->
  ~ access ad m1 ths1[tid] ->
  m1 / ths1 ~~[tid', e]~~> m2 / ths2 ->
  ~ access ad m2 ths2[tid].
Proof.
  split_preservation.
  - eauto using nacc_preservation_spawn.
  - eauto using nacc_preservation_alloc.
  - eauto using nacc_preservation_unt_alloc.
  - eauto using nacc_preservation_read.
  - eauto using nacc_preservation_write.
  - eauto using nacc_preservation_unt_write.
  - eauto using nacc_preservation_none.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-unsafe-access                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma nuacc_mem_add : forall m t ad tT,
  ~ unsafe_access (#m) m t ->
  (* --- *)
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad (m +++ tT) t.
Proof.
  intros ** Huacc.
  induction Huacc; inv_nuacc; eauto using unsafe_access.
  Array.sga; eauto using unsafe_access; inv_nuacc; eauto.
  simpl in *. inv_uacc.
Qed.

Lemma nuacc_mem_set1 : forall m t ad ad' v T,
  ~ unsafe_access ad m v ->
  (* --- *)
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m[ad' <- (v, T)] t.
Proof.
  assert (H : forall m m' ad ad',
    unsafe_access ad m m'[ad'].tm -> ad' < #m'). {
      intros * H. decompose sum (lt_eq_lt_dec ad' (#m')); subst; trivial;
      simpl_array; simpl in *; inv_uacc.
  }
  (* main proof *)
  intros ** Huacc.
  induction Huacc; eauto using unsafe_access.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  eapply H in Huacc. rewrite set_preserves_length in Huacc.
  Array.sgs; eauto using unsafe_access.
Qed.

Lemma nuacc_mem_set2 : forall m t ad ad' tT,
  ~ unsafe_access ad' m t ->
  (* --- *)
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m[ad' <- tT] t.
Proof.
  intros ** Huacc.
  induction Huacc; inv_nuacc; inv_nuacc; eauto.
  match goal with _ : _ <> ?ad |- _ => destruct (nat_eq_dec ad' ad); subst end;
  simpl_array; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_none : forall m t1 t2 ad,
  ~ unsafe_access ad m t1 ->
  t1 --[e_None]--> t2 ->
  ~ unsafe_access ad m t2.
Proof.
  intros ** Huacc.
  induction_tstep; inv_nuacc; try inv_uacc; eauto.
  inv_nuacc. contradict Huacc. eauto using (may_subst (unsafe_access ad)).
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_alloc : forall m t1 t2 ad v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t1 ->
  (* --- *)
  ad < #m ->
  ~ unsafe_access ad m t1 ->
  t1 --[e_Alloc (#m) v T]--> t2 ->
  ~ unsafe_access ad (m +++ (v, T)) t2.
Proof.
  intros ** ?.
  induction_tstep; inv_vad; inv_nuacc; invc_uacc; eauto;
  match goal with F : unsafe_access _ (_ +++ _) _ |- _ => contradict F end;
  try simpl_array; eauto using nacc_vad_length, nacc_then_nuacc, nuacc_mem_add.
Qed.

Lemma nuacc_preservation_unt_alloc : forall m t1 t2 t ad ad' v T,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  (* --- *)
  ~ unsafe_access ad m t ->
  t1 --[e_Alloc ad' v T]--> t2 ->
  ~ unsafe_access ad (m +++ (v, T)) t.
Proof.
  eauto using nuacc_mem_add, nuacc_vad_length.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_read : forall m t1 t2 ad ad',
  forall_memory m value ->
  well_typed_term t1 ->
  consistently_typed_references m t1 ->
  (* --- *)
  ~ unsafe_access ad m t1 ->
  t1 --[e_Read ad' m[ad'].tm]--> t2 ->
  ~ unsafe_access ad m t2.
Proof.
  intros ** ?.
  induction_tstep; intros;
  inv_wtt; inv_ctr; inv_nuacc; try invc_uacc; eauto;
  inv_wtt; destruct (nat_eq_dec ad' ad); subst; eauto using unsafe_access;
  inv_ctr;
  match goal with F : unsafe_access _ _ _[_].tm |- _ => contradict F end;
  eauto using nuacc_from_immutable_type.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_write : forall m t1 t2 ad ad' v T,
  ~ unsafe_access ad m t1 ->
  t1 --[e_Write ad' v T]--> t2 ->
  ~ unsafe_access ad m[ad' <- (v, T)] t2.
Proof.
  assert (forall m t t' ad ad' v T,
    ~ unsafe_access ad m t ->
    t --[e_Write ad' v T]--> t' ->
    ~ unsafe_access ad m v)
    by (intros; induction_tstep; eauto using unsafe_access).
  (* main proof *)
  intros ** ?. induction_tstep; inv_nuacc; invc_uacc; eauto;
  match goal with _ : unsafe_access _ _ ?t |- _ => rename t into tx end;
  eapply (nuacc_mem_set1 _ tx _ _ v); eauto.
Qed.

Lemma nuacc_preservation_unt_write : forall m t1 t2 t ad ad' v T,
  well_typed_term t1 ->
  (access ad' m t -> ~ unsafe_access ad' m t1) ->
  (* --- *)
  ~ unsafe_access ad m t ->
  t1 --[e_Write ad' v T]--> t2 ->
  ~ unsafe_access ad m[ad' <- (v, T)] t.
Proof.
  intros * ? Hsms **.
  eapply nuacc_mem_set2; eauto.
  assert (unsafe_access ad' m t1) by eauto using tstep_write_requires_uacc.
  intros ?. eapply Hsms; eauto using uacc_then_acc.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma nuacc_preservation_spawn : forall m t1 t2 t ad,
  ~ unsafe_access ad m t1 ->
  t1 --[e_Spawn t]--> t2 ->
  ~ unsafe_access ad m t2.
Proof.
  intros ** ?. induction_tstep; inv_uacc; eauto; inv_nuacc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem nuacc_preservation : forall m1 m2 ths1 ths2 tid tid' ad e,
  forall_memory m1 value ->
  forall_memory m1 (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistently_typed_references m1) ->
  safe_memory_sharing m1 ths1 ->
  (* --- *)
  ad < #m1 ->
  tid < #ths1 ->
  ~ unsafe_access ad m1 ths1[tid] ->
  m1 / ths1 ~~[tid', e]~~> m2 / ths2 ->
  ~ unsafe_access ad m2 ths2[tid].
Proof.
  split_preservation.
  - eauto using nuacc_preservation_spawn. 
  - eauto using nuacc_preservation_alloc. 
  - eauto using nuacc_preservation_unt_alloc. 
  - eauto using nuacc_preservation_read. 
  - eauto using nuacc_preservation_write. 
  - eauto using nuacc_preservation_unt_write. 
  - eauto using nuacc_preservation_none. 
Qed.

(* unused *)
Local Corollary nuacc_preservation_corollary_from_nacc_preservation :
  forall m1 m2 ths1 ths2 ad tid tid' e,
    forall_memory m1 value ->
    forall_memory m1 (valid_addresses m1) ->
    forall_memory m1 well_typed_term ->
    forall_memory m1 (consistently_typed_references m1) ->
    forall_threads ths1 (valid_addresses m1) ->
    forall_threads ths1 well_typed_term ->
    forall_threads ths1 (consistently_typed_references m1) ->
    safe_memory_sharing m1 ths1 ->
    (* --- *)
    ad < #m1 ->
    tid < #ths1 ->
    ~ unsafe_access ad m1 ths1[tid] ->
    m1 / ths1 ~~[tid', e]~~> m2 / ths2 ->
    ~ unsafe_access ad m2 ths2[tid].
Proof.
  intros.
  assert (forall_program m2 ths2 (consistently_typed_references m2))
    as [? ?] by (eapply ctr_preservation; eauto).
  destruct (acc_dec ad m1 ths1[tid]).
  - intros ?.
    assert (safe_access ad m1 ths1[tid]) by (split; eauto).
    eapply (ptyp_sacc_uacc_contradiction m1 m2 ths1[tid] ths2[tid]);
    eauto using value_preservation, ptyp_cstep_preservation.
  - eauto using nacc_then_nuacc, nacc_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* safe-memory-sharing                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_write_sms_helper : forall m t ad v ths tid tid' T,
  tid <> tid' ->
  forall_threads ths well_typed_term ->
  safe_memory_sharing m ths ->
  ths[tid] --[e_Write ad v T]--> t ->
  ~ access ad m ths[tid'].
Proof.
  assert (forall m t t' ad v T Te,
    empty |-- t is T ->
    t --[e_Write ad v Te]--> t' ->
    unsafe_access ad m t
  ). {
    intros. generalize dependent T.
    induction_tstep; intros; inv_type; eauto using unsafe_access.
    inv_type. eauto using unsafe_access.
  }
  (* main proof *)
  intros * Hneq Htype Hsms ? Hacc.
  destruct (Htype tid). specialize (Hsms _ _ _ Hneq Hacc); eauto.
Qed.

(* tstep ----------------------------------------------------------------- *)

(* Three cases:
   - needs nuacc-tstep-preservation;
   - needs acc-tstep-inheritance;
   - just safe-memory-sharing.
*)

Local Ltac destruct_sms ths tid tid1 tid2 :=
  assert (Hlt : tid < #ths) by eauto using tstep_length_tid;
  destruct (nat_eq_dec tid tid1), (nat_eq_dec tid tid2); subst;
  try contradiction.

Local Lemma sms_tstep_none_preservation : forall m t ths tid,
  safe_memory_sharing m ths ->
  ths[tid] --[e_None]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros ** tid1 tid2 **. destruct_sms ths tid tid1 tid2; simpl_array;
  eauto using nuacc_preservation_none, acc_tstep_none_inheritance.
Qed.

Local Lemma sms_tstep_alloc_preservation : forall m t v ths tid T,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[e_Alloc (#m) v T]--> t ->
  safe_memory_sharing (m +++ (v, T)) ths[tid <- t].
Proof.
  intros * ? Hvad ** tid1 tid2 ** Huacc.
  assert (forall tid, ~ unsafe_access (#m) m ths[tid])
    by eauto using nuacc_vad_length.
  eapply uacc_then_acc in Huacc as ?. contradict Huacc.
  destruct_sms ths tid tid1 tid2; simpl_array;
  eauto 6 using acc_mem_add_inheritance,
                acc_tstep_alloc_inheritance,
                nuacc_mem_add,
                nuacc_preservation_alloc,
                vad_acc.
Qed.

Local Lemma sms_tstep_read_preservation : forall m t ad ths tid,
  forall_memory m value ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[e_Read ad m[ad].tm]--> t ->
  safe_memory_sharing m ths[tid <- t].
Proof.
  intros * ? Hwtt ** tid1 tid2 **. destruct (Hwtt tid1).
  destruct_sms ths tid tid1 tid2; simpl_array;
  eauto using acc_tstep_read_inheritance, nuacc_preservation_read.
Qed.

Local Lemma sms_tstep_write_preservation : forall m ths t tid ad v T,
  forall_threads ths well_typed_term ->
  (* --- *)
  safe_memory_sharing m ths ->
  ths[tid] --[e_Write ad v T]--> t ->
  safe_memory_sharing m[ad <- (v, T)] ths[tid <- t].
Proof.
  intros ** tid1 tid2 ** Huacc.
  eapply uacc_then_acc in Huacc as ?. contradict Huacc.
  destruct_sms ths tid tid1 tid2; simpl_array;
  try assert (~ access ad m ths[tid1]) by eauto using step_write_sms_helper;
  try assert (~ access ad m ths[tid2]) by eauto using step_write_sms_helper;
  eauto 7 using uacc_then_acc,
    nuacc_preservation_write,
    acc_tstep_write_inheritance,
    nuacc_mem_set2,
    alt_acc_mem_set_inheritance.
Qed.

Local Lemma sms_tstep_spawn_preservation : forall m ths t block tid,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  forall_memory m (consistently_typed_references m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (consistently_typed_references m) ->
  forall_threads ths safe_spawns ->
  (* --- *)
  tid < #ths ->
  safe_memory_sharing m ths ->
  ths[tid] --[e_Spawn block]--> t ->
  safe_memory_sharing m (ths[tid <- t] +++ block).
Proof.
  intros ** tid1 tid2 **.
  destruct_sms ths tid tid1 tid2;
  decompose sum (lt_eq_lt_dec tid1 (#ths)); subst;
  decompose sum (lt_eq_lt_dec tid2 (#ths)); subst;
  simpl_array;
  try solve [lia | inv_acc | intros ?; inv_uacc];
  eauto using nuacc_preservation_spawn, acc_tstep_spawn_inheritance;
  assert (~ unsafe_access ad m block) by eauto using spawn_nuacc; eauto;
  assert (consistently_typed_references m block)
    by eauto using (tstep_spawn_block consistently_typed_references);
  eauto using uacc_by_association, ctr_preservation_spawn.
Qed.

Local Corollary sms_mstep_preservation : forall m m' t e ths tid,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  (* --- *)
  safe_memory_sharing m ths ->
  m / ths[tid] ==[e]==> m' / t ->
  safe_memory_sharing m' ths[tid <- t].
Proof.
  intros. inv_mstep;
  eauto using sms_tstep_none_preservation,
              sms_tstep_alloc_preservation,
              sms_tstep_read_preservation,
              sms_tstep_write_preservation.
Qed.

(* safe-memory-sharing preservation -------------------------------------- *)

Theorem sms_preservation : forall m m' ths ths' tid e,
  forall_memory m value ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  forall_program m ths safe_spawns ->
  (* --- *)
  safe_memory_sharing m ths ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  safe_memory_sharing m' ths'.
Proof.
  intros * ? [? ?] [_ ?] [? ?] [_ ?] **. split_preservation;
  eauto using sms_tstep_none_preservation,
              sms_tstep_alloc_preservation,
              sms_tstep_read_preservation,
              sms_tstep_write_preservation,
              sms_tstep_spawn_preservation.
Qed.

