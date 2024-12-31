From Coq Require Import Lia.
From Coq Require Import Lists.List.

From Elo Require Import Core.
From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentTerm.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

(* TODO: rename *)
Lemma aux_inc1 : forall Gamma k T1 T2,
  (safe Gamma)[k <== T2] includes (safe Gamma[k <== T1])[k <== T2].
Proof.
  intros * k' ? H. unfold safe in H. str_eq_dec k k'.
  - rewrite lookup_update_eq in *. trivial.
  - repeat (rewrite lookup_update_neq in *; trivial).
Qed.

(* TODO: rename *)
Lemma aux_inc2 : forall Gamma k k' T T',
  k <> k' ->
  (safe Gamma)[k' <== T'][k <== T] includes (safe Gamma[k <== T])[k' <== T'].
Proof.
  eauto using update_safe_includes_safe_update,
    MapInc.trans, MapInc.update_inclusion, MapInc.update_permutation.
Qed.

Lemma typeof_subst : forall t tx T Tx Gamma x,
  Gamma[x <== Tx] |-- t is T ->
  empty |-- tx is Tx ->
  Gamma |-- <{[x := tx] t}> is T.
Proof.
  intros ?. induction t; intros * Htype ?; invc_typeof; eauto using type_of;
  simpl; try destruct _str_eq_dec; subst;
  eauto using type_of, context_weakening_empty, context_weakening,
    update_safe_includes_safe_update,
    MapInc.update_overwrite, MapInc.update_permutation;
  try match goal with | H : _[_ <== _] _ = _ |- _ => rename H into Hty end.
  - rewrite lookup_update_eq in Hty.
    invc Hty. eauto using context_weakening_empty.
  - rewrite lookup_update_neq in Hty; eauto using type_of.
  - eauto using aux_inc1, context_weakening, type_of.
  - eauto 6 using aux_inc2, context_weakening, type_of.
Qed.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_typeof_preservation T :=
  intros; gendep T; ind_tstep; intros;
  repeat invc_ctm; repeat invc_typeof;
  try invc_eq; eauto using typeof_subst, type_of.

Lemma typeof_preservation_none : forall T t1 t2,
  empty |-- t1 is T ->
  t1 --[e_none]--> t2 ->
  empty |-- t2 is T.
Proof. solve_typeof_preservation T. Qed.

Lemma typeof_preservation_alloc : forall T t1 t2 ad' T',
  empty |-- t1 is T ->
  t1 --[e_alloc ad' T']--> t2 ->
  empty |-- t2 is T.
Proof. solve_typeof_preservation T. Qed.

Lemma typeof_preservation_insert : forall T t1 t2 ad' t' T',
  empty |-- t1 is T ->
  t1 --[e_insert ad' t' T']--> t2 ->
  empty |-- t2 is T.
Proof. solve_typeof_preservation T. Qed.

Lemma typeof_preservation_read : forall T m t1 t2 ad' t',
  consistent_term m t1 ->
  (* --- *)
  m[ad'].t = Some t' ->
  empty |-- t1 is T ->
  t1 --[e_read ad' t']--> t2 ->
  empty |-- t2 is T.
Proof. solve_typeof_preservation T. Qed.

Lemma typeof_preservation_write : forall T t1 t2 ad' t',
  empty |-- t1 is T ->
  t1 --[e_write ad' t']--> t2 ->
  empty |-- t2 is T.
Proof. solve_typeof_preservation T. Qed.

Lemma typeof_preservation_acq : forall T m t1 t2 ad' t',
  consistent_term m t1 ->
  (* --- *)
  m[ad'].t = Some t' ->
  empty |-- t1 is T ->
  t1 --[e_acq ad' t']--> t2 ->
  empty |-- t2 is T.
Proof. solve_typeof_preservation T. Qed.

Lemma typeof_preservation_rel : forall T t1 t2 ad,
  empty |-- t1 is T ->
  t1 --[e_rel ad]--> t2 ->
  empty |-- t2 is T.
Proof. solve_typeof_preservation T. Qed.

Lemma typeof_preservation_spawn : forall T t1 t2 tid t,
  empty |-- t1 is T ->
  t1 --[e_spawn tid t]--> t2 ->
  empty |-- t2 is T.
Proof. solve_typeof_preservation T. Qed.

Lemma typeof_preservation_spawned : forall t1 t2 tid t T1,
  empty |-- t1 is T1 ->
  t1 --[e_spawn tid t]--> t2 ->
  exists T, empty |-- t is T.
Proof.
  intros. gendep T1. ind_tstep; intros; invc_typeof; eauto.
Qed.

Local Lemma typeof_preservation_mstep : forall m1 m2 t1 t2 e T,
  consistent_term m1 t1 ->
  (* --- *)
  empty |-- t1 is T ->
  m1 / t1 ==[e]==> m2 / t2 ->
  empty |-- t2 is T.
Proof.
  intros. invc_mstep.
  - eauto using typeof_preservation_none.
  - eauto using typeof_preservation_alloc.
  - eauto using typeof_preservation_insert.
  - eauto using typeof_preservation_read.
  - eauto using typeof_preservation_write.
  - eauto using typeof_preservation_acq.
  - eauto using typeof_preservation_rel.
Qed.

Local Lemma typeof_preservation_mem_mstep : forall m1 m2 t1 t2 t1' t2' e ad T,
  well_typed_term t1 ->
  consistent_term m1 t1 ->
  (* --- *)
  m1[ad].t = Some t1' ->
  m2[ad].t = Some t2' ->
  empty |-- t1' is T ->
  m1 / t1 ==[e]==> m2 / t2 ->
  empty |-- t2' is T.
Proof.
  intros * [T' ?] **. rename ad into ad'.
  assert (ad' < #m1) by (lt_eq_gt (#m1) ad'; sigma; upsilon; auto).
  invc_mstep; try invc_eq; trivial;
  sigma; try omicron; repeat invc_eq; trivial; upsilon.
  + assert (m1[ad'].t = None) by eauto using insert_then_uninitialized. invc_eq.
  + gendep T'. gendep t1'. ind_tstep; intros;
    repeat invc_typeof; repeat invc_ctm; repeat invc_ctm; eauto.
    invc_eq. apply_deterministic_typing. assumption.
Qed.

Definition types_of (ths : threads) (Ts: list ty) :=
  #ths = #Ts /\ forall i, empty |-- ths[i] is (Ts[i] or `Unit`).

Notation "'|--' ths 'is' Ts" := (types_of ths Ts) (at level 40).

Theorem typeof_preservation : forall m1 m2 ths1 ths2 Ts tid e,
  forall_threads ths1 (consistent_term m1) ->
  (* --- *)
  |-- ths1 is Ts ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  (|-- ths2 is Ts \/ exists T, |-- ths2 is (Ts +++ T)).
Proof.
  intros * ? [Heq ?] **. inv_cstep.
  - left. split; sigma; trivial.
    intros ?. omicron; eauto using typeof_preservation_mstep.
  - right.
    assert (exists T, empty |-- te is T) as [? ?]
        by eauto using typeof_preservation_spawned.
    eexists. split; sigma; eauto.
    intros ?. omicron;
    repeat match goal with
    | H : #ths1 < _ |- _ => rewrite Heq in H
    | H : _ < #ths1 |- _ => rewrite Heq in H
    | |- context C [ #ths1 ] => rewrite Heq 
    end;
    sigma; eauto using typeof_preservation_spawn, type_of.
Qed.

Lemma forall_array_inversion {A} {d} : forall (P : A -> Prop) x xs,
  forall_array d P (x :: xs) ->
  P x /\ forall_array d P xs.
Proof.
  intros * H. unfold forall_array in *.
  specialize (H 0) as H'. split; trivial.
  intros i. specialize (H (S i)). trivial.
Qed.

Corollary forall_threads_inversion : forall (P : tm -> Prop) th ths,
  forall_threads (th :: ths) P ->
  P th /\ forall_threads ths P.
Proof. eauto using forall_array_inversion. Qed.

Local Ltac invc_forall_threads :=
  match goal with
  | H : forall_threads (_ :: _) _ |- _ =>
    eapply forall_threads_inversion in H as [H ?]
  end. 

Local Lemma wtt_to_typesof : forall ths,
  forall_threads ths well_typed_term ->
  exists Ts, |-- ths is Ts.
Proof.
  intros * H. induction ths.
  - exists nil. split; trivial. destruct i; eauto using type_of.
  - invc_forall_threads. destruct H as [T ?].
    destruct IHths as [Ts [? ?]]; trivial.
    exists (T :: Ts). split; simpl; try lia. destruct i; trivial.
Qed.

Lemma wtt_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 (consistent_term m1) ->
  (* --- *)
  forall_threads ths1 well_typed_term ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 well_typed_term.
Proof.
  intros * ? Hwtt **.
  eapply wtt_to_typesof in Hwtt as [Ts ?].
  assert (|-- ths2 is Ts \/ exists T, |-- ths2 is (Ts +++ T))
    as [[? ?] | [? [? ?]]] by eauto using typeof_preservation;
  intros ?; eexists; eauto.
Qed.

Lemma wtt_preservation_memory : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 well_typed_term ->
  (* --- *)
  forall_memory m1 well_typed_term ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_memory m2 well_typed_term.
Proof.
  intros. invc_cstep; trivial. invc_mstep; trivial;
  intros ? ? ?; upsilon; eauto using wtt_insert_term, wtt_write_term.
Qed.

Theorem wtt_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (consistent_term m1) ->
  (* --- *)
  forall_program m1 ths1 well_typed_term ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 well_typed_term.
Proof.
  intros * [_ ?] [? ?] **. split;
  eauto using wtt_preservation_memory, wtt_preservation_threads.
Qed.

Theorem wtt_preservation_rstep : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (consistent_term m1) ->
  (* --- *)
  forall_program m1 ths1 well_typed_term ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 well_typed_term.
Proof.
  intros. invc_rstep; eauto using wtt_preservation_cstep.
  match goal with _ : _ / _ ~~[_, _]~~> ?m / ?ths |- _ =>
    assert (forall_program m ths well_typed_term) as [Hmwtt Hwtt]
      by eauto using wtt_preservation_cstep
  end.
  invc_cstep. invc_mstep.
  split; intros i; repeat intro; omicron; upsilon; auto;
  specialize (Hmwtt i); specialize (Hwtt i); sigma; auto.
Qed.

Theorem wtt_preservation_base : forall t,
  well_typed_term t ->
  forall_program nil (base t) well_typed_term.
Proof.
  intros. split; eauto using forallmemory_base.
  intros tid. simpl. unfold well_typed_term.
  repeat (destruct tid; eauto using type_of).
Qed.

(* ------------------------------------------------------------------------- *)

Local Ltac invc_value_typeof :=
  match goal with
  | H : value ?t, _ : _ |-- ?t is _ |- _ =>
    invc H; invc_typeof
  end.

Ltac destructIH IH :=
  destruct IH as [?Hval | [?t2' [
    [?m2 [?ad' [?t' ?Hmstep]]] | [[?m2 [?e ?Hmstep]] | [?tid [?t' ?Htstep]]]
  ]]].

Theorem limited_progress : forall m1 t1,
  valid_term      m1 t1 ->
  consistent_term m1 t1 ->
  (* --- *)
  well_typed_term t1 ->
  (value t1 \/ exists t2,
  (exists m2 ad t, m1[ad].X = false -> m1 / t1 ==[e_acq ad t]==> m2 / t2)   \/
  (exists m2 e, (forall ad t, e <> e_acq ad t) -> m1 / t1 ==[e]==> m2 / t2) \/
  (exists tid t, t1 --[e_spawn tid t]--> t2)).
Proof.
  intros * ? ? [T ?]. remember empty as Gamma.
  ind_typeof; invc_vtm; invc_ctm; eauto using value; right; repeat spec.
  - destructIH IHtype_of1.
    + invc_value_typeof. invc_vtm. invc_ctm.
      destructIH IHtype_of2.
      * invc_value_typeof. invc_vtm. invc_ctm.
        eexists. right. left. eauto using tstep, mstep.
      * eexists. left. repeat eexists. intros Hfalse.
        specialize (Hmstep Hfalse). invc_mstep. eauto using value, tstep, mstep.
      * eexists. right. left. repeat eexists. intros He.
        specialize (Hmstep He). invc_mstep; eauto using value, tstep, mstep.
      * eexists. right. right. repeat eexists. eauto using value, tstep.
    + eexists. left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + eexists. right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + eexists. right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of1.
    + invc_value_typeof. invc_vtm. invc_ctm.
      destructIH IHtype_of2.
      * invc_value_typeof. invc_vtm. invc_ctm.
        eexists. right. left. eauto using tstep, mstep.
      * eexists. left. repeat eexists. intros Hfalse.
        specialize (Hmstep Hfalse). invc_mstep. eauto using value, tstep, mstep.
      * eexists. right. left. repeat eexists. intros He.
        specialize (Hmstep He). invc_mstep; eauto using value, tstep, mstep.
      * eexists. right. right. repeat eexists. eauto using value, tstep.
    + eexists. left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + eexists. right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + eexists. right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of1; eexists.
    + right. left. eauto using tstep, mstep.
    + left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of1.
    + invc_value_typeof. invc_vtm. invc_ctm.
      destruct n; eexists; right; left; eauto using tstep, mstep.
    + eexists. left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + eexists. right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + eexists. right. right. repeat eexists. eauto using tstep.
  - eexists. right. left. eauto using tstep, mstep. 
  - rewrite HeqGamma in *. unfold empty, Map.empty' in *. auto.
  - destructIH IHtype_of1.
    + invc_value_typeof. invc_vtm. invc_ctm.
      destructIH IHtype_of2; eexists.
      * right. left. eauto using tstep, mstep.
      * left. repeat eexists. intros Hfalse.
        specialize (Hmstep Hfalse). invc_mstep. eauto using value, tstep, mstep.
      * right. left. repeat eexists. intros He.
        specialize (Hmstep He). invc_mstep; eauto using value, tstep, mstep.
      * right. right. repeat eexists. eauto using value, tstep.
    + eexists. left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + eexists. right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + eexists. right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of; eexists; right; left; eauto using tstep, mstep.
  - destructIH IHtype_of; eexists; right; left; eauto using tstep, mstep.
  - destructIH IHtype_of; eexists; right; left; eauto using tstep, mstep.
  - destructIH IHtype_of; eexists.
    + right. left. eauto using tstep, mstep.
    + left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of; eexists.
    + right. left. eauto using tstep, mstep.
    + left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of; eexists.
    + right. left. eauto using tstep, mstep.
    + left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of.
    + invc_value_typeof. invc_vtm. invc_ctm.
      eexists. right. left. eauto using tstep, mstep.
    + eexists. left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + eexists. right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + eexists. right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of.
    + invc_value_typeof. invc_vtm. invc_ctm.
      eexists. right. left. eauto using tstep, mstep.
    + eexists. left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + eexists. right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + eexists. right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of1.
    + invc_value_typeof. invc_vtm. invc_ctm.
      destructIH IHtype_of2; eexists.
      * right. left. eauto using tstep, mstep.
      * left. repeat eexists. intros Hfalse.
        specialize (Hmstep Hfalse). invc_mstep. eauto using value, tstep, mstep.
      * right. left. repeat eexists. intros He.
        specialize (Hmstep He). invc_mstep; eauto using value, tstep, mstep.
      * right. right. repeat eexists. eauto using value, tstep.
    + eexists. left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + eexists. right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + eexists. right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of1.
    + invc_value_typeof. invc_vtm. invc_ctm.
      eexists. left. eauto using tstep, mstep.
    + eexists. left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + eexists. right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + eexists. right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of; eexists.
    + right. left. eauto using tstep, mstep.
    + left. repeat eexists. intros Hfalse.
      specialize (Hmstep Hfalse). invc_mstep. eauto using tstep, mstep.
    + right. left. repeat eexists. intros He.
      specialize (Hmstep He). invc_mstep; eauto using tstep, mstep.
    + right. right. repeat eexists. eauto using tstep.
  - destructIH IHtype_of; eexists;
    right; right; exists 0; eexists; eauto using tstep.
Qed.

(*
Theorem limited_progress : forall m1 t1,
  valid_term      m1 t1 ->
  consistent_term m1 t1 ->
  (* --- *)
  well_typed_term t1 ->
  (value t1
    \/ (exists m2 t2,        m1 / t1 ==[e_none         ]==> m2 / t2)
    \/ (exists m2 t2 ad T,   m1 / t1 ==[e_alloc ad T   ]==> m2 / t2)
    \/ (exists m2 t2 ad t T, m1 / t1 ==[e_insert ad t T]==> m2 / t2)
    \/ (exists m2 t2 ad t,   m1 / t1 ==[e_read ad t    ]==> m2 / t2)
    \/ (exists m2 t2 ad t,   m1 / t1 ==[e_write ad t   ]==> m2 / t2)
    \/ (exists m2 t2 ad t,   m1[ad].X = false ->
                             m1 / t1 ==[e_acq ad t     ]==> m2 / t2)
    \/ (exists m2 t2 ad,     m1 / t1 ==[e_rel ad       ]==> m2 / t2)
    \/ (exists t2 tid t,     t1 --[e_spawn tid t]--> t2)).
Proof.
  intros * ? ? [T ?]. remember empty as Gamma.
  ind_typeof; eauto using value; right; invc_vtm; invc_ctm;
  try solve [subst; discriminate].
  - repeat spec.
    repeat (destruct_IH; try solve [solve_inductive_progress_case]).
  - repeat spec.
    repeat (destruct_IH; try solve [solve_inductive_progress_case]).
    pick_none.
    invc_value_typeof.
    repeat eexists. eauto using tstep, mstep.
  - pick_alloc. repeat eexists. eauto using tstep, mstep.
  - pick_alloc. repeat eexists. eauto using tstep, mstep.
  - pick_alloc. repeat eexists. eauto using tstep, mstep.
  - repeat spec.
    destruct_IH; try solve [solve_inductive_progress_case].
    pick_insert.
    invc_value_typeof;
    repeat eexists; eauto using tstep, mstep, value.
  - repeat spec.
    destruct_IH; try solve [solve_inductive_progress_case].
    pick_insert.
    invc_value_typeof;
    repeat eexists; eauto using tstep, mstep, value.
  - repeat spec.
    destruct_IH; try solve [solve_inductive_progress_case].
    pick_insert.
    invc_value_typeof;
    repeat eexists; eauto using tstep, mstep, value.
  - repeat spec.
    destruct_IH; try solve [solve_inductive_progress_case].
    pick_read.
    invc_value_typeof. invc_vtm. invc_ctm.
    repeat eexists. eauto using tstep, mstep.
  - repeat spec.
    destruct_IH; try solve [solve_inductive_progress_case].
    pick_read.
    invc_value_typeof. invc_vtm. invc_ctm.
    repeat eexists. eauto using tstep, mstep.
  - repeat spec.
    repeat (destruct_IH; try solve [solve_inductive_progress_case]).
    pick_write.
    invc_value_typeof. invc_vtm. invc_ctm.
    repeat eexists. eauto using tstep, mstep.
  - repeat spec.
    repeat (destruct_IH; try solve [solve_inductive_progress_case]).
    pick_acq.
    invc_value_typeof. invc_vtm. invc_ctm.
    repeat eexists. eauto using tstep, mstep.
  - repeat spec.
    repeat (destruct_IH; try solve [solve_inductive_progress_case]).
    pick_rel.
    repeat eexists. intros. eauto using tstep, mstep.
  - pick_spawn.
    eexists. exists 0. eexists. eauto using tstep.
Qed.
*)

