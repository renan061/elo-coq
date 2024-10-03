From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import WellTypedTerm.
From Elo Require Import ValidAddresses.
From Elo Require Import ValidReferences.

Local Lemma safe_preserves_inclusion : forall Gamma1 Gamma2,
  Gamma1 includes Gamma2 ->
  (safe Gamma1) includes (safe Gamma2).
Proof.
  unfold inclusion, safe. intros * H *.
  destruct (Gamma1 k) eqn:E1; destruct (Gamma2 k) eqn:E2;
  solve [ intros F; inv F
        | eapply H in E2; rewrite E1 in E2; inv E2; trivial
        ].
Qed.

Local Lemma update_safe_includes_safe_update : forall Gamma k T,
  (safe Gamma)[k <== T] includes (safe Gamma[k <== T]).
Proof.
  intros ? ? ? k' ? H. unfold safe in H. 
  destruct (str_eq_dec k k'); subst.
  - rewrite lookup_update_eq in *. destruct T; inv H; trivial.
  - rewrite lookup_update_neq in *; trivial.
Qed.

Local Lemma context_weakening : forall Gamma1 Gamma2 t T,
  Gamma2 |-- t is T ->
  Gamma1 includes Gamma2 ->
  Gamma1  |-- t is T.
Proof.
  intros. generalize dependent Gamma1.
  ind_typeof; intros; eauto using type_of,
                                  safe_preserves_inclusion,
                                  MapInclusion.update_inclusion.
Qed.

Local Corollary context_weakening_empty : forall Gamma t T,
  empty |-- t is T ->
  Gamma |-- t is T.
Proof.
  intros. eapply (context_weakening _ empty); trivial. discriminate.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Local Lemma typeof_subst : forall t tx T Tx Gamma x,
  Gamma[x <== Tx] |-- t is T ->
  empty |-- tx is Tx ->
  Gamma |-- <{[x := tx] t}> is T.
Proof.
  intros ?. induction t; intros * Htype ?; invc_typeof; eauto using type_of;
  eauto using update_safe_includes_safe_update, context_weakening, type_of;
  eauto using context_weakening_empty, type_of;
  simpl; destruct str_eq_dec; subst;
  eauto using MapInclusion.update_overwrite, context_weakening, type_of;
  eauto using MapInclusion.update_permutation, context_weakening, type_of;
  match goal with | H : _[_ <== _] _ = _ |- _ => rename H into Hty end.
  - rewrite lookup_update_eq in Hty.
    invc Hty. eauto using context_weakening_empty.
  - rewrite lookup_update_neq in Hty; eauto using type_of.
Qed.

Local Lemma typeof_preservation_mstep : forall m1 m2 t1 t2 e T,
  valid_references m1 t1 ->
  (* --- *)
  empty |-- t1 is T ->
  m1 / t1 ==[e]==> m2 / t2 ->
  empty |-- t2 is T.
Proof.
  intros. invc_mstep;
  generalize dependent T; ind_tstep; intros;
  invc_vr; invc_typeof; eauto using type_of;
  repeat invc_typeof; repeat invc_vr; eauto using typeof_subst, type_of.
Qed.

Local Lemma typeof_preservation_mem_mstep : forall m1 m2 t1 t2 e ad T,
  well_typed_term t1 ->
  valid_references m1 t1 ->
  (* --- *)
  ad < #m1 ->
  empty |-- m1[ad].t is T ->
  m1 / t1 ==[e]==> m2 / t2 ->
  empty |-- m2[ad].t is T.
Proof.
  intros * [T1 ?] **. invc_mstep; sigma; trivial; omicron; trivial.
  generalize dependent T1. ind_tstep; intros; invc_typeof; invc_vr; eauto.
  invc_typeof. invc_vr. apply_deterministic_typing. eauto.
Qed.

Lemma typeof_preservation_spawn : forall t1 t2 tid t T,
  empty |-- t1 is T ->
  t1 --[e_spawn tid t]--> t2 ->
  empty |-- t2 is T.
Proof.
  intros. remember empty as Gamma. generalize dependent T.
  ind_tstep; intros; inv_typeof; eauto using type_of.
Qed.

Lemma typeof_preservation_spawned : forall t1 t2 tid t T1,
  empty |-- t1 is T1 ->
  t1 --[e_spawn tid t]--> t2 ->
  exists T, empty |-- t is T.
Proof.
  intros. generalize dependent T1.
  ind_tstep; intros; inv_typeof; eauto.
Qed.

Definition thread_types (ths : threads) (tys: list ty) :=
  #ths = #tys /\ forall i, empty |-- ths[i] is (tys[i] or `Unit`).

Theorem type_preservation : forall m1 m2 ths1 ths2 tys tid e,
  forall_threads ths1 (valid_references m1) ->
  (* --- *)
  thread_types ths1 tys ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  (thread_types ths2 tys \/ exists T, thread_types ths2 (tys +++ T)).
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

(* ------------------------------------------------------------------------- *)

Local Ltac destruct_IH :=
  repeat auto_specialize;
  match goal with
  | H : safe empty = empty -> _ |- _ =>
    specialize (H empty_eq_safe_empty); destruct_IH
  | IH : value ?t
    \/   (exists _ _ _, _ / ?t ==[_]==> _/ _)
    \/   (exists _ _ _, ?t --[e_spawn _ _]--> _)
    |-   _ =>
    destruct IH as [? | [[? [? [? ?]]] | [? [? [? ?]]]]]
  end.

Local Ltac solve_progress :=
  try solve [left; repeat eexists; eauto using value, tstep, mstep];
  match goal with
  | Hval : value ?t1, _ : _ |-- ?t1 is `?T --> _`, _ : _ |-- ?t2 is ?T |- _ =>
    invc Hval; invc_typeof
  | Hval : value ?t1, _ : _ |-- ?t1 is `Safe ?T`, _ : _ |-- ?t2 is ?T |- _ =>
    invc Hval; invc_typeof
  | Hval : value ?t, _ : _ |-- ?t is _ |- _ =>
    invc Hval; invc_typeof; repeat invc_vad; repeat invc_vr
  | Hmstep : _ / _ ==[?e]==> ?m2 / _ |- _ =>
    left; exists e, m2; eexists; invc_mstep; eauto using value, tstep, mstep
  | Htstep : _ --[e_spawn _ _]--> _ |- _ =>
    right; repeat eexists; eauto using value, tstep
  end.

Theorem basic_progress : forall m1 t1,
  valid_addresses m1 t1 ->
  valid_references m1 t1 ->
  (* --- *)
  well_typed_term t1 ->
  (value t1
    \/ (exists e m2 t2, m1 / t1 ==[e]==> m2 / t2)
    \/ (exists tid t t2, t1 --[e_spawn tid t]--> t2)).
Proof.
  intros * ? ? [T ?]. remember empty as Gamma.
  ind_typeof; try invc_vad; try invc_vr; eauto using value; right;
  try solve [subst; discriminate];
  try solve [destruct_IH; repeat solve_progress];
  try solve [
    destruct_IH; try solve [repeat solve_progress];
    destruct_IH; repeat solve_progress
  ].
  - destruct_IH.
    + destruct_IH; repeat solve_progress.
      repeat invc_vad. repeat invc_vr.
      left. repeat eexists.
      eapply ms_acq; eauto using tstep.
      admit.
    + repeat solve_progress.
    + repeat solve_progress.
  - destruct_IH.
    + left. repeat eexists.
      eapply ms_rel; eauto using tstep.
      admit.
    + repeat solve_progress.
    + repeat solve_progress.
  - destruct_IH.
    + right. eauto using tstep.
    + right. eauto using tstep.
    + repeat solve_progress.
Abort.

(* ------------------------------------------------------------------------- *)

Lemma forall_array_inversion {A} {default} : forall (P : A -> Prop) x xs,
  forall_array default P (x :: xs) ->
  P x /\ forall_array default P xs.
Proof.
  intros * H. unfold forall_array in *.
  specialize (H 0) as H'. split; trivial.
  intros i. specialize (H (S i)). trivial.
Qed.

(*
Corollary forall_threads_inversion : forall (P : tm -> Prop) x xs,
  forall_threads (x :: xs) P ->
  P x /\ forall_threads xs P.
Proof. eauto using forall_array_inversion. Qed.

Ltac inv_forall_array H :=
  eapply forall_array_inversion in H as [? ?].

Ltac inv_forall_threads H :=
  eapply forall_threads_inversion in H as [? ?].

Lemma forall_array_cons {A} {default} : forall (P : A -> Prop) x xs,
  P x ->
  forall_array default P xs ->
  forall_array default P (x :: xs).
Proof.
  unfold forall_array in *. intros. destruct i; eauto.
Qed.

Lemma forall_threads_cons : forall (P : tm -> Prop) x xs,
  P x ->
  forall_threads xs P ->
  forall_threads (x :: xs) P.
Proof.
  unfold forall_threads. eauto using forall_array_cons.
Qed.

Lemma cstep_cons : forall m m' ths ths' t tid e,
  m / ths ~~[tid, e]~~> m' / ths' ->
  m / (t :: ths) ~~[S tid, e]~~> m' / (t :: ths').
Proof.
  intros. inv_cstep;
  (eapply (CS_Spawn _ t') || eapply (CS_Mem _ _ t'));
  trivial; simpl; lia.
Qed.

Theorem progress : forall m ths,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (consistently_typed_references m) ->
  (* -- *)
  forall_threads ths well_typed_term ->
  (forall_threads ths value
    \/ (exists  m' ths' tid e, m / ths ~~[tid, e]~~> m' / ths')).
Proof.
  intros * Hvad Hctr Hwtt. induction ths as [ | t ths IHths].
  - left. intros [| ?]; eauto using value.
  - inv_forall_threads Hctr.
    destruct IHths as [? | Hcstep]; eauto.
    + inv_forall_threads Hvad. assumption.
    + inv_forall_threads Hwtt. assumption.
    + assert (value t \/ ~ value t) as [? | ?] by eauto using value_dec.
      * left. eauto using forall_threads_cons.
      * right.
        assert (value t
          \/ (exists e m' t', m / t ==[e]==> m' / t')
          \/ (exists block t', t --[EF_Spawn block]--> t'))
          as [? | [[? [? [? ?]]] | [? [? ?]]]]. {
            inv_forall_threads Hvad.
            inv_forall_threads Hwtt.
            eauto using basic_progress.
          }
        ** contradiction.
        ** do 2 eexists. exists 0. eexists.
           eapply CS_Mem; eauto using mstep. simpl. lia.
        ** do 2 eexists. exists 0. eexists.
           eapply CS_Spawn; eauto using tstep. simpl. lia.
    + right. destruct Hcstep as [? [? [? [? ?]]]]. do 4 eexists.
      eauto using cstep_cons.
Qed.
*)

(* ------------------------------------------------------------------------- *)
(* preservation mem                                                          *)
(* ------------------------------------------------------------------------- *)

(*
Lemma wtt_cstep_mem_preservation : forall m m' ths ths' tid e,
  forall_threads ths well_typed_term ->
  (* --- *)
  forall_memory m well_typed_term ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_memory m' well_typed_term.
Proof.
  intros. invc_cstep; trivial. invc_mstep; trivial; intros ?.
  - omicron; eauto; simpl;
    eauto using wtt_tstep_alloc_value, type_of with wtt.
  - omicron; eauto. simpl.
    eauto using wtt_tstep_write_value.
Qed.
*)

(* ------------------------------------------------------------------------- *)
(* soundness                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
Local Lemma wtt_to_tys : forall ths,
  forall_threads ths well_typed_term ->
  exists tys, thread_types ths tys.
Proof.
  intros * H. induction ths.
  - exists nil. split; trivial.
    intros i. simpl. destruct i; eauto using type_of.
  - inv_forall_threads H. destruct H as [T ?].
    destruct IHths as [TT [? ?]]; trivial.
    exists (T :: TT). split; simpl; try lia. intros i. destruct i; trivial.
Qed.
*)

Corollary wtt_cstep_preservation : forall m m' ths ths' tid e,
  forall_threads ths (valid_references m) ->
  (* --- *)
  forall_threads ths well_typed_term ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_threads ths' well_typed_term.
Proof.
  intros * Hctr Hwtt Hcstep.
  eapply wtt_to_TT in Hwtt as [TT Htt].
  assert (thread_types ths' TT \/ exists T, thread_types ths' (TT +++ T))
    as [[? ?] | [? [? ?]]] by eauto using type_preservation;
  eexists; eauto.
Qed.

Lemma wtt_preservation : forall m m' ths ths' tid e,
  forall_program m ths (consistently_typed_references m) ->
  (* --- *)
  forall_program m ths well_typed_term ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_program m' ths' well_typed_term.
Proof.
  intros * [_ ?] [? ?].
  eauto using wtt_cstep_mem_preservation, wtt_cstep_preservation.
Qed.

Corollary type_soundness : forall m m' ths ths' tid e,
  forall_program m ths well_typed_term ->
  forall_program m ths (valid_addresses m) ->
  forall_program m ths (consistently_typed_references m) ->
  (* --- *)
  m / ths ~~[tid, e]~~> m' / ths' ->
  (forall_threads ths' value \/
    exists m'' ths'' tid' e',
    m' / ths' ~~[tid', e']~~> m'' / ths'').
Proof.
  intros. destruct_forall_program.
  eauto using progress, wtt_cstep_preservation,
    vad_cstep_preservation,
    ctr_cstep_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Local Theorem typing_preservation : forall m m' ths ths' tid e,
  forall_program m ths (valid_addresses m) ->
  (* --- *)
  forall_program m ths well_typed_term ->
  forall_program m ths (consistently_typed_references m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_program m' ths' well_typed_term /\
  forall_program m' ths' (consistently_typed_references m').
Proof.
  intros * ? [? ?] [? ?]. split;
  eauto using wtt_cstep_mem_preservation, wtt_cstep_preservation.
  eauto 6 using ctr_preservation.
Qed.

