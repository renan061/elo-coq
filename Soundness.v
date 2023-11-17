From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Elo Require Import Core.
From Elo Require Import Properties.
From Elo Require Import Preservation.

Local Lemma safe_preserves_inclusion : forall Gamma Gamma',
  Gamma includes Gamma' ->
  (safe Gamma) includes (safe Gamma').
Proof.
  unfold inclusion, safe. intros * H *.
  destruct (Gamma k) eqn:E1; destruct (Gamma' k) eqn:E2;
  solve [ intros F; inversion F
        | eapply H in E2; rewrite E1 in E2; inversion E2; subst; trivial
        ].
Qed.

Local Lemma update_safe_includes_safe_update : forall Gamma k T,
  (safe Gamma)[k <== T] includes (safe Gamma[k <== T]).
Proof.
  intros ? ? ? k' ? H. unfold safe in H. 
  destruct (string_eq_dec k k'); subst.
  - rewrite lookup_update_eq in *. destruct T; inversion H; subst; trivial.
  - rewrite lookup_update_neq in *; trivial.
Qed.

Local Lemma context_weakening : forall Gamma Gamma' t T,
  Gamma' |-- t is T ->
  Gamma includes Gamma' ->
  Gamma  |-- t is T.
Proof.
  intros. generalize dependent Gamma. induction_type; intros;
  eauto using type_of,
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

Local Lemma typeof_subst_preservation : forall t tx T Tx Tx' Gamma x,
  Gamma |-- <{ fn x Tx t }> is <{{ Tx' --> T }}> ->
  empty |-- tx is Tx' ->
  Gamma |-- [x := tx] t is T.
Proof.
  assert (forall t tx T Tx Gamma x,
    Gamma[x <== Tx] |-- t is T ->
    empty |-- tx is Tx ->
    Gamma |-- ([x := tx] t) is T
  ). {
    unfold subst. intros ?. induction t; intros * Htype ?; 
    try (destruct string_eq_dec); try inv_type;
    eauto using type_of, context_weakening, context_weakening_empty,
      MapInclusion.update_overwrite, MapInclusion.update_permutation,
      update_safe_includes_safe_update;
    match goal with
    | H : _[_ <== _] _ = _ |- _ =>
      try (erewrite lookup_update_eq in H || erewrite lookup_update_neq in H);
      inversion H; subst; eauto using context_weakening_empty, type_of
    end.
  }
  intros. inv_type. eauto.
Qed.

Local Lemma typeof_tstep_spawn_preservation : forall t t' block T,
  empty |-- t is T ->
  t --[EF_Spawn block]--> t' ->
  empty |-- t' is T.
Proof.
  intros. remember empty as Gamma. generalize dependent T.
  induction_tstep; intros; inv_type; eauto using type_of.
Qed.

Local Lemma typeof_mstep_preservation : forall m m' t t' e T,
  consistently_typed_references m t ->
  empty |-- t is T ->
  m / t ==[e]==> m' / t' ->
  empty |-- t' is T.
Proof.
  intros.
  invc_mstep; generalize dependent t'; remember empty as Gamma;
  induction_type; intros; inv_tstep; inv_ctr;
  eauto using type_of, typeof_subst_preservation;
  inv_type; inv_ctr; trivial.
Qed.

Local Lemma typeof_mstep_mem_preservation : forall m m' t t' e ad T Tm,
  consistently_typed_references m t ->
  ad < #m ->
  empty |-- t is T ->
  empty |-- m[ad].tm is Tm ->
  m / t ==[e]==> m' / t' ->
  empty |-- m'[ad].tm is Tm.
Proof.
  intros * ? ? Htype ? ?. rename ad into ad'.
  invc_mstep; try simpl_array; trivial.
  decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array; trivial.
  generalize dependent t'. remember empty as Gamma.
  induction Htype; inv HeqGamma; intros;
  try inv_ctr; inv_tstep; eauto.
  inv_type; inv_ctr; apply_deterministic_typing. eauto.
Qed.

Lemma typeof_spawn_block_preservation : forall t t' block T,
  empty |-- t is T ->
  t --[EF_Spawn block]--> t' ->
  exists Tb, empty |-- block is Tb.
Proof.
  intros. remember empty as Gamma. generalize dependent T.
  induction_tstep; intros; inv_type; eauto.
Qed.

Definition thread_types (ths : threads) (TT: list typ) :=
  #ths = #TT /\ forall i, empty |-- ths[i] is (TT[i] or <{{ Unit }}>).

Theorem type_preservation : forall m m' ths ths' tid e TT,
  forall_threads ths (consistently_typed_references m) ->
  thread_types ths TT ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  (thread_types ths' TT \/ exists T, thread_types ths' (TT +++ T)).
Proof.
  intros * ? [? ?]. intros. inv_cstep.
  - right.
    assert (exists T, empty |-- block is T) as [? ?]
        by eauto using typeof_spawn_block_preservation.
    eexists. split.
    + rewrite 2 add_increments_length. rewrite set_preserves_length. eauto.
    + intros i. decompose sum (lt_eq_lt_dec i (#ths)); subst; simpl_array.
      * rewrite set_preserves_length in a0. rewrite H0 in a0.
        decompose sum (lt_eq_lt_dec i tid); subst; simpl_array;
        eauto using typeof_tstep_spawn_preservation.
      * rewrite set_preserves_length. rewrite H0. simpl_array. eauto.
      * rewrite set_preserves_length in b. rewrite H0 in b.
        simpl_array. eauto using type_of.
  - left. split.
    + rewrite set_preserves_length. trivial.
    + intros i. decompose sum (lt_eq_lt_dec i tid); subst; simpl_array;
      eauto using typeof_mstep_preservation.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem basic_progress : forall m t,
  valid_addresses m t ->
  consistently_typed_references m t ->
  (* --- *)
  well_typed_term t ->
  (value t
    \/ (exists e m' t', m / t ==[e]==> m' / t')
    \/ (exists block t', t --[EF_Spawn block]--> t')).
Proof.
  intros * ? ? [T ?]. remember empty as Gamma.
  induction_type; try inv_vad; try inv_ctr;
  try solve [left; eauto using value];
  right;
  try solve
    [ destruct IHtype_of as [? | [[e [? [? ?]]] | [? [? ?]]]];
      eauto using tstep; left;
      try solve [ do 3 eexists; eauto using tstep, mstep
                | exists e; do 2 eexists;
                  destruct e; inv_mstep; eauto using tstep, mstep
                ]
    ].
  - destruct IHtype_of as [Hval | [[e [? [? ?]]] | [? [? ?]]]];
    eauto using tstep.
    + left. destruct t; inv Hval; inv_type. inv_vad.
      eauto using tstep, mstep.
    + left. exists e. exists x. eexists.
      destruct e; inv_mstep; eauto using tstep, mstep.
  - destruct IHtype_of as [Hval | [[e [? [? ?]]] | [? [? ?]]]];
    eauto using tstep.
    + left. destruct t; inv Hval; inv_type. inv_vad.
      eauto using tstep, mstep.
    + left. exists e. exists x. eexists.
      destruct e; inv_mstep; eauto using tstep, mstep.
  - destruct IHtype_of1 as [Hval1 | [[e1 [? [? ?]]] | [? [? ?]]]];
    eauto using tstep.
    + destruct IHtype_of2 as [Hval2 | [[e2 [? [? ?]]] | [? [? ?]]]];
      eauto using tstep.
      * destruct Hval1; inv H1_.
        left. do 3 eexists. inv_vad; eauto using tstep, mstep.
      * left. exists e2. exists x. eexists. 
        destruct e2; inv_mstep; eauto using tstep, mstep.
    + left. exists e1. exists x. eexists. 
      destruct e1; inv_mstep; eauto using tstep, mstep.
  - subst. inv H1.
  - destruct IHtype_of1 as [Hval1 | [[e1 [? [? ?]]] | [? [? ?]]]];
    eauto using tstep.
    + destruct IHtype_of2 as [Hval2 | [[e2 [? [? ?]]] | [? [? ?]]]];
      eauto using tstep.
      * destruct Hval1; inv H1_.
        left. do 3 eexists. inv_vad; eauto using tstep, mstep.
      * left. exists e2. exists x. eexists. 
        destruct e2; inv_mstep; eauto using tstep, mstep.
    + left. exists e1. exists x. eexists. 
      destruct e1; inv_mstep; eauto using tstep, mstep.
  - destruct IHtype_of1 as [Hval1 | [[e1 [? [? ?]]] | [? [? ?]]]];
    eauto using tstep.
    + destruct IHtype_of2 as [Hval2 | [[e2 [? [? ?]]] | [? [? ?]]]];
      eauto using tstep.
      * left. do 3 eexists. eauto using tstep, mstep.
      * left. do 3 eexists. eauto using tstep, mstep.
      * left. do 3 eexists. eauto using tstep, mstep.
    + left. exists e1. exists x. eexists. 
      destruct e1; inv_mstep; eauto using tstep, mstep.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma forall_array_inversion {A} {default} : forall (P : A -> Prop) x xs,
  forall_array default P (x :: xs) ->
  P x /\ forall_array default P xs.
Proof.
  intros * H. unfold forall_array in *.
  specialize (H 0) as H'. split; trivial.
  intros i. specialize (H (S i)). trivial.
Qed.

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

(* ------------------------------------------------------------------------- *)
(* preservation mem                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma wtt_cstep_mem_preservation : forall m m' ths ths' tid e,
  forall_memory m well_typed_term ->
  forall_threads ths well_typed_term ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_memory m' well_typed_term.
Proof.
  intros. invc_cstep; trivial. invc_mstep; trivial; intros ad'.
  - decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; eauto; simpl;
    eauto using wtt_tstep_alloc_value, type_of with wtt.
  - decompose sum (lt_eq_lt_dec ad ad'); subst; simpl_array; eauto. simpl.
    eauto using wtt_tstep_write_value.
Qed.

(* ------------------------------------------------------------------------- *)
(* soundness                                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma wtt_to_TT : forall ths,
  forall_threads ths well_typed_term ->
  exists TT, thread_types ths TT.
Proof.
  intros * H. induction ths.
  - exists nil. split; trivial.
    intros i. simpl. destruct i; eauto using type_of.
  - inv_forall_threads H. destruct H as [T ?].
    destruct IHths as [TT [? ?]]; trivial.
    exists (T :: TT). split; simpl; try lia. intros i. destruct i; trivial.
Qed.

Corollary wtt_cstep_preservation : forall m m' ths ths' tid e,
  forall_threads ths (consistently_typed_references m) ->
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
  forall_memory m (valid_addresses m) ->
  forall_memory m (consistently_typed_references m) ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistently_typed_references m) ->
  (* --- *)
  m / ths ~~[tid, e]~~> m' / ths' ->
  (forall_threads ths' value \/
    exists m'' ths'' tid' e',
    m' / ths' ~~[tid', e']~~> m'' / ths'').
Proof.
  intros * Hmvad Hmctr Hvad Hwtt Hctr Hcstep.
  eauto using progress, wtt_cstep_preservation,
    vad_preservation.vad_cstep_preservation,
    ctr_preservation.ctr_cstep_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Theorem typing_preservation : forall m m' ths ths' tid e,
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
  eauto 6 using ctr_preservation.ctr_preservation.
Qed.

