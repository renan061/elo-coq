From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.

From Elo Require Export Array.
From Elo Require Export Multimap.
From Elo Require Export Core.
From Elo Require Export Properties.

Reserved Notation "m / ths / mvis / trc '~~>' m' / ths' / mvis' / trc'"
  (at level 40, ths at next level, mvis at next level, trc at next level,
                m' at next level, ths' at next level, mvis' at next level).

(* memory visibility *)
(* maps a memory address to the threads that can access it *)
Definition memvis := multimap nat nat.
Definition trace := list ceffect.

Definition memvis_empty : memvis := multimap_empty eqb.

Definition memvis_update mvis ceff :=
  match ceff with
  | CEF_None  tid => mvis
  | CEF_Alloc tid addr => multimap_update mvis addr tid
  | CEF_Load  tid addr => mvis
  | CEF_Store tid addr => mvis
  | CEF_Spawn tid => mvis (* TODO *)
  end.

(* trace step (from one concurrent state to another) *)
Inductive tstep : mem -> threads -> memvis -> trace ->
                  mem -> threads -> memvis -> trace -> Prop :=
  | trace_refl : forall m ths mvis trc,
    m / ths / mvis / trc ~~> m / ths / mvis / trc

  | trace_step : forall m0 m m' ths0 ths ths' mvis0 mvis trc0 trc ceff,
    m0 / ths0 / mvis0 / trc0 ~~> m / ths / mvis / trc ->
    m / ths ==> m' / ths' # ceff ->
    m / ths / mvis / trc ~~> m' / ths' / (memvis_update mvis ceff) / (ceff :: trc)

  where "m / ths / mvis / trc '~~>' m' / ths' / mvis' / trc'" :=
    (tstep m ths mvis trc m' ths' mvis' trc').

Definition safe_memory_address mt addr :=
  safe_type (get_typ mt addr).

Definition safe_load mt (mvis : memvis) tid addr :=
  multimap_lookup mvis addr = (tid :: nil) \/
  safe_memory_address mt addr.

Definition safe_store (mvis : memvis) tid addr :=
  multimap_lookup mvis addr = tid :: nil.

Inductive well_formed_trace : mem_typ -> memvis -> trace -> Prop :=
  | well_formed_trace_nil : forall mt, (* TODO: is this mt correct? *)
    well_formed_trace mt memvis_empty nil

  | well_formed_trace_none : forall mt mvis trc tid,
    well_formed_trace mt mvis trc ->
    well_formed_trace mt mvis (CEF_None tid :: trc)

  | well_formed_trace_alloc : forall mt mt' T mvis mvis' trc tid addr,
    mt' = add mt T ->
    mvis' = multimap_update mvis addr tid ->
    well_formed_trace mt mvis trc ->
    well_formed_trace mt' mvis' (CEF_Alloc tid addr :: trc)

  | well_formed_trace_load : forall mt mvis trc tid addr,
    safe_load mt mvis tid addr ->
    well_formed_trace mt mvis trc ->
    well_formed_trace mt mvis (CEF_Load tid addr :: trc)

  | well_formed_trace_store : forall mt mvis trc tid addr,
    safe_store mvis tid addr ->
    well_formed_trace mt mvis trc ->
    well_formed_trace mt mvis (CEF_Store tid addr :: trc)

  | well_formed_trace_spawn : forall mt mvis trc tid,
    well_formed_trace mt mvis trc ->
    well_formed_trace mt mvis (CEF_Spawn tid :: trc) (* TODO: different mvis *)
  .

(* TODO: move *)
Theorem cstep_none_preservation : forall mt m ths ths' tid,
  well_typed_program mt m ths ->
  m / ths ==> m / ths' # (CEF_None tid) ->
  well_typed_program mt m ths'.
Proof.
  intros * [Hmem Hths] Hcstep.
  inversion Hcstep; subst. split; trivial.
  intros tid'. destruct (tid =? tid') eqn:E.
  + apply Nat.eqb_eq in E. subst.
    rewrite (get_i_set_i TM_Nil); trivial.
    specialize (Hths tid') as [? ?]. eexists.
    eauto using limited_preservation.
  + apply Nat.eqb_neq in E. apply not_eq_sym in E.
    rewrite (get_i_set_j TM_Nil); trivial.
Qed.

Theorem trace_preservation : forall mt m m' ths ths' mvis mvis' trc trc',
  well_typed_program mt m ths ->
  well_formed_trace mt mvis trc ->
  m / ths / mvis / trc ~~> m' / ths' / mvis' / trc' ->
  exists mt' mvis',
    mt' extends mt /\
    well_formed_trace mt' mvis' trc'.
Proof.
  intros * Hwt Htrace Htstep. inversion Htstep; subst.
  - eexists. eexists. split; eauto using extends_refl.
  - unfold memvis_update in *. destruct ceff.
    + inversion H0; subst. eauto.
      assert (well_typed_program mt m' (set ths i t)) as [? Hwt'].
      eauto using cstep_none_preservation.
      eexists. eexists. split; eauto using extends_refl, well_formed_trace.
    + eexists. eexists. split; eauto using extends_add.
      eapply well_formed_trace_alloc; eauto.
    + eexists. eexists. split; eauto using extends_refl.
      eapply well_formed_trace_load; eauto.
      (* TODO *)
Admitted.


(*
Lemma well_typed_cmultistep : forall m m' ths ths' mvis trc,
  m / ths ==>* m' / ths' # mvis # trc ->
  exists mt, well_typed_program mt m' ths'.
Proof.
  intros * Hcmultistep. induction Hcmultistep;
  try solve [
    match goal with
    | IH : exists mt, _ |- _ =>
      specialize IH as [mt ?]
    end;
    assert (exists mt',
      mt' extends mt /\
      well_typed_program mt' m' ths') as [? [_ ?]];
    eauto using preservation
  ].
  exists nil. split.
  - split; trivial. destruct i; eauto using @typeof.
  - intros i. unfold get_tm. simpl.
    repeat (destruct i; eauto using @typeof).
Qed.
*)

(*
Lemma aux : forall mt m0 m m' ths0 ths ths' mvis trc tid addr,
  m0 / ths0 ==>* m / ths # mvis # trc ->
  well_typed_memory mt m ->
  mt |== trc ->
  m / ths ==> m' / ths' # CEF_Load tid addr ->
  exists mt',
    well_typed_memory mt' m' /\
    mt' |== (CEF_Load tid addr :: trc).
Proof.
  intros * Hcmultistep Hmem Htrace Hcstep.
  eexists mt. split.
  - inversion Hcstep. subst. assumption.
  - eapply well_formed_trace_load; eauto.
    unfold safe_load.
Admitted.

Theorem traces_are_well_formed : forall m ths mvis trace,
  m / ths ==>* mvis / trace ->
  |== trace.
Proof.
  intros * Hcsteps. induction Hcsteps; eauto using well_formed_trace.
  - eapply well_formed_trace_load; eauto.
  - eapply well_formed_trace_store; eauto.
Admitted.
*)

(* FOR LATER *)

(*
Lemma well_typed_cmultistep : forall m m' ths ths' mvis trc,
  m / ths ==>* m' / ths' # mvis # trc ->
  exists mt, well_typed_program mt m' ths'.
Proof.
  intros * Hcmultistep. induction Hcmultistep;
  try solve [
    match goal with
    | IH : exists mt, _ |- _ =>
      specialize IH as [mt ?]
    end;
    assert (exists mt',
      mt' extends mt /\
      well_typed_program mt' m' ths') as [? [_ ?]];
    eauto using preservation
  ].
  exists nil. split.
  - split; trivial. destruct i; eauto using @typeof.
  - intros i. unfold get_tm. simpl.
    repeat (destruct i; eauto using @typeof).
Qed.
*)
