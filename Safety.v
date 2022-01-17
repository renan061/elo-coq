From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.

From Elo Require Export Multimap.
From Elo Require Export Core.
From Elo Require Export Properties.

Reserved Notation "m / ths '==>*' memvis / trace"
  (at level 40, ths at next level, memvis at next level).
Reserved Notation "'|==' trace"
  (at level 40).

Definition trace := list ceffect.
(* memory visibility => maps a memory address to a thread *)
Definition memvis := multimap nat nat.

Inductive trace_cmultistep : mem -> threads -> memvis -> trace -> Prop :=
  | trace_cmultistep_one : forall ths,
    well_typed_program nil nil ths ->
    nil / ths ==>* multimap_empty / (CEF_None 0 :: nil)

  | trace_cmultistep_none : forall i m m' ths ths' mvis trace,
    m  / ths  ==>* mvis / trace ->
    m  / ths  ==>  m' / ths' # (CEF_None i) ->
    m' / ths' ==>* mvis / (CEF_None i :: trace)

  | trace_cmultistep_alloc : forall i addr m m' ths ths' mvis trace,
    m  / ths  ==>* mvis / trace ->
    m  / ths  ==>  m' / ths' # (CEF_Alloc i addr) ->
    m' / ths' ==>* (add mvis i) / (CEF_Alloc i addr :: trace)

  | trace_cmultistep_load : forall i addr m m' ths ths' mvis trace,
    m  / ths  ==>* mvis / trace ->
    m  / ths  ==>  m' / ths' # (CEF_Load i addr) ->
    m' / ths' ==>* mvis / (CEF_Load i addr :: trace)

  | trace_cmultistep_store : forall i addr m m' ths ths' mvis trace,
    m  / ths  ==>* mvis / trace ->
    m  / ths  ==>  m' / ths' # (CEF_Store i addr) ->
    m' / ths' ==>* mvis / (CEF_Store i addr :: trace)
(*
  | trace_cmultistep_spawn : forall i m m' ths ths' mvis trace,
    m  / ths  ==>* mvis / trace ->
    m  / ths  ==>  m' / ths' # (CEF_Spawn i) ->
    m' / ths' ==>* mvis / (CEF_Spawn i :: trace)
*)
  where "m / ths '==>*' mvis / trace" := (trace_cmultistep m ths mvis trace).

Lemma well_typed_trace_cmultistep : forall m ths mvis trace,
  m / ths ==>* mvis / trace ->
  exists mt, well_typed_program mt m ths.
Proof.
  intros * H. induction H;
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
  + split; trivial. destruct i; eauto using @typeof.
  + intros i. specialize H as [_ Hths]. specialize (Hths i). assumption.
Qed.

Fixpoint trace_has_concurrent_load trace i addr :=
  match trace with
  | nil =>
      False
  | CEF_Load j addr :: trace =>
      i <> j \/ (trace_has_concurrent_load trace i addr)
  | _ :: trace =>
      trace_has_concurrent_load trace i addr
  end.

Fixpoint trace_has_concurrent_store trace i addr :=
  match trace with
  | nil =>
      False
  | CEF_Store j addr :: trace =>
      i <> j \/ (trace_has_concurrent_store trace i addr)
  | _ :: trace =>
      trace_has_concurrent_store trace i addr
  end.

Inductive well_formed_trace : trace -> Prop :=
  | well_formed_trace_nil :
    |== nil

  | well_formed_trace_none : forall i trace,
    |== trace ->
    |== (CEF_None i :: trace)

  | well_formed_trace_alloc : forall i addr trace,
    |== trace ->
    |== (CEF_Alloc i addr :: trace)

  | well_formed_trace_load : forall i addr trace,
    ~ (trace_has_concurrent_load trace i addr) ->
    |== trace ->
    |== (CEF_Load i addr :: trace)

  | well_formed_trace_store : forall i addr trace,
    ~ (trace_has_concurrent_load trace i addr) ->
    ~ (trace_has_concurrent_store trace i addr) ->
    |== trace ->
    |== (CEF_Store i addr :: trace)

  | well_formed_trace_spawn : forall i trace,
    |== trace ->
    |== (CEF_Spawn i :: trace)

  where "'|==' trace" := (well_formed_trace trace).

Theorem traces_are_well_formed : forall m ths mvis trace,
  m / ths ==>* mvis / trace ->
  |== trace.
Proof.
Admitted.

(*

  intros ? ? trace. induction trace as [| ceff trace IH]; intros * Hcsteps.
  - inversion Hcsteps.
  - assert (exists mt, well_typed_program mt m ths) as [mt [Hmem Hths]].
    { eauto using well_typed_trace_cmultistep. }
    inversion Hcsteps; subst;
    try destruct ceff; eauto using well_formed_trace.
    + eapply well_formed_trace_load; eauto.
      specialize (Hths i) as [T Htype].
      shelve.
    + eapply well_formed_trace_store; eauto.
      * shelve.
      * shelve.
Admitted.

*)
