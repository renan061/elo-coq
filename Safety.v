From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.

From Elo Require Export Array.
From Elo Require Export Map.

From Elo Require Export Core.
From Elo Require Export Properties.

Inductive trace : list ceffect -> mem -> list tm -> Prop :=
  | trace_nil : forall main T,
    nil / empty |-- main is T ->
    trace (CEF_None 0 :: nil) nil (main :: nil)

  | trace_cons : forall m m' ths ths' ceff ceffs,
    trace ceffs  m  ths ->
    m / ths ==> m' / ths' # ceff ->
    trace (ceff :: ceffs) m' ths'
  .

(* TODO : tem que ser uma relação indutiva! *)
Fixpoint no_concurrent_write ceffs i addr :=
  match ceffs with
  | nil => True

  | CEF_Store i' addr' :: ceffs =>
    (addr <> addr' \/ i = i') /\ (no_concurrent_write ceffs i addr)

  | _ :: ceffs => no_concurrent_write ceffs i addr
  end.

Inductive well_formed_trace : list ceffect -> Prop :=
  | well_formed_trace_nil :
    well_formed_trace nil

  | well_formed_trace_none : forall i ceffs,
    well_formed_trace ceffs ->
    well_formed_trace (CEF_None i :: ceffs)

  | well_formed_trace_alloc : forall i addr ceffs,
    well_formed_trace ceffs ->
    well_formed_trace (CEF_Alloc i addr :: ceffs)

  | well_formed_trace_load : forall i addr ceffs,
    well_formed_trace ceffs ->
    well_formed_trace (CEF_Load i addr :: ceffs)

  | well_formed_trace_store : forall i addr ceffs,
    well_formed_trace ceffs ->
    no_concurrent_write ceffs i addr ->
    well_formed_trace (CEF_Store i addr :: ceffs)

  | well_formed_trace_spawn : forall i ceffs,
    well_formed_trace ceffs ->
    well_formed_trace (CEF_Spawn i :: ceffs)
  .

Lemma traces_are_well_typed : forall m ths ceffs,
  trace ceffs m ths ->
  exists mt, well_typed_program mt m ths.
Proof.
  intros * Htrace. induction Htrace as [| ? ? ? ? ? ? ? [mt Hprog]].
  - exists nil. split.
    + split; trivial. destruct i; eauto using @typeof.
    + intros i. unfold get_tm. simpl; destruct i;
      try destruct i; eauto using @typeof. 
  - assert (exists mt',
      mt' extends mt /\
      well_typed_program mt' m' ths') as [? [_ ?]];
    eauto using preservation.
Qed.

Theorem traces_are_well_formed : forall ceffs m ths,
  trace ceffs m ths ->
  well_formed_trace ceffs.
Proof.
  intros ?. induction ceffs as [| ceff ceffs IH]; intros * Htrace.
  - inversion Htrace.
  - inversion Htrace; subst;
    try destruct ceff; eauto using well_formed_trace.
    eapply well_formed_trace_store; eauto.
Qed.

















