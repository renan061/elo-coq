From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import WellTypedTerm.

(* ------------------------------------------------------------------------- *)
(* well-typed-memory                                                         *)
(* ------------------------------------------------------------------------- *)

Reserved Notation " T1 '~>' T2  " (at level 80, no associativity).

Inductive points_to_type : ty -> ty -> Prop :=
  | pt_R : forall T,
    `r&T` ~> `Safe T`

  | pt_X : forall T,
    `x&T` ~> T

  | pt_W : forall T,
    `w&T` ~> T

  where "T1 ~> T2" := (points_to_type T1 T2).

Definition valid_pointer_types (m : mem) :=
  forall ad T, ad < #m -> empty |-- m[ad].tm is T -> m[ad].ty ~> T.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Local Lemma deterministic_R : forall t T1 T2,
  empty |-- t is `Safe T1` ->
  empty |-- t is T2 ->
  `r&T1` ~> T2.
Proof.
  intros.
  assert (`Safe T1` = T2) by eauto using deterministic_typing.
  subst. eauto using points_to_type.
Qed.

Local Lemma deterministic_X : forall t T1 T2,
  empty |-- t is T1 ->
  empty |-- t is T2 ->
  `x&T1` ~> T2.
Proof.
  intros.
  assert (T1 = T2) by eauto using deterministic_typing.
  subst. eauto using points_to_type.
Qed.

Local Lemma deterministic_W : forall t T1 T2,
  empty |-- t is T1 ->
  empty |-- t is T2 ->
  `w&T1` ~> T2.
Proof.
  intros.
  assert (T1 = T2) by eauto using deterministic_typing.
  subst. eauto using points_to_type.
Qed.

Local Lemma vpt_acq_rel : forall m otid ad t T,
  valid_pointer_types m ->
  empty |-- t is T ->
  ad < # m ->
  m[ad].tm = <{ptm otid t}> ->
  m[ad].ty ~> T.
Proof.
  intros * Hvpt ? ? Heq.
  eapply Hvpt; trivial.
  rewrite Heq. eauto using type_of.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma vpt_preservation_alloc : forall m t1 t2 t T,
  well_typed_term t1 ->
  (* --- *)
  valid_pointer_types m ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  valid_pointer_types (m +++ (t, T)).
Proof.
  intros * [T' ?] **. generalize dependent T'.
  ind_tstep; intros; invc_typeof; eauto;
  intros ? ? ? ?; Array.sga; simpl in *; eauto; Array.simpl_lengths; try lia;
  try invc_typeof;
  eauto using deterministic_R, deterministic_X, deterministic_W.
Qed.

Lemma vpt_preservation_write : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  (* --- *)
  valid_pointer_types m ->
  t1 --[e_write ad t T]--> t2 ->
  valid_pointer_types m[ad <- (t, T)].
Proof.
  intros * [T' ?] **. generalize dependent T'.
  ind_tstep; intros; invc_typeof; eauto.
  intros ? ? ? ?. invc_typeof. 
  Array.simpl_lengths. Array.sgs; eauto using deterministic_W.
Qed.

Lemma vpt_preservation_acq : forall m t1 t2 otid1 otid2 tid ad t,
  well_typed_term t1 ->
  (* --- *)
  m[ad].tm = <{ptm otid1 t}> ->
  valid_pointer_types m ->
  t1 --[e_acq tid ad t]--> t2 ->
  valid_pointer_types m[ad <- (<{ptm otid2 t}>, m[ad].ty)].
Proof.
  intros * [T' ?] **. generalize dependent T'.
  ind_tstep; intros; invc_typeof; eauto.
  intros ? ? ? ?. repeat invc_typeof.
  Array.simpl_lengths. Array.sgs; eauto.
  simpl in *. invc_typeof. eauto using vpt_acq_rel.
Qed.

Lemma vpt_preservation_rel : forall m t1 t2 otid1 otid2 tid ad t,
  well_typed_term t1 ->
  (* --- *)
  m[ad].tm = <{ptm otid1 t}> ->
  valid_pointer_types m ->
  t1 --[e_rel tid ad]--> t2 ->
  valid_pointer_types m[ad <- (<{ptm otid2 t}>, m[ad].ty)].
Proof.
  intros * [T' ?] **. generalize dependent T'.
  ind_tstep; intros; invc_typeof; eauto.
  intros ? ? ? ?.
  Array.simpl_lengths. Array.sgs; eauto.
  simpl in *. invc_typeof. eauto using vpt_acq_rel.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem vpt_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  (* --- *)
  valid_pointer_types m1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  valid_pointer_types m2.
Proof.
  intros * Hwtt **. invc Hwtt.
  invc_cstep; try invc_mstep;
  eauto using vpt_preservation_alloc,
              vpt_preservation_write,
              vpt_preservation_acq,
              vpt_preservation_rel.
Qed.

