From Coq Require Logic.ClassicalFacts.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.

(* A term accesses an address if it refers to the address directly or 
indirectly. *)
Inductive access (m : mem) : tm -> addr -> Prop :=
  | access_mem : forall ad ad' T,
    access m m[ad'] ad ->
    access m <{ &ad' :: T }> ad

  | access_ref : forall ad T,
    access m <{ &ad :: T }> ad

  | access_new : forall T t ad,
    access m t ad ->
    access m <{ new T t }> ad

  | access_load : forall t ad,
    access m t ad ->
    access m <{ *t }> ad

  | access_asg1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ t1 = t2 }> ad

  | access_asg2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ t1 = t2 }> ad

  | access_fun : forall x Tx t ad,
    access m t ad ->
    access m <{ fn x Tx --> t }> ad

  | access_call1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ call t1 t2 }> ad

  | access_call2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ call t1 t2 }> ad

  | access_seq1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ t1; t2 }> ad

  | access_seq2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ t1; t2 }> ad
  .

(* strong access_mem *)
Theorem access_get_trans : forall m t ad ad',
  access m t ad' ->
  access m m[ad'] ad ->
  access m t ad.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access.
Qed.

Ltac inversion_access :=
  match goal with
  | H : access _ TM_Unit        _ |- _ => inversion H; clear H
  | H : access _ (TM_Num _)     _ |- _ => inversion H; clear H
  | H : access _ (TM_Ref _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_New _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Load _)    _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Asg _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Id _)      _ |- _ => inversion H; clear H
  | H : access _ (TM_Fun _ _ _) _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Call _ _)  _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Seq _ _)   _ |- _ => inversion H; subst; clear H
  | H : access _ (TM_Spawn _)   _ |- _ => inversion H; clear H
  end.

(* ------------------------------------------------------------------------- *)
(* access-dec                                                                *)
(* ------------------------------------------------------------------------- *)

Local Axiom excluded_middle : ClassicalFacts.excluded_middle.

Lemma access_dec : forall m t ad,
  (access m t ad) \/ (~ access m t ad).
Proof. eauto using excluded_middle. Qed.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Inductive not_access (m : mem) : tm -> addr -> Prop :=
  | not_access_unit : forall ad,
    not_access m <{ unit }> ad

  | not_access_num : forall n ad,
    not_access m <{ N n }> ad

  | not_access_ref : forall T ad ad',
    ad <> ad' ->
    ~ access m m[ad] ad' ->
    not_access m <{ &ad :: T }> ad'

  | not_access_new : forall T t ad,
    ~ access m t ad ->
    not_access m <{ new T t }> ad

  | not_access_load : forall t ad,
    ~ access m t ad ->
    not_access m <{ *t }> ad

  | not_access_asg : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1 = t2 }> ad

  | not_access_id : forall x ad,
    not_access m <{ ID x }> ad

  | not_access_fun : forall x Tx t ad,
    ~ access m t ad ->
    not_access m <{ fn x Tx --> t }> ad

  | not_access_call : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ call t1 t2 }> ad

  | not_access_seq : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1; t2 }> ad

  | not_access_spawn : forall t ad,
    not_access m <{ spawn t }> ad
  .

Theorem not_access_iff : forall m t ad,
  ~ access m t ad <-> not_access m t ad.
Proof.
  intros. split; intros H; destruct t;
  try (eapply not_access_ref
    || eapply not_access_asg
    || eapply not_access_call
    || eapply not_access_seq);
  eauto using access, not_access;
  intros ?; subst;
  try (inversion_access; inversion_clear H);
  eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* valid-accesses                                                            *)
(* ------------------------------------------------------------------------- *)

Definition valid_accesses (m : mem) (t : tm) :=
  forall ad, access m t ad -> ad < length m.

(* ------------------------------------------------------------------------- *)
(* va constructors                                                           *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_constructor_va := 
  intros; intros ? ?; inversion_access; eauto.

Local Lemma va_new: forall m t T,
  valid_accesses m t ->
  valid_accesses m <{ new T t }>.
Proof. solve_constructor_va. Qed.

Local Lemma va_load : forall m t,
  valid_accesses m t ->
  valid_accesses m <{ *t }>.
Proof. solve_constructor_va. Qed.

Local Lemma va_asg : forall m t1 t2,
  valid_accesses m t1 ->
  valid_accesses m t2 ->
  valid_accesses m <{ t1 = t2 }>.
Proof. solve_constructor_va. Qed.

Local Lemma va_fun : forall m x Tx t,
  valid_accesses m t ->
  valid_accesses m <{ fn x Tx --> t }>.
Proof. solve_constructor_va. Qed.

Local Lemma va_call : forall m t1 t2,
  valid_accesses m t1 ->
  valid_accesses m t2 ->
  valid_accesses m <{ call t1 t2 }>.
Proof. solve_constructor_va. Qed.

Local Lemma va_seq : forall m t1 t2,
  valid_accesses m t1 ->
  valid_accesses m t2 ->
  valid_accesses m <{ t1; t2 }>.
Proof. solve_constructor_va. Qed.

(* ------------------------------------------------------------------------- *)
(* inversion-valid-accesses                                                  *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_inversion_va := 
  intros; unfold valid_accesses in *;
  match goal with
  | [ |- _ /\ _ ] => split
  | [ |- _ ] => idtac
  end;
  eauto using access.

Local Lemma inversion_va_ref : forall m ad T,
  valid_accesses m <{ &ad :: T }> ->
  valid_accesses m m[ad].
Proof. solve_inversion_va. Qed.

Local Lemma inversion_va_new : forall m t T,
  valid_accesses m <{ new T t }> ->
  valid_accesses m t.
Proof. solve_inversion_va. Qed.

Local Lemma inversion_va_load : forall m t,
  valid_accesses m <{ *t }> ->
  valid_accesses m t.
Proof. solve_inversion_va. Qed.

Local Lemma inversion_va_asg : forall m t1 t2,
  valid_accesses m <{ t1 = t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_inversion_va. Qed.

Local Lemma inversion_va_fun : forall m x Tx t,
  valid_accesses m <{ fn x Tx --> t }> ->
  valid_accesses m t.
Proof. solve_inversion_va. Qed.

Local Lemma inversion_va_call : forall m t1 t2,
  valid_accesses m <{ call t1 t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_inversion_va. Qed.

Local Lemma inversion_va_seq : forall m t1 t2,
  valid_accesses m <{ t1; t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_inversion_va. Qed.

Ltac inversion_va :=
  match goal with
    | [ H : valid_accesses _ <{ &_ :: _ }>      |- _ ] =>
        eapply inversion_va_ref in H as Hwba'
    | [ H : valid_accesses _ <{ new _ _ }>      |- _ ] =>
        eapply inversion_va_new in H
    | [ H : valid_accesses _ <{ *_ }>           |- _ ] =>
        eapply inversion_va_load in H
    | [ H : valid_accesses _ <{ _ = _ }>        |- _ ] => 
        eapply inversion_va_asg in H as [? ?]
    | [ H : valid_accesses _ <{ fn _ _ --> _ }> |- _ ] => 
        eapply inversion_va_fun in H
    | [ H : valid_accesses _ <{ call _ _ }>     |- _ ] => 
        eapply inversion_va_call in H as [? ?]
    | [ H : valid_accesses _ <{ _; _ }>         |- _ ] => 
        eapply inversion_va_seq in H as [? ?]
  end.

(* ------------------------------------------------------------------------- *)
(* va -- value, mem & subst                                                  *)
(* ------------------------------------------------------------------------- *)

Local Lemma va_alloc_value : forall m t t' ad v,
  valid_accesses m t ->
  t --[EF_Alloc ad v]--> t' ->
  valid_accesses m v.
Proof.
  intros. induction_step; inversion_va; eauto using access.
Qed.

Local Lemma va_write_value : forall m t t' ad v,
  valid_accesses m t ->
  t --[EF_Write ad v]--> t' ->
  valid_accesses m v.
Proof.
  intros. induction_step; inversion_va; eauto using access.
Qed.

Ltac rewrite_array default :=
  match goal with
  (* get_add_eq *)
  | H : context C [ (?l +++ _)[length ?l] ] |- _ =>
    rewrite (get_add_eq default) in H; trivial
  | |-  context C [ (?l +++ _)[length ?l] ] =>
    rewrite (get_add_eq default); trivial
  (* get_add_lt *)
  | H : context C [ (?l +++ _)[?i] ], _ : ?i < length ?l |- _ => 
    rewrite (get_add_lt default) in H; trivial
  | _ : ?i < length ?l |- context C [ (?l +++ _)[?i] ] => 
    rewrite (get_add_lt default); trivial
  (* get_add_gt *)
  | H : context C [ (?l +++ _)[?i] ], _ : length ?l < ?i |- _ => 
    rewrite (get_add_gt default) in H; trivial
  | _ : length ?l < ?i |- context C [ (?l +++ _)[?i] ] => 
    rewrite (get_add_gt default); trivial
  (* get_set_eq *)
  | H : context C [ ?l[?i <- _ ][?i] ] |- _ =>
    rewrite (get_set_eq default) in H; trivial
  | |-  context C [ ?l[?i <- _ ][?i] ] =>
    rewrite (get_set_eq default); trivial
  (* get_set_neq *)
  | H : context C [ ?l[?j <- _][?i] ], _ : ?i <> ?j |- _ => 
    rewrite (get_set_neq default) in H; trivial
  | H : context C [ ?l[?j <- _][?i] ], _ : ?j <> ?i |- _ => 
    rewrite (get_set_neq default) in H; trivial
  | _ : ?i <> ?j |- context C [ ?l[?j <- _][?i] ] => 
    rewrite (get_set_neq default); trivial
  | _ : ?j <> ?i |- context C [ ?l[?j <- _][?i] ] => 
    rewrite (get_set_neq default); trivial
  (* get_set_lt *)
  | H : context C [ ?l[?j <- _][?i] ], _ : ?i < ?j |- _ => 
    rewrite (get_set_lt default) in H; trivial
  | _ : ?i < ?j |- context C [ ?l[?j <- _][?i] ] => 
    rewrite (get_set_lt default); trivial
  (* get_set_gt *)
  | H : context C [ ?l[?j <- _][?i] ], _ : ?j < ?i |- _ => 
    rewrite (get_set_gt default) in H; trivial
  | _ : ?j < ?i |- context C [ ?l[?j <- _][?i] ] => 
    rewrite (get_set_gt default); trivial
  end.

Local Lemma va_added_value : forall m v T,
  valid_accesses (m +++ v) v ->
  valid_accesses (m +++ v) <{ &(length m) :: T }>.
Proof.
  intros * ? ? Hacc.
  remember (add m v) as m'.
  remember (TM_Ref T (length m)) as t'.
  induction Hacc; inversion Heqt'; subst.
  - do 2 (rewrite_array TM_Unit). eauto using access.
  - rewrite add_increments_length. lia.
Qed.

Local Lemma va_mem_add : forall m t v,
  valid_accesses m t ->
  valid_accesses (m +++ v) t.
Proof.
  intros * Hva ? Hacc. induction Hacc; subst; inversion_va; eauto.
  - eapply IHHacc. intros ? ?.
    destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]; subst;
    do 3 (rewrite_array TM_Unit); eauto; try solve [inversion_access].
    specialize (Hva (length m) (access_ref m (length m) _)). lia.
  - rewrite add_increments_length. eauto using access, Nat.lt_lt_succ_r.
Qed.

Local Lemma va_mem_set : forall m t ad v,
  valid_accesses m v ->
  valid_accesses m t ->
  valid_accesses m[ad <- v] t.
Proof.
  intros * ? ? ? Hacc.
  rewrite set_preserves_length.
  induction Hacc; inversion_va; eauto using access.
  destruct (Nat.eq_dec ad ad'); subst;
  do 2 (rewrite_array TM_Unit); eauto using access.
Qed.

Local Lemma va_subst : forall m t tx x,
  valid_accesses m t ->
  valid_accesses m tx ->
  valid_accesses m ([x := tx] t).
Proof.
  intros. induction t;
  try inversion_va; simpl; try (destruct String.string_dec);
  eauto using va_new, va_load, va_asg, va_call, va_seq, va_fun.
Qed.

(* ------------------------------------------------------------------------- *)
(* valid-accesses-preservation                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma va_none_preservation : forall m t t',
  valid_accesses m t ->
  t --[EF_None]--> t' ->
  valid_accesses m t'.
Proof.
  intros. induction_step; inversion_va;
  eauto using va_new, va_load, va_asg, va_fun, va_call, va_seq. 
  inversion_va. eauto using va_subst.
Qed.

Local Lemma va_alloc_preservation : forall m t t' v,
  valid_accesses m t ->
  t --[EF_Alloc (length m) v]--> t' ->
  valid_accesses (m +++ v) t'.
Proof.
  intros. induction_step; inversion_va;
  eauto using va_new, va_load, va_asg, va_call, va_seq, va_mem_add,
    va_added_value. 
Qed.

Local Lemma va_read_preservation : forall m t t' ad,
  valid_accesses m t ->
  t --[EF_Read ad m[ad]]--> t' ->
  valid_accesses m t'.
Proof.
  intros. induction_step; inversion_va;
  eauto using va_new, va_load, va_asg, va_call, va_seq.
  intros ? ?. eauto using access.
Qed.

Local Lemma va_write_preservation : forall m t t' ad v,
  valid_accesses m t ->
  t --[EF_Write ad v]--> t' ->
  valid_accesses m[ad <- v] t'.
Proof.
  intros.
  assert (valid_accesses m v); eauto using va_write_value.
  induction_step; inversion_va;
  eauto using va_new, va_load, va_asg, va_call, va_seq, va_mem_set.
  intros ? ?. inversion_access.
Qed.

Theorem va_mstep_preservation : forall m m' t t' eff,
  valid_accesses m t ->
  m / t ==[eff]==> m' / t' ->
  valid_accesses m' t'.
Proof.
  intros. inversion_mstep;
  eauto using va_none_preservation,
    va_alloc_preservation,
    va_read_preservation,
    va_write_preservation.
Qed.

Definition va_memory (m : mem) := forall ad,
  valid_accesses m m[ad].

(* ------------------------------------------------------------------------- *)
(* va memory                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Lemma va_memory_alloc_preservation : forall m t t' v,
  valid_accesses m t ->
  (forall ad, valid_accesses m m[ad]) ->
  t --[EF_Alloc (length m) v]--> t' ->
  (forall ad, valid_accesses (m +++ v) (m +++ v)[ad]).
Proof.
  intros * Hva Hmva ? ad. induction_step; inversion_va; eauto.
  decompose sum (lt_eq_lt_dec ad (length m)); subst;
  rewrite_array TM_Unit; eauto using va_mem_add.
  intros ? ?. inversion_access.
Qed.

Local Lemma va_memory_write_preservation : forall m t t' ad v,
  valid_accesses m t ->
  (forall ad, valid_accesses m m[ad]) ->
  t --[EF_Write ad v]--> t' ->
  (forall ad', valid_accesses m[ad <- v] m[ad <- v][ad']).
Proof.
  intros * Hva Hmva ? ad'. induction_step; inversion_va; eauto.
  decompose sum (lt_eq_lt_dec ad ad'); subst;
  rewrite_array TM_Unit; eauto using va_mem_set.
  TODO
Qed.

Theorem memory_va_mstep_preservation : forall m m' t t' eff,
  valid_accesses m t ->
  va_memory m ->
  m / t ==[eff]==> m' / t' ->
  va_memory m'.
Proof.
  intros * Hva Hmva ?. inversion_mstep; trivial.
  - induction_step; inversion_va; eauto.
    intros ad.
    decompose sum (lt_eq_lt_dec ad (length m)); subst; rewrite_array TM_Unit.
    + eauto using va_mem_add.
    + intros ad Hacc.
      rewrite add_increments_length.
      specialize (Hva ad).
      eapply Nat.lt_lt_succ_r.
      eapply Hva; clear Hva.
      specialize (Hmva ad ad).
    + 

Qed.

  forall ad ad', access m m[ad'] ad -> ad < length m.

(* ------------------------------------------------------------------------- *)
(* subst                                                                     *)
(* ------------------------------------------------------------------------- *)

(*
Lemma access_subst : forall m x X t t' ad,
  access m ([x := t'] t) ad ->
  access m (TM_Call (TM_Fun x X t) t') ad.
Proof.
  intros. induction t; eauto using access; simpl in *;
  try (destruct String.eqb; eauto using access);
  try solve [ 
    inversion_access; auto_specialize;
    inversion_access; try inversion_access; eauto using access
  ].
Qed.

Lemma not_access_subst : forall m id t x ad,
  ~ access m t ad ->
  ~ access m x ad ->
  ~ access m ([id := x] t) ad.
Proof.
  intros. induction t; trivial;
  try solve [
    inversion_not_access;
    eauto using not_access_new, not_access_load, not_access_asg,
      not_access_fun, not_access_call, not_access_seq
  ];
  simpl; destruct String.eqb; trivial.
  try solve [inversion_not_access; eauto using not_access_fun].
  - shelve.
  - shelve.
Qed.
*)
