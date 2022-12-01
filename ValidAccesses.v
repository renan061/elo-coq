From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.

Definition valid_accesses (m : mem) (t : tm) :=
  forall ad, access m t ad -> ad < length m.

(* ------------------------------------------------------------------------- *)
(* auxiliary                                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma va_length : forall m t ad,
  valid_accesses m t ->
  access m t ad ->
  ad < length m.
Proof.
  intros * Hva Hacc. decompose sum (lt_eq_lt_dec ad (length m)); subst; trivial.
  - specialize (Hva (length m) Hacc). lia.
  - specialize (Hva ad Hacc). lia.
Qed.

Lemma va_nacc_length : forall m t,
  valid_accesses m t ->
  ~ access m t (length m).
Proof.
  intros * ? F. eapply va_length in F; eauto. lia.
Qed.

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
(* inversion-va                                                              *)
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
  valid_accesses m m[ad].tm.
Proof.
  intros; unfold valid_accesses in *; eauto using access.
  intros ad'. destruct (Nat.eq_dec ad ad'); subst; eauto using access.
Qed.

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

Local Lemma va_alloc_value : forall m t t' ad v V,
  valid_accesses m t ->
  t --[EF_Alloc ad v V]--> t' ->
  valid_accesses m v.
Proof.
  intros. induction_step; inversion_va; eauto using access.
Qed.

Local Lemma va_write_value : forall m t t' ad v V,
  valid_accesses m t ->
  t --[EF_Write ad v V]--> t' ->
  valid_accesses m v.
Proof.
  intros. induction_step; inversion_va; eauto using access.
Qed.

Local Lemma va_added_value : forall m v V T,
  valid_accesses (m +++ (v, V)) v ->
  valid_accesses (m +++ (v, V)) <{ &(length m) :: T }>.
Proof.
  intros * ? ? Hacc.
  remember (m +++ (v, V)) as m'.
  remember (<{ &(length m) :: T }>) as t'.
  induction Hacc; inversion Heqt'; subst.
  - do 2 simpl_array. eauto using access.
  - rewrite add_increments_length. lia.
Qed.

Local Lemma va_mem_add : forall m t v V,
  valid_accesses m t ->
  valid_accesses (m +++ (v, V)) t.
Proof.
  intros * Hva ? Hacc. induction Hacc; subst; inversion_va; eauto.
  - eapply IHHacc. intros ? ?.
    destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]; subst;
    do 3 simpl_array; eauto; simpl in *; try solve [inversion_access].
    specialize (Hva (length m) (access_ref m (length m) _)). lia.
  - rewrite add_increments_length. eauto using access, Nat.lt_lt_succ_r.
Qed.

Local Lemma va_mem_set : forall m t ad v V,
  valid_accesses m v ->
  valid_accesses m t ->
  valid_accesses m[ad <- (v, V)] t.
Proof.
  intros * ? ? ? Hacc.
  rewrite set_preserves_length.
  induction Hacc; inversion_va; eauto using access.
  destruct (Nat.eq_dec ad ad'); subst;
  assert (ad' < length m) by eauto using access;
  do 2 simpl_array; eauto using access.
Qed.

Local Lemma va_subst : forall m t tx x,
  valid_accesses m t ->
  valid_accesses m tx ->
  valid_accesses m ([x := tx] t).
Proof.
  intros. induction t;
  try inversion_va; simpl; try (destruct String.string_dec);
  eauto using va_new, va_load, va_asg, va_call, va_seq, va_fun.
  intros ? F. inversion F.
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

Local Lemma va_alloc_preservation : forall m t t' v V,
  valid_accesses m t ->
  t --[EF_Alloc (length m) v V]--> t' ->
  valid_accesses (m +++ (v, V)) t'.
Proof.
  intros. induction_step; inversion_va;
  eauto using va_new, va_load, va_asg, va_call, va_seq, va_mem_add,
    va_added_value. 
Qed.

Local Lemma va_read_preservation : forall m t t' ad,
  valid_accesses m t ->
  t --[EF_Read ad m[ad].tm]--> t' ->
  valid_accesses m t'.
Proof.
  intros. induction_step; inversion_va;
  eauto using va_new, va_load, va_asg, va_call, va_seq.
  intros ad' ?. destruct (Nat.eq_dec ad ad'); subst; eauto using access.
Qed.

Local Lemma va_write_preservation : forall m t t' ad v V,
  valid_accesses m t ->
  t --[EF_Write ad v V]--> t' ->
  valid_accesses m[ad <- (v, V)] t'.
Proof.
  intros. assert (valid_accesses m v); eauto using va_write_value.
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

(* ------------------------------------------------------------------------- *)
(* memory valid-accesses preservation                                        *)
(* ------------------------------------------------------------------------- *)

Local Lemma mva_alloc_preservation : forall m t t' v V,
  valid_accesses m t ->
  forall_memory_terms m (valid_accesses m) ->
  t --[EF_Alloc (length m) v V]--> t' ->
  forall_memory_terms (m +++ (v, V)) (valid_accesses (m +++ (v, V))).
Proof.
  intros * Hva ? ? ad. induction_step; inversion_va; eauto.
  decompose sum (lt_eq_lt_dec ad (length m)); subst;
  simpl_array; eauto using va_mem_add.
  intros ? ?. simpl in *. inversion_access.
Qed.

Local Lemma mva_write_preservation : forall m t t' ad v V,
  valid_accesses m t ->
  forall_memory_terms m (valid_accesses m) ->
  t --[EF_Write ad v V]--> t' ->
  forall_memory_terms m[ad <- (v, V)] (valid_accesses m[ad <- (v, V)]).
Proof.
  intros * Hva Hmva ? ad'. induction_step; inversion_va; eauto.
  decompose sum (lt_eq_lt_dec ad ad'); subst;
  try (assert (ad' < length m) by eauto using access);
  simpl_array; eauto using va_mem_set.
Qed.

Theorem mva_mstep_preservation : forall m m' t t' eff,
  valid_accesses m t ->
  forall_memory_terms m (valid_accesses m) ->
  m / t ==[eff]==> m' / t' ->
  forall_memory_terms m' (valid_accesses m').
Proof.
  intros. inversion_mstep;
  eauto using mva_alloc_preservation, mva_write_preservation.
Qed.

