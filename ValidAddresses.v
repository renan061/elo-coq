From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import AnyTerm.
From Elo Require Import Meta.

(* ------------------------------------------------------------------------- *)
(* has_address                                                               *)
(* ------------------------------------------------------------------------- *)

(* Make into submodule. *)

Inductive is_address : addr -> tm -> Prop :=
  | is_ad : forall ad T,
    is_address ad <{ &ad :: T}>
  .

Notation "t 'has_address' ad" := (anyt (is_address ad) t)
  (at level 80, no associativity).

Local Lemma write_requires_has_address : forall t t' ad v V,
  t --[EF_Write ad v V]--> t' ->
  t has_address ad.
Proof.
  intros. induction_step; eauto using anyt, is_address.
Qed.

Local Ltac inversion_is_address := 
  match goal with
  | H : is_address _ _ |- _ => inversion_subst_clear H
  end.

Local Ltac inversion_has_address := 
  match goal with
  | H : _ has_address _ |- _ =>
      inversion_subst_clear H; try inversion_is_address
  end.

Local Hint Extern 4 =>
  try inversion_has_address; try inversion_is_address
  : has_address_inversion.

(* ------------------------------------------------------------------------- *)
(* valid-addresses                                                           *)
(* ------------------------------------------------------------------------- *)

(* The addresses are valid if they are within the bounds of the memory. *)
Definition valid_addresses (m : mem) (t : tm) :=
  forall ad, t has_address ad -> ad < #m.

#[export] Hint Unfold valid_addresses : core.

Theorem valid_address_write : forall m t t' ad v V,
  valid_addresses m t ->
  t --[EF_Write ad v V]--> t' ->
  ad < #m.
Proof. eauto using write_requires_has_address. Qed.

(* ------------------------------------------------------------------------- *)
(* constructors                                                              *)
(* ------------------------------------------------------------------------- *)

Local Lemma vad_unit : forall m,
  valid_addresses m <{ unit }>.
Proof. eauto with has_address_inversion. Qed.

Local Lemma vad_num : forall m n,
  valid_addresses m <{ N n }>.
Proof. eauto with has_address_inversion. Qed.

Local Lemma vad_new : forall m t T,
  valid_addresses m t ->
  valid_addresses m <{ new T t }>.
Proof. eauto with has_address_inversion. Qed.

Local Lemma vad_load : forall m t,
  valid_addresses m t ->
  valid_addresses m <{ *t }>.
Proof. eauto with has_address_inversion. Qed.

Local Lemma vad_asg : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ t1 = t2 }>.
Proof. eauto with has_address_inversion. Qed.

Local Lemma vad_var : forall m x,
  valid_addresses m <{ var x }>.
Proof. eauto with has_address_inversion. Qed.

Local Lemma vad_fun : forall m x Tx t,
  valid_addresses m t ->
  valid_addresses m <{ fn x Tx t }>.
Proof. eauto with has_address_inversion. Qed.

Local Lemma vad_call : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ call t1 t2 }>.
Proof. eauto with has_address_inversion. Qed.

Local Lemma vad_seq : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ t1; t2 }>.
Proof. eauto with has_address_inversion. Qed.

Local Lemma vad_spawn : forall m t,
  valid_addresses m t ->
  valid_addresses m <{ spawn t }>.
Proof. eauto with has_address_inversion. Qed.

Local Hint Resolve vad_unit vad_num 
                   vad_new vad_load vad_asg
                   vad_var vad_fun vad_call vad_seq vad_spawn
                   : vad_constructors.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vad_inversion := 
  intros; try split; eauto using anyt, is_address.

(* vad_unit implicates nothing *)
(* vad_num implicates nothing *)

Local Lemma inv_vad_ref : forall m ad T,
  valid_addresses m <{ &ad :: T }> ->
  ad < #m.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_new : forall m t T,
  valid_addresses m <{ new T t }> ->
  valid_addresses m t.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_load : forall m t,
  valid_addresses m <{ *t }> ->
  valid_addresses m t.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_asg : forall m t1 t2,
  valid_addresses m <{ t1 = t2 }> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_vad_inversion. Qed.

(* vad_var implicates nothing *)

Local Lemma inv_vad_fun : forall m x Tx t,
  valid_addresses m <{ fn x Tx t }> ->
  valid_addresses m t.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_call : forall m t1 t2,
  valid_addresses m <{ call t1 t2 }> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_seq : forall m t1 t2,
  valid_addresses m <{ t1; t2 }> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_spawn : forall m t,
  valid_addresses m <{ spawn t }> ->
  valid_addresses m t.
Proof. solve_vad_inversion. Qed.

Ltac inversion_vad :=
 match goal with
 | H: valid_addresses _ <{ & _ :: _ }> |- _ => eapply inv_vad_ref  in H as ?
 | H: valid_addresses _ <{ new _ _  }> |- _ => eapply inv_vad_new  in H
 | H: valid_addresses _ <{ * _      }> |- _ => eapply inv_vad_load in H
 | H: valid_addresses _ <{ _ = _    }> |- _ => eapply inv_vad_asg  in H as [? ?]
 | H: valid_addresses _ <{ fn _ _ _ }> |- _ => eapply inv_vad_fun  in H
 | H: valid_addresses _ <{ call _ _ }> |- _ => eapply inv_vad_call in H as [? ?]
 | H: valid_addresses _ <{ _ ; _    }> |- _ => eapply inv_vad_seq  in H as [? ?]
 | H: valid_addresses _ <{ spawn _  }> |- _ => eapply inv_vad_spawn in H
 end.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Local Lemma subst_preservation_vad :
  subst_preservation valid_addresses.
Proof.
  unfold subst_preservation.
  intros. induction t; try inversion_vad; simpl; eauto with vad_constructors;
  destruct string_eq_dec; subst; trivial;
  autounfold in *; eauto with has_address_inversion.
Qed.

Local Lemma mem_add_preservation_vad :
  mem_add_preservation valid_addresses.
Proof.
  unfold mem_add_preservation.
  intros. intros ? Hha. rewrite add_increments_length.
  induction Hha; try inversion_vad; eauto with has_address_inversion.
Qed.

Local Lemma mem_set_preservation_vad :
  mem_set_preservation valid_addresses.
Proof.
  unfold mem_set_preservation.
  intros. intros ? Hha. rewrite set_preserves_length.
  induction Hha; try inversion_vad; eauto with has_address_inversion.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma thread_default_preservation_vad :
  thread_default_preservation valid_addresses.
Proof.
  unfold thread_default_preservation.
  intros. intros ? ?. inversion_has_address.
Qed.

Local Lemma spawn_block_preservation_vad :
  spawn_block_preservation valid_addresses.
Proof.
  unfold spawn_block_preservation.
  intros. induction_step; inversion_vad; eauto.
Qed.

Local Lemma untouched_threads_preservation_vad :
  untouched_threads_preservation valid_addresses.
Proof.
  unfold untouched_threads_preservation.
  intros. intros ? ?. autounfold in *. inversion_mstep; eauto;
  (rewrite add_increments_length || rewrite set_preserves_length);
  eauto using Nat.lt_lt_succ_r.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma tstep_none_preservation_vad :
  tstep_none_preservation valid_addresses.
Proof.
  unfold tstep_none_preservation.
  intros. induction_step; inversion_vad; eauto with vad_constructors. 
  inversion_vad. eauto using subst_preservation_vad.
Qed.

Local Lemma tstep_alloc_preservation_vad :
  tstep_alloc_preservation valid_addresses.
Proof.
  unfold tstep_alloc_preservation.
  intros. induction_step; inversion_vad;
  eauto using mem_add_preservation_vad with vad_constructors.
  intros ? ?. rewrite add_increments_length. inversion_has_address. lia.
Qed.

Local Lemma tstep_read_preservation_vad :
  tstep_read_preservation valid_addresses.
Proof.
  unfold tstep_read_preservation.
  intros. induction_step; inversion_vad; eauto with vad_constructors.
Qed.

Local Lemma tstep_write_preservation_vad :
  tstep_write_preservation valid_addresses.
Proof.
  unfold tstep_write_preservation.
  intros. assert (valid_addresses m v); induction_step; inversion_vad;
  eauto using mem_set_preservation_vad with vad_constructors.
Qed.

Local Lemma tstep_spawn_preservation_vad :
  tstep_spawn_preservation valid_addresses.
Proof.
  unfold tstep_spawn_preservation.
  intros. induction_step; inversion_vad; eauto with vad_constructors.
Qed.

Local Hint Resolve
  subst_preservation_vad
  mem_add_preservation_vad
  mem_set_preservation_vad
  thread_default_preservation_vad
  spawn_block_preservation_vad
  untouched_threads_preservation_vad
  tstep_none_preservation_vad
  tstep_alloc_preservation_vad
  tstep_read_preservation_vad
  tstep_write_preservation_vad
  tstep_spawn_preservation_vad
  : vad_preservation.

Local Corollary cstep_preservation_vad :
  cstep_preservation valid_addresses.
Proof. eauto with preservation vad_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* memory preservation                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_alloc_mem_vad_preservation : forall m t t' v T,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  t --[EF_Alloc (#m) v T]--> t' ->
  forall_memory  (m +++ (v, T)) (valid_addresses (m +++ (v, T))).
Proof.
  intros. intros ad.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
  intros ? ?; rewrite add_increments_length; autounfold in *;
  eauto using anyt_alloc_generalization, Nat.lt_lt_succ_r
        with has_address_inversion.
Qed.

Local Lemma step_write_mem_vad_preservation : forall m t t' ad v T,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  t --[EF_Write ad v T]--> t' ->
  forall_memory m[ad <- (v, T)] (valid_addresses m[ad <- (v, T)]).
Proof.
  intros. intros ad'. 
  assert (ad < #m) by eauto using valid_address_write.
  destruct (Nat.eq_dec ad ad'); subst; simpl_array;
  intros ? ?; rewrite set_preserves_length; autounfold in *;
  eauto using anyt_write_generalization, Nat.lt_lt_succ_r.
Qed.

Local Corollary mstep_mem_vad_preservation : forall m m' t t' e,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  m / t ==[e]==> m' / t' ->
  forall_memory m' (valid_addresses m').
Proof.
  intros. inversion_mstep; trivial;
  eauto using step_alloc_mem_vad_preservation, step_write_mem_vad_preservation.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem valid_addresses_memory_preservation : forall m m' ths ths' tid e,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_memory m' (valid_addresses m').
Proof.
  intros. inversion_cstep; eauto using mstep_mem_vad_preservation.
Qed.

Corollary valid_addresses_preservation :
  property_preservation valid_addresses.
Proof.
  unfold property_preservation. intros * [? ?] ?.
  eauto using cstep_preservation_vad, valid_addresses_memory_preservation.
Qed.

