From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Classical_Prop.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import HasAddress.


(* The addresses of a term are valid if they
are smaller than the length of the memory. *)
Definition valid_addresses (m : mem) (t : tm) :=
  forall ad, HasAddress ad t -> ad < #m.

(* ------------------------------------------------------------------------- *)
(* constructors                                                              *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_va_constructor := 
  intros; intros ? ?; inversion_ha; eauto.

Local Lemma va_unit : forall m,
  valid_addresses m <{ unit }>.
Proof. solve_va_constructor. Qed.

Local Lemma va_new : forall m t T,
  valid_addresses m t ->
  valid_addresses m <{ new T t }>.
Proof. solve_va_constructor. Qed.

Local Lemma va_load : forall m t,
  valid_addresses m t ->
  valid_addresses m <{ *t }>.
Proof. solve_va_constructor. Qed.

Local Lemma va_asg : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ t1 = t2 }>.
Proof. solve_va_constructor. Qed.

Local Lemma va_fun : forall m x Tx t,
  valid_addresses m t ->
  valid_addresses m <{ fn x Tx --> t }>.
Proof. solve_va_constructor. Qed.

Local Lemma va_call : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ call t1 t2 }>.
Proof. solve_va_constructor. Qed.

Local Lemma va_seq : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ t1; t2 }>.
Proof. solve_va_constructor. Qed.

Local Lemma va_spawn : forall m t,
  valid_addresses m t ->
  valid_addresses m <{ spawn t }>.
Proof. solve_va_constructor. Qed.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_va_inversion := 
  intros; unfold valid_addresses in *; try split; eauto using HasAddress.

Local Lemma inv_va_ref : forall m ad T,
  valid_addresses m <{ &ad :: T }> ->
  ad < length m.
Proof. solve_va_inversion. Qed.

Local Lemma inv_va_new : forall m t T,
  valid_addresses m <{ new T t }> ->
  valid_addresses m t.
Proof. solve_va_inversion. Qed.

Local Lemma inv_va_load : forall m t,
  valid_addresses m <{ *t }> ->
  valid_addresses m t.
Proof. solve_va_inversion. Qed.

Local Lemma inv_va_asg : forall m t1 t2,
  valid_addresses m <{ t1 = t2 }> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_va_inversion. Qed.

Local Lemma inv_va_fun : forall m x Tx t,
  valid_addresses m <{ fn x Tx --> t }> ->
  valid_addresses m t.
Proof. solve_va_inversion. Qed.

Local Lemma inv_va_call : forall m t1 t2,
  valid_addresses m <{ call t1 t2 }> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_va_inversion. Qed.

Local Lemma inv_va_seq : forall m t1 t2,
  valid_addresses m <{ t1; t2 }> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_va_inversion. Qed.

Local Lemma inv_va_spawn : forall m t,
  valid_addresses m <{ spawn t }> ->
  valid_addresses m t.
Proof. solve_va_inversion. Qed.

Ltac inversion_va :=
  match goal with
  | H: valid_addresses _ <{ & _ :: _ }> |- _ => eapply inv_va_ref  in H as ?
  | H: valid_addresses _ <{ new _ _  }> |- _ => eapply inv_va_new  in H
  | H: valid_addresses _ <{ * _      }> |- _ => eapply inv_va_load in H
  | H: valid_addresses _ <{ _ = _    }> |- _ => eapply inv_va_asg  in H as [? ?]
  | H: valid_addresses _ <{ fn _ _ --> _ }> |- _ => eapply inv_va_fun in H
  | H: valid_addresses _ <{ call _ _ }> |- _ => eapply inv_va_call in H as [? ?]
  | H: valid_addresses _ <{ _ ; _    }> |- _ => eapply inv_va_seq  in H as [? ?]
  | H: valid_addresses _ <{ spawn _  }> |- _ => eapply inv_va_spawn in H
  end.

(* ------------------------------------------------------------------------- *)
(* preservation helpers                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma va_subst : forall m t tx x,
  valid_addresses m t ->
  valid_addresses m tx ->
  valid_addresses m ([x := tx] t).
Proof.
  intros. induction t; try inversion_va; simpl;
  eauto using va_new, va_load, va_asg, va_call, va_seq, va_fun, va_spawn;
  destruct String.string_dec; subst; trivial;
  intros ? ?; inversion_ha; unfold valid_addresses in *; eauto.
Qed.

Local Lemma mem_add_va : forall m t v,
  valid_addresses m t ->
  valid_addresses (m +++ v) t.
Proof.
  intros * ? ? Hha. rewrite add_increments_length.
  induction Hha; inversion_va; eauto.
Qed.

Local Lemma mem_set_va : forall m t ad v V,
  valid_addresses m v ->
  valid_addresses m t ->
  valid_addresses m[ad <- (v, V)] t.
Proof.
  intros * ? ? ? Hha. rewrite set_preserves_length.
  induction Hha; inversion_va; eauto.
Qed.

Local Lemma spawn_block_va : forall m t t' block,
  valid_addresses m t ->
  t --[EF_Spawn block]--> t' ->
  valid_addresses m block.
Proof.
  intros. induction_step; inversion_va; eauto.
Qed.


(* ------------------------------------------------------------------------- *)
(* term preservation                                                         *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_none_va_preservation : forall m t t',
  valid_addresses m t ->
  t --[EF_None]--> t' ->
  valid_addresses m t'.
Proof.
  intros. induction_step; inversion_va;  
  eauto using va_new, va_load, va_asg, va_fun, va_call, va_seq. 
  inversion_va. eauto using va_subst.
Qed.

Local Lemma step_alloc_va_preservation : forall m t t' v V,
  valid_addresses m t ->
  t --[EF_Alloc (length m) v V]--> t' ->
  valid_addresses (m +++ (v, V)) t'.
Proof.
  intros. induction_step; inversion_va;
  eauto using mem_add_va, va_new, va_load, va_asg, va_call, va_seq.
  intros ? ?. inversion_ha. rewrite add_increments_length. lia.
Qed.

Local Lemma step_read_va_preservation : forall m t t' ad v,
  valid_addresses m v ->
  valid_addresses m t ->
  t --[EF_Read ad v]--> t' ->
  valid_addresses m t'.
Proof.
  intros. induction_step; inversion_va;
  eauto using va_new, va_load, va_asg, va_call, va_seq.
Qed.

Local Lemma step_write_va_preservation : forall m t t' ad v V,
  valid_addresses m t ->
  t --[EF_Write ad v V]--> t' ->
  valid_addresses m[ad <- (v, V)] t'.
Proof.
  intros. assert (valid_addresses m v) by shelve.
  induction_step; inversion_va;
  eauto using mem_set_va, va_unit, va_new, va_load, va_asg, va_call, va_seq.
  Unshelve. intros ? ?. induction_step; inversion_va; eauto.
Qed.

Local Corollary mstep_va_preservation : forall m m' t t' eff,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  m / t ==[eff]==> m' / t' ->
  valid_addresses m' t'.
Proof.
  intros. inversion_mstep;
  eauto using step_none_va_preservation,
    step_alloc_va_preservation,
    step_read_va_preservation,
    step_write_va_preservation.
Qed.

Local Lemma step_spawn_va_preservation : forall m t t' block,
  valid_addresses m t ->
  t --[EF_Spawn block]--> t' ->
  valid_addresses m t'.
Proof.
  intros. induction_step; inversion_va;
  eauto using va_unit, va_new, va_load, va_asg, va_call, va_seq.
Qed.

(* ------------------------------------------------------------------------- *)
(* memory preservation                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_alloc_mem_va_preservation : forall m t t' v V,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  t --[EF_Alloc (length m) v V]--> t' ->
  forall_memory  (m +++ (v, V)) (valid_addresses (m +++ (v, V))).
Proof.
  intros. intros ad.
  decompose sum (lt_eq_lt_dec ad (length m)); subst; simpl_array;
  intros ? ?; rewrite add_increments_length;
  unfold valid_addresses in *; eauto using step_alloc_hasad, Nat.lt_lt_succ_r.
  simpl in *. inversion_ha.
Qed.

Local Lemma step_write_mem_va_preservation : forall m t t' ad v V,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  t --[EF_Write ad v V]--> t' ->
  forall_memory m[ad <- (v, V)] (valid_addresses m[ad <- (v, V)]).
Proof.
  intros. intros ad'. 
  assert (ad < length m) by eauto using step_write_hasad1.
  destruct (Nat.eq_dec ad ad'); subst; simpl_array;
  intros ? ?; rewrite set_preserves_length;
  eauto using step_write_hasad2, Nat.lt_lt_succ_r.
  unfold valid_addresses in *. eauto.
Qed.

Local Corollary mstep_mem_va_preservation : forall m m' t t' eff,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  m / t ==[eff]==> m' / t' ->
  forall_memory m' (valid_addresses m').
Proof.
  intros. inversion_mstep; trivial;
  eauto using step_alloc_mem_va_preservation, step_write_mem_va_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem valid_addresses_term_preservation : forall m m' ths ths' tid eff,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_threads ths' (valid_addresses m').
Proof.
  intros. inversion_cstep; intros tid'.
  - destruct (Nat.eq_dec tid tid'); subst; simpl_array;
    eauto using mstep_va_preservation.
    intros ? ?. unfold valid_addresses in *.
    inversion_mstep; eauto;
    (rewrite add_increments_length || rewrite set_preserves_length);
    eauto using Nat.lt_lt_succ_r.
  - decompose sum (lt_eq_lt_dec tid' (length ths[tid <- t'])); subst;
    simpl_array; eauto using spawn_block_va, va_unit.
    destruct (Nat.eq_dec tid tid'); subst; simpl_array;
    eauto using step_spawn_va_preservation.
Qed.

Theorem valid_addresses_memory_preservation : forall m m' ths ths' tid eff,
  forall_threads ths (valid_addresses m) ->
  forall_memory m (valid_addresses m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_memory m' (valid_addresses m').
Proof.
  intros. inversion_cstep; eauto using mstep_mem_va_preservation.
Qed.

