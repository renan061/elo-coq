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

Local Ltac solve_vad_constructor := 
  intros; intros ? ?; inversion_ha; eauto.

Local Lemma vad_unit : forall m,
  valid_addresses m <{ unit }>.
Proof. solve_vad_constructor. Qed.

Local Lemma vad_new : forall m t T,
  valid_addresses m t ->
  valid_addresses m <{ new T t }>.
Proof. solve_vad_constructor. Qed.

Local Lemma vad_load : forall m t,
  valid_addresses m t ->
  valid_addresses m <{ *t }>.
Proof. solve_vad_constructor. Qed.

Local Lemma vad_asg : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ t1 = t2 }>.
Proof. solve_vad_constructor. Qed.

Local Lemma vad_fun : forall m x Tx t,
  valid_addresses m t ->
  valid_addresses m <{ fn x Tx --> t }>.
Proof. solve_vad_constructor. Qed.

Local Lemma vad_call : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ call t1 t2 }>.
Proof. solve_vad_constructor. Qed.

Local Lemma vad_seq : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ t1; t2 }>.
Proof. solve_vad_constructor. Qed.

Local Lemma vad_spawn : forall m t,
  valid_addresses m t ->
  valid_addresses m <{ spawn t }>.
Proof. solve_vad_constructor. Qed.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vad_inversion := 
  intros; unfold valid_addresses in *; try split; eauto using HasAddress.

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

Local Lemma inv_vad_fun : forall m x Tx t,
  valid_addresses m <{ fn x Tx --> t }> ->
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
  |H: valid_addresses _ <{ & _ :: _ }> |- _ => eapply inv_vad_ref  in H as ?
  |H: valid_addresses _ <{ new _ _  }> |- _ => eapply inv_vad_new  in H
  |H: valid_addresses _ <{ * _      }> |- _ => eapply inv_vad_load in H
  |H: valid_addresses _ <{ _ = _    }> |- _ => eapply inv_vad_asg  in H as [? ?]
  |H: valid_addresses _ <{ fn _ _ --> _ }> |- _ => eapply inv_vad_fun in H
  |H: valid_addresses _ <{ call _ _ }> |- _ => eapply inv_vad_call in H as [? ?]
  |H: valid_addresses _ <{ _ ; _    }> |- _ => eapply inv_vad_seq  in H as [? ?]
  |H: valid_addresses _ <{ spawn _  }> |- _ => eapply inv_vad_spawn in H
  end.

(* ------------------------------------------------------------------------- *)
(* preservation helpers                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma subst_vad : forall m t tx x,
  valid_addresses m t ->
  valid_addresses m tx ->
  valid_addresses m ([x := tx] t).
Proof.
  intros. induction t; try inversion_vad; simpl;
  eauto using vad_new, vad_load, vad_asg, vad_call, vad_seq, vad_fun, vad_spawn;
  destruct String.string_dec; subst; trivial;
  intros ? ?; inversion_ha; unfold valid_addresses in *; eauto.
Qed.

Local Lemma mem_add_vad : forall m t vTr,
  valid_addresses m t ->
  valid_addresses (m +++ vTr) t.
Proof.
  intros * ? ? Hha. rewrite add_increments_length.
  induction Hha; inversion_vad; eauto.
Qed.

Local Lemma mem_set_vad : forall m t ad v Tr,
  valid_addresses m v ->
  valid_addresses m t ->
  valid_addresses m[ad <- (v, Tr)] t.
Proof.
  intros * ? ? ? Hha. rewrite set_preserves_length.
  induction Hha; inversion_vad; eauto.
Qed.

Local Lemma step_spawn_vad_block : forall m t t' block,
  valid_addresses m t ->
  t --[EF_Spawn block]--> t' ->
  valid_addresses m block.
Proof.
  intros. induction_step; inversion_vad; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* term preservation                                                         *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_none_vad_preservation : forall m t t',
  valid_addresses m t ->
  t --[EF_None]--> t' ->
  valid_addresses m t'.
Proof.
  intros. induction_step; inversion_vad;  
  eauto using vad_new, vad_load, vad_asg, vad_fun, vad_call, vad_seq. 
  inversion_vad. eauto using subst_vad.
Qed.

Local Lemma step_alloc_vad_preservation : forall m t t' v Tr,
  valid_addresses m t ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  valid_addresses (m +++ (v, Tr)) t'.
Proof.
  intros. induction_step; inversion_vad;
  eauto using mem_add_vad, vad_new, vad_load, vad_asg, vad_call, vad_seq.
  intros ? ?. inversion_ha. rewrite add_increments_length. lia.
Qed.

Local Lemma step_read_vad_preservation : forall m t t' ad v,
  valid_addresses m v ->
  valid_addresses m t ->
  t --[EF_Read ad v]--> t' ->
  valid_addresses m t'.
Proof.
  intros. induction_step; inversion_vad;
  eauto using vad_new, vad_load, vad_asg, vad_call, vad_seq.
Qed.

Local Lemma step_write_vad_preservation : forall m t t' ad v Tr,
  valid_addresses m t ->
  t --[EF_Write ad v Tr]--> t' ->
  valid_addresses m[ad <- (v, Tr)] t'.
Proof.
  intros. assert (valid_addresses m v) by shelve.
  induction_step; inversion_vad;
  eauto using mem_set_vad, vad_unit, vad_new, vad_load, vad_asg,
    vad_call, vad_seq.
  Unshelve. intros ? ?. induction_step; inversion_vad; eauto.
Qed.

Local Corollary mstep_vad_preservation : forall m m' t t' eff,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  m / t ==[eff]==> m' / t' ->
  valid_addresses m' t'.
Proof.
  intros. inversion_mstep;
  eauto using step_none_vad_preservation,
    step_alloc_vad_preservation,
    step_read_vad_preservation,
    step_write_vad_preservation.
Qed.

Local Lemma step_spawn_vad_preservation : forall m t t' block,
  valid_addresses m t ->
  t --[EF_Spawn block]--> t' ->
  valid_addresses m t'.
Proof.
  intros. induction_step; inversion_vad;
  eauto using vad_unit, vad_new, vad_load, vad_asg, vad_call, vad_seq.
Qed.

(* ------------------------------------------------------------------------- *)
(* memory preservation                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_alloc_mem_vad_preservation : forall m t t' v Tr,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  forall_memory  (m +++ (v, Tr)) (valid_addresses (m +++ (v, Tr))).
Proof.
  intros. intros ad.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
  intros ? ?; rewrite add_increments_length;
  unfold valid_addresses in *; eauto using step_alloc_hasad, Nat.lt_lt_succ_r.
  simpl in *. inversion_ha.
Qed.

Local Lemma step_write_mem_vad_preservation : forall m t t' ad v Tr,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  t --[EF_Write ad v Tr]--> t' ->
  forall_memory m[ad <- (v, Tr)] (valid_addresses m[ad <- (v, Tr)]).
Proof.
  intros. intros ad'. 
  assert (ad < #m) by eauto using step_write_hasad1.
  destruct (Nat.eq_dec ad ad'); subst; simpl_array;
  intros ? ?; rewrite set_preserves_length;
  eauto using step_write_hasad2, Nat.lt_lt_succ_r.
  unfold valid_addresses in *. eauto.
Qed.

Local Corollary mstep_mem_vad_preservation : forall m m' t t' eff,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  m / t ==[eff]==> m' / t' ->
  forall_memory m' (valid_addresses m').
Proof.
  intros. inversion_mstep; trivial;
  eauto using step_alloc_mem_vad_preservation, step_write_mem_vad_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem valid_addresses_term_preservation : forall m m' ths ths' tid eff,
  forall_program m ths (valid_addresses m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_threads ths' (valid_addresses m').
Proof.
  intros * [? ?]. intros. eapply cstep_preservation; eauto.
  - eauto using mstep_vad_preservation.
  - intros. intros ? ?. unfold valid_addresses in *. inversion_mstep; eauto;
    (rewrite add_increments_length || rewrite set_preserves_length);
    eauto using Nat.lt_lt_succ_r.
  - eauto using step_spawn_vad_block.
  - eauto using step_spawn_vad_preservation.
  - unfold thread_default. eauto using vad_unit.
Qed.

Theorem valid_addresses_memory_preservation : forall m m' ths ths' tid eff,
  forall_program m ths (valid_addresses m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_memory m' (valid_addresses m').
Proof.
  intros * [? ?]. intros.
  inversion_cstep; eauto using mstep_mem_vad_preservation.
Qed.

