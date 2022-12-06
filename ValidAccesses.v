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

Lemma vac_length : forall m t ad,
  valid_accesses m t ->
  access m t ad ->
  ad < #m.
Proof.
  intros * Hvac Hacc.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; trivial.
  - specialize (Hvac (#m) Hacc). lia.
  - specialize (Hvac ad Hacc). lia.
Qed.

Lemma vac_nacc_length : forall m t,
  valid_accesses m t ->
  ~ access m t (#m).
Proof.
  intros * ? F. eapply vac_length in F; eauto. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* constructors                                                              *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vac_constructor := 
  intros; intros ? ?; inversion_acc; eauto.

Local Lemma vac_unit : forall m,
  valid_accesses m <{ unit }>.
Proof. solve_vac_constructor. Qed.

Local Lemma vac_num : forall m n,
  valid_accesses m <{ N n }>.
Proof. solve_vac_constructor. Qed.

Local Lemma vac_new : forall m t T,
  valid_accesses m t ->
  valid_accesses m <{ new T t }>.
Proof. solve_vac_constructor. Qed.

Local Lemma vac_load : forall m t,
  valid_accesses m t ->
  valid_accesses m <{ *t }>.
Proof. solve_vac_constructor. Qed.

Local Lemma vac_asg : forall m t1 t2,
  valid_accesses m t1 ->
  valid_accesses m t2 ->
  valid_accesses m <{ t1 = t2 }>.
Proof. solve_vac_constructor. Qed.

Local Lemma vac_var : forall m x,
  valid_accesses m <{ var x }>.
Proof. solve_vac_constructor. Qed.

Local Lemma vac_fun : forall m x Tx t,
  valid_accesses m t ->
  valid_accesses m <{ fn x Tx --> t }>.
Proof. solve_vac_constructor. Qed.

Local Lemma vac_call : forall m t1 t2,
  valid_accesses m t1 ->
  valid_accesses m t2 ->
  valid_accesses m <{ call t1 t2 }>.
Proof. solve_vac_constructor. Qed.

Local Lemma vac_seq : forall m t1 t2,
  valid_accesses m t1 ->
  valid_accesses m t2 ->
  valid_accesses m <{ t1; t2 }>.
Proof. solve_vac_constructor. Qed.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vac_inversion := 
  intros; unfold valid_accesses in *; try split; eauto using access.

Local Lemma inv_vac_ref : forall m ad T,
  valid_accesses m <{ &ad :: T }> ->
  valid_accesses m m[ad].tm.
Proof.
  intros; unfold valid_accesses in *; eauto using access.
  intros ad'. destruct (Nat.eq_dec ad ad'); subst; eauto using access.
Qed.

Local Lemma inv_vac_new : forall m t T,
  valid_accesses m <{ new T t }> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_load : forall m t,
  valid_accesses m <{ *t }> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_asg : forall m t1 t2,
  valid_accesses m <{ t1 = t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_fun : forall m x Tx t,
  valid_accesses m <{ fn x Tx --> t }> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_call : forall m t1 t2,
  valid_accesses m <{ call t1 t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_seq : forall m t1 t2,
  valid_accesses m <{ t1; t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Ltac inversion_vac :=
  match goal with
  | H: valid_accesses _ <{ &_ :: _  }> |- _ => eapply inv_vac_ref  in H as Hwba'
  | H: valid_accesses _ <{ new _ _  }> |- _ => eapply inv_vac_new  in H
  | H: valid_accesses _ <{ * _      }> |- _ => eapply inv_vac_load in H
  | H: valid_accesses _ <{ _ = _    }> |- _ => eapply inv_vac_asg  in H as [? ?]
  | H: valid_accesses _ <{ fn _ _ --> _ }> |- _ => eapply inv_vac_fun in H
  | H: valid_accesses _ <{ call _ _ }> |- _ => eapply inv_vac_call in H as [? ?]
  | H: valid_accesses _ <{ _ ; _    }> |- _ => eapply inv_vac_seq  in H as [? ?]
  end.

(* ------------------------------------------------------------------------- *)
(* preservation helpers                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_write_value_vac : forall m t t' ad v Tr,
  valid_accesses m t ->
  t --[EF_Write ad v Tr]--> t' ->
  valid_accesses m v.
Proof.
  intros. induction_step; inversion_vac; eauto using access.
Qed.

Local Lemma subst_vac : forall m t tx x,
  valid_accesses m t ->
  valid_accesses m tx ->
  valid_accesses m ([x := tx] t).
Proof.
  intros. induction t;
  try inversion_vac; simpl; try (destruct String.string_dec);
  eauto using vac_new, vac_load, vac_asg, vac_call, vac_seq, vac_fun.
  intros ? ?. inversion_acc.
Qed.

Local Lemma mem_add_vac : forall m t v Tr,
  valid_accesses m t ->
  valid_accesses (m +++ (v, Tr)) t.
Proof.
  intros * Hvac ? Hacc. induction Hacc; subst; inversion_vac; eauto.
  - eapply IHHacc. intros ? ?.
    destruct (lt_eq_lt_dec ad' (#m)) as [[? | ?] | ?]; subst;
    simpl_array; eauto; simpl in *; try inversion_acc.
    specialize (Hvac (#m) (acc_ref m (#m) _)). lia.
  - rewrite add_increments_length. eauto using access, Nat.lt_lt_succ_r.
Qed.

Local Lemma mem_set_vac : forall m t ad v Tr,
  valid_accesses m v ->
  valid_accesses m t ->
  valid_accesses m[ad <- (v, Tr)] t.
Proof.
  intros * ? ? ? Hacc. rewrite set_preserves_length.
  induction Hacc; inversion_vac; eauto using access.
  destruct (Nat.eq_dec ad ad'); subst;
  assert (ad' < #m) by eauto using access;
  simpl_array; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* term preservation                                                         *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_none_vac_preservation : forall m t t',
  valid_accesses m t ->
  t --[EF_None]--> t' ->
  valid_accesses m t'.
Proof.
  intros. induction_step; inversion_vac;
  eauto using vac_new, vac_load, vac_asg, vac_fun, vac_call, vac_seq.
  inversion_vac. eauto using subst_vac.
Qed.

Local Lemma step_alloc_vac_preservation : forall m t t' v Tr,
  valid_accesses m t ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  valid_accesses (m +++ (v, Tr)) t'.
Proof.
  intros. induction_step; inversion_vac;
  eauto using mem_add_vac, vac_new, vac_load, vac_asg, vac_call, vac_seq.
  assert (valid_accesses (m +++ (v, Tr)) v) by eauto using mem_add_vac.
  intros ? Hacc.
  remember (m +++ (v, Tr)) as m'.
  remember (<{ &(#m) :: Tr }>) as t'.
  induction Hacc; inversion Heqt'; subst.
  - simpl_array. eauto using access.
  - rewrite add_increments_length. lia.
Qed.

Local Lemma step_read_vac_preservation : forall m t t' ad,
  valid_accesses m t ->
  t --[EF_Read ad m[ad].tm]--> t' ->
  valid_accesses m t'.
Proof.
  intros. induction_step; inversion_vac;
  eauto using vac_new, vac_load, vac_asg, vac_call, vac_seq.
  intros ad' ?. destruct (Nat.eq_dec ad ad'); subst; eauto using access.
Qed.

Local Lemma step_write_vac_preservation : forall m t t' ad v Tr,
  valid_accesses m t ->
  t --[EF_Write ad v Tr]--> t' ->
  valid_accesses m[ad <- (v, Tr)] t'.
Proof.
  intros. assert (valid_accesses m v) by eauto using step_write_value_vac.
  induction_step; inversion_vac;
  eauto using mem_set_vac, vac_unit, vac_new, vac_load, vac_asg,
    vac_call, vac_seq.
Qed.

Local Corollary mstep_vac_preservation : forall m m' t t' eff,
  valid_accesses m t ->
  m / t ==[eff]==> m' / t' ->
  valid_accesses m' t'.
Proof.
  intros. inversion_mstep;
  eauto using step_none_vac_preservation,
    step_alloc_vac_preservation,
    step_read_vac_preservation,
    step_write_vac_preservation.
Qed.

Local Lemma step_spawn_vac_preservation : forall m t t' block,
  valid_accesses m t ->
  t --[EF_Spawn block]--> t' ->
  valid_accesses m t'.
Proof.
  intros. induction_step; try inversion_vac;
  eauto using vac_unit, vac_new, vac_load, vac_asg, vac_call, vac_seq.
Qed.

(* ------------------------------------------------------------------------- *)
(* memory preservation                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_alloc_mem_vac_preservation : forall m t t' v Tr,
  valid_accesses m t ->
  forall_memory m (valid_accesses m) ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  forall_memory (m +++ (v, Tr)) (valid_accesses (m +++ (v, Tr))).
Proof.
  intros * Hvac ? ? ad. induction_step; inversion_vac; eauto;
  decompose sum (lt_eq_lt_dec ad (#m)); subst;
  simpl_array; eauto using mem_add_vac.
  unfold memory_default. simpl. eauto using vac_unit.
Qed.

Local Lemma step_write_mem_vac_preservation : forall m t t' ad v Tr,
  valid_accesses m t ->
  forall_memory m (valid_accesses m) ->
  t --[EF_Write ad v Tr]--> t' ->
  forall_memory m[ad <- (v, Tr)] (valid_accesses m[ad <- (v, Tr)]).
Proof.
  intros * Hvac Hmvac ? ad'. induction_step; inversion_vac; eauto.
  decompose sum (lt_eq_lt_dec ad ad'); subst;
  try (assert (ad' < #m) by eauto using access);
  simpl_array; eauto using mem_set_vac.
Qed.

Local Corollary mstep_mem_vac_preservation : forall m m' t t' eff,
  valid_accesses m t ->
  forall_memory m (valid_accesses m) ->
  m / t ==[eff]==> m' / t' ->
  forall_memory m' (valid_accesses m').
Proof.
  intros. inversion_mstep;
  eauto using step_alloc_mem_vac_preservation, step_write_mem_vac_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

From Elo Require Import HasAddress.
From Elo Require Import ValidAddresses.

Local Lemma todo : forall m t ad,
  access m t ad ->
  HasAddress ad t \/ (exists ad', HasAddress ad m[ad'].tm).
Proof.
  intros * Hacc. induction Hacc;
  try destruct IHHacc as [? | [? ?]];
  eauto using HasAddress.
Qed.

Local Lemma step_spawn_block_vac : forall m t t' block,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  valid_accesses m t ->
  t --[EF_Spawn block]--> t' ->
  valid_accesses m block.
Proof.
  intros. induction_step;
  inversion_va; try inversion_vac; eauto. 
  intros ? ?. specialize (H0 ad).
  assert (HasAddress ad block \/ (exists ad', HasAddress ad m[ad'].tm))
    as [? | [? ?]] by eauto using todo; eauto.
  specialize (H x). simpl in *. eauto.
Qed.

Theorem valid_accesses_term_preservation : forall m m' ths ths' tid eff,
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  forall_memory m (valid_accesses m) ->
  forall_threads ths (valid_accesses m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_threads ths' (valid_accesses m').
Proof.
  intros. eapply cstep_preservation; eauto; intros.
  - eauto using mstep_vac_preservation.
  - inversion_mstep; eauto using mem_add_vac, mem_set_vac, step_write_value_vac.
  - eauto using step_spawn_block_vac.
  - eauto using step_spawn_vac_preservation.
  - unfold thread_default. eauto using vac_unit.
Qed.

Theorem valid_accesses_memory_preservation : forall m m' ths ths' tid eff,
  forall_threads ths (valid_accesses m) ->
  forall_memory m (valid_accesses m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_memory m' (valid_accesses m').
Proof.
  intros. inversion_cstep; eauto using mstep_mem_vac_preservation.
Qed.

