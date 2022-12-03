From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Classical_Prop.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.

(* -------------------------------------------------------------------------- *)
(* has-address                                                                *)
(* -------------------------------------------------------------------------- *)

Inductive HasAddress (ad : addr) : tm -> Prop :=
  | hasad_ref : forall T,
    HasAddress ad <{ &ad :: T }>

  | hasad_new : forall t T,
    HasAddress ad t ->
    HasAddress ad <{ new T t }>

  | hasad_load : forall t,
    HasAddress ad t ->
    HasAddress ad <{ *t }>

  | hasad_asg1 : forall t1 t2,
    HasAddress ad t1 ->
    HasAddress ad <{ t1 = t2 }>

  | hasad_asg2 : forall t1 t2,
    HasAddress ad t2 ->
    HasAddress ad <{ t1 = t2 }>

  | hasad_fun : forall t x Tx,
    HasAddress ad t ->
    HasAddress ad <{ fn x Tx --> t }>

  | hasad_call1 : forall t1 t2,
    HasAddress ad t1 ->
    HasAddress ad <{ call t1 t2 }>

  | hasad_call2 : forall t1 t2,
    HasAddress ad t2 ->
    HasAddress ad <{ call t1 t2 }>

  | hasad_seq1 : forall t1 t2,
    HasAddress ad t1 ->
    HasAddress ad <{ t1; t2 }>

  | hasad_seq2 : forall t1 t2,
    HasAddress ad t2 ->
    HasAddress ad <{ t1; t2 }>

  | hasad_spawn : forall t,
    HasAddress ad t ->
    HasAddress ad <{ spawn t }>
  .

Lemma hasad_dec : forall ad t,
  Decidable.decidable (HasAddress ad t).
Proof. intros. eauto using classic_decidable. Qed.

(* -------------------------------------------------------------------------- *)
(* inversion-ha                                                               *)
(* -------------------------------------------------------------------------- *)

Ltac inversion_ha :=
  match goal with
  | H : HasAddress _ <{ unit         }> |- _ => inversion H
  | H : HasAddress _ <{ N _          }> |- _ => inversion H
  | H : HasAddress _ <{ & _ :: _     }> |- _ => inversion H; subst
  | H : HasAddress _ <{ new _ _      }> |- _ => inversion H; subst
  | H : HasAddress _ <{ * _          }> |- _ => inversion H; subst
  | H : HasAddress _ <{ _ = _        }> |- _ => inversion H; subst
  | H : HasAddress _ <{ var _        }> |- _ => inversion H
  | H : HasAddress _ <{ fn _ _ --> _ }> |- _ => inversion H; subst
  | H : HasAddress _ <{ call _ _     }> |- _ => inversion H; subst
  | H : HasAddress _ <{ _ ; _        }> |- _ => inversion H; subst
  | H : HasAddress _ <{ spawn _      }> |- _ => inversion H; subst
  end.

(* -------------------------------------------------------------------------- *)
(* inversion-nha                                                              *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_inv_nha1 :=
  intros; intros ?; eauto using HasAddress.

Local Ltac solve_inv_nha2 :=
  intros * F; eapply Classical_Prop.not_or_and;
  intros [? | ?]; eapply F; eauto using HasAddress.

Local Lemma inv_nha_ref : forall ad ad' T,
  ~ HasAddress ad <{ &ad' :: T}> ->
  ad <> ad'.
Proof. intros. intros ?. subst. eauto using HasAddress. Qed.

Local Lemma inv_nha_new : forall ad t T,
  ~ HasAddress ad <{ new T t }> ->
  ~ HasAddress ad t.
Proof. solve_inv_nha1. Qed.

Local Lemma inv_nha_load : forall ad t,
  ~ HasAddress ad <{ *t }> ->
  ~ HasAddress ad t.
Proof. solve_inv_nha1. Qed.

Local Lemma inv_nha_asg : forall ad t1 t2,
  ~ HasAddress ad <{ t1 = t2 }> ->
  (~ HasAddress ad t1) /\ (~ HasAddress ad t2).
Proof. solve_inv_nha2. Qed.

Local Lemma inv_nha_fun : forall ad t x Tx,
  ~ HasAddress ad <{ fn x Tx --> t }> ->
  ~ HasAddress ad t.
Proof. solve_inv_nha1. Qed.

Local Lemma inv_nha_call : forall ad t1 t2,
  ~ HasAddress ad <{ call t1 t2 }> ->
  (~ HasAddress ad t1) /\ (~ HasAddress ad t2).
Proof. solve_inv_nha2. Qed.

Local Lemma inv_nha_seq : forall ad t1 t2,
  ~ HasAddress ad <{ t1; t2 }> ->
  (~ HasAddress ad t1) /\ (~ HasAddress ad t2).
Proof. solve_inv_nha2. Qed.

Local Lemma inv_nha_spawn : forall ad t,
  ~ HasAddress ad <{ spawn t }> ->
  ~ HasAddress ad t.
Proof. solve_inv_nha1. Qed.

Ltac inversion_nha :=
  match goal with
  | H : ~ HasAddress _ <{ & _ :: _ }> |- _ => eapply inv_nha_ref   in H
  | H : ~ HasAddress _ <{ new _ _  }> |- _ => eapply inv_nha_new   in H
  | H : ~ HasAddress _ <{ * _      }> |- _ => eapply inv_nha_load  in H
  | H : ~ HasAddress _ <{ _ = _    }> |- _ => eapply inv_nha_asg   in H as [? ?]
  | H : ~ HasAddress _ <{ fn _ _ --> _ }> |- _ => eapply inv_nha_fun in H
  | H : ~ HasAddress _ <{ call _ _ }> |- _ => eapply inv_nha_call  in H as [? ?]
  | H : ~ HasAddress _ <{ _ ; _    }> |- _ => eapply inv_nha_seq   in H as [? ?]
  | H : ~ HasAddress _ <{ spawn _  }> |- _ => eapply inv_nha_spawn in H
  end.

(* ------------------------------------------------------------------------- *)
(* has-address helpers                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma step_write_hasad1 : forall t t' ad v V,
  t --[EF_Write ad v V]--> t' ->
  HasAddress ad t.
Proof. intros. induction_step; eauto using HasAddress. Qed.

Lemma step_write_hasad2 : forall t t' ad ad' v V,
  HasAddress ad v ->
  t --[EF_Write ad' v V]--> t' ->
  HasAddress ad t.
Proof. intros. induction_step; eauto using HasAddress. Qed.

(* -------------------------------------------------------------------------- *)
(* valid-addresses                                                            *)
(* -------------------------------------------------------------------------- *)

Definition valid_addresses (m : mem) (t : tm) :=
  forall ad, HasAddress ad t -> ad < length m.

Local Ltac solve_con_va := 
  intros; intros ? ?; inversion_ha; eauto.

Local Lemma va_unit: forall m,
  valid_addresses m <{ unit }>.
Proof. solve_con_va. Qed.

Local Lemma va_num: forall m n,
  valid_addresses m <{ N n }>.
Proof. solve_con_va. Qed.

Local Lemma va_new: forall m t T,
  valid_addresses m t ->
  valid_addresses m <{ new T t }>.
Proof. solve_con_va. Qed.

Local Lemma va_load : forall m t,
  valid_addresses m t ->
  valid_addresses m <{ *t }>.
Proof. solve_con_va. Qed.

Local Lemma va_asg : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ t1 = t2 }>.
Proof. solve_con_va. Qed.

Local Lemma va_fun : forall m x Tx t,
  valid_addresses m t ->
  valid_addresses m <{ fn x Tx --> t }>.
Proof. solve_con_va. Qed.

Local Lemma va_call : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ call t1 t2 }>.
Proof. solve_con_va. Qed.

Local Lemma va_seq : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{ t1; t2 }>.
Proof. solve_con_va. Qed.

Local Lemma va_spawn : forall m t,
  valid_addresses m t ->
  valid_addresses m <{ spawn t }>.
Proof. solve_con_va. Qed.

(* -------------------------------------------------------------------------- *)
(* inversion-va                                                               *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_inv_va := 
  intros; unfold valid_addresses in *; try split; eauto using HasAddress.

Local Lemma inv_va_ref : forall m ad T,
  valid_addresses m <{ &ad :: T }> ->
  ad < length m.
Proof. intros. unfold valid_addresses in *. eauto using HasAddress. Qed.

Local Lemma inv_va_new : forall m t T,
  valid_addresses m <{ new T t }> ->
  valid_addresses m t.
Proof. solve_inv_va. Qed.

Local Lemma inv_va_load : forall m t,
  valid_addresses m <{ *t }> ->
  valid_addresses m t.
Proof. solve_inv_va. Qed.

Local Lemma inv_va_asg : forall m t1 t2,
  valid_addresses m <{ t1 = t2 }> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_inv_va. Qed.

Local Lemma inv_va_fun : forall m x Tx t,
  valid_addresses m <{ fn x Tx --> t }> ->
  valid_addresses m t.
Proof. solve_inv_va. Qed.

Local Lemma inv_va_call : forall m t1 t2,
  valid_addresses m <{ call t1 t2 }> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_inv_va. Qed.

Local Lemma inv_va_seq : forall m t1 t2,
  valid_addresses m <{ t1; t2 }> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_inv_va. Qed.

Local Lemma inv_va_spawn : forall m t,
  valid_addresses m <{ spawn t }> ->
  valid_addresses m t.
Proof. solve_inv_va. Qed.

Ltac inversion_va :=
  match goal with
  | H: valid_addresses _ <{ & ?ad :: _ }> |- _ => eapply inv_va_ref in H as ?
  | H: valid_addresses _ <{ new _ _ }> |- _ => eapply inv_va_new  in H
  | H: valid_addresses _ <{ * _     }> |- _ => eapply inv_va_load in H
  | H: valid_addresses _ <{ _ = _   }> |- _ => eapply inv_va_asg  in H as [? ?]
  | H: valid_addresses _ <{ fn _ _ --> _ }> |- _ => eapply inv_va_fun in H
  | H: valid_addresses _ <{ call _ _ }> |- _ => eapply inv_va_call in H as [? ?]
  | H: valid_addresses _ <{ _ ; _    }> |- _ => eapply inv_va_seq  in H as [? ?]
  | H: valid_addresses _ <{ spawn _  }> |- _ => eapply inv_va_spawn in H
  end.

(* -------------------------------------------------------------------------- *)
(* va-preservation helpers                                                    *)
(* -------------------------------------------------------------------------- *)

Local Lemma va_subst : forall m t tx x,
  valid_addresses m t ->
  valid_addresses m tx ->
  valid_addresses m ([x := tx] t).
Proof.
  intros. induction t;
  try inversion_va; simpl;
  eauto using va_new, va_load, va_asg, va_call, va_seq, va_fun, va_spawn;
  destruct String.string_dec; subst; trivial;
  intros ? ?; inversion_ha; unfold valid_addresses in *; eauto.
Qed.

Local Lemma mem_add_va : forall m t v,
  valid_addresses m t ->
  valid_addresses (m +++ v) t.
Proof.
  intros * ? ? Hha. induction Hha; inversion_va; eauto.
  rewrite add_increments_length. lia.
Qed.

Local Lemma mem_set_va : forall m t ad v V,
  valid_addresses m v ->
  valid_addresses m t ->
  valid_addresses m[ad <- (v, V)] t.
Proof.
  intros * ? ? ? Hha. rewrite set_preserves_length.
  induction Hha; inversion_va; eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* va-preservation                                                            *)
(* -------------------------------------------------------------------------- *)

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
  eauto using va_new, va_load, va_asg, va_call, va_seq, mem_add_va.
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
  eauto using va_unit, va_new, va_load, va_asg, va_call, va_seq, mem_set_va.
  Unshelve. intros ? ?. induction_step; inversion_va; eauto.
Qed.

Local Corollary mstep_va_preservation : forall m m' t t' eff,
  forall_memory_terms m (valid_addresses m) ->
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

(* -------------------------------------------------------------------------- *)
(* mem-va-preservation                                                        *)
(* -------------------------------------------------------------------------- *)

Local Lemma hasad_alloc_term : forall t t' ad ad' v V,
  HasAddress ad v ->
  t --[EF_Alloc ad' v V]--> t' ->
  HasAddress ad t.
Proof. intros. induction_step; eauto using HasAddress. Qed.

Local Lemma step_alloc_mem_va_preservation : forall m t t' v V,
  valid_addresses m t ->
  forall_memory_terms m (valid_addresses m) ->
  t --[EF_Alloc (length m) v V]--> t' ->
  forall_memory_terms  (m +++ (v, V)) (valid_addresses (m +++ (v, V))).
Proof.
  intros. intros ad. decompose sum (lt_eq_lt_dec ad (length m)); subst;
  simpl_array; intros ? ?; rewrite add_increments_length;
  unfold valid_addresses in *; eauto using hasad_alloc_term, Nat.lt_lt_succ_r.
  simpl in *. inversion_ha.
Qed.

Local Lemma step_write_mem_va_preservation : forall m t t' ad v V,
  valid_addresses m t ->
  forall_memory_terms m (valid_addresses m) ->
  t --[EF_Write ad v V]--> t' ->
  forall_memory_terms m[ad <- (v, V)] (valid_addresses m[ad <- (v, V)]).
Proof.
  intros. intros ad'. 
  assert (HasAddress ad t); assert (ad < length m);
  eauto using step_write_hasad1.
  destruct (Nat.eq_dec ad ad'); subst; simpl_array;
  intros ? ?; rewrite set_preserves_length;
  eauto using step_write_hasad2, Nat.lt_lt_succ_r.
  unfold valid_addresses in *. eauto.
Qed.

Local Corollary mstep_mem_va_preservation : forall m m' t t' eff,
  valid_addresses m t ->
  forall_memory_terms m (valid_addresses m) ->
  m / t ==[eff]==> m' / t' ->
  forall_memory_terms m' (valid_addresses m').
Proof.
  intros. inversion_mstep; trivial;
  eauto using step_alloc_mem_va_preservation, step_write_mem_va_preservation.
Qed.

(* -------------------------------------------------------------------------- *)
(* main theorems                                                              *)
(* -------------------------------------------------------------------------- *)

Local Lemma va_spawn_block : forall m t t' block,
  valid_addresses m t ->
  t --[EF_Spawn block]--> t' ->
  valid_addresses m block.
Proof.
  intros. induction_step; inversion_va; eauto.
Qed.

Theorem valid_addresses_preservation1 : forall m m' ths ths' tid eff,
  forall_memory_terms m (valid_addresses m) ->
  forall_threads ths (valid_addresses m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_threads ths' (valid_addresses m').
Proof.
  intros. inversion_cstep; intros tid'.
  - destruct (Nat.eq_dec tid tid'); subst; simpl_array;
    eauto using mstep_va_preservation. intros ? ?.
    unfold valid_addresses in *. inversion_mstep;
    try (rewrite add_increments_length || rewrite set_preserves_length);
    eauto using Nat.lt_lt_succ_r.
  - decompose sum (lt_eq_lt_dec tid' (length ths[tid <- t'])); subst;
    simpl_array; eauto using va_unit, va_spawn_block.
    destruct (Nat.eq_dec tid tid'); subst; simpl_array;
    eauto using step_spawn_va_preservation.
Qed.

Theorem valid_addresses_preservation2 : forall m m' ths ths' tid eff,
  forall_threads ths (valid_addresses m) ->
  forall_memory_terms m (valid_addresses m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_memory_terms m' (valid_addresses m').
Proof.
  intros. inversion_cstep; eauto using mstep_mem_va_preservation.
Qed.

