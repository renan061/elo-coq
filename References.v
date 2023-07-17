From Coq Require Import Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import Meta.
From Elo Require Import ValidAddresses.

(* ------------------------------------------------------------------------- *)
(* well-typed-references                                                     *)
(* ------------------------------------------------------------------------- *)

Inductive well_typed_references (m : mem) : tm -> Prop :=
  | wtr_unit :
    well_typed_references m <{ unit }> 

  | wtr_num : forall n,
    well_typed_references m <{ N n }>

  | wtr_refM : forall T ad,
    empty |-- m[ad].tm is T ->
    m[ad].typ = <{{ &T }}> ->
    well_typed_references m <{ &ad :: &T }>

  | wtr_refI : forall T ad,
    empty |-- m[ad].tm is <{{ Immut T }}> ->
    m[ad].typ = <{{ i&T }}> ->
    well_typed_references m <{ &ad :: i&T }>

  | wtr_new : forall T t,
    well_typed_references m t ->
    well_typed_references m <{ new T t }> 

  | wtr_load : forall t,
    well_typed_references m t ->
    well_typed_references m <{ *t }> 

  | wtr_asg : forall t1 t2,
    well_typed_references m t1 ->
    well_typed_references m t2 ->
    well_typed_references m <{ t1 = t2 }> 

  | wtr_var : forall x,
    well_typed_references m <{ var x }>

  | wtr_fun : forall x Tx t,
    well_typed_references m t ->
    well_typed_references m <{ fn x Tx t }>

  | wtr_call : forall t1 t2,
    well_typed_references m t1 ->
    well_typed_references m t2 ->
    well_typed_references m <{ call t1 t2 }> 

  | wtr_seq : forall t1 t2,
    well_typed_references m t1 ->
    well_typed_references m t2 ->
    well_typed_references m <{ t1; t2 }>

  | wtr_spawn : forall t,
    well_typed_references m t ->
    well_typed_references m <{ spawn t }>
  .

Ltac inversion_wtr :=
  match goal with
  | H : well_typed_references _ <{ unit     }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ N _      }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ & _ :: _ }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ new _ _  }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ * _      }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ _ = _    }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ var _    }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ fn _ _ _ }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ call _ _ }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ _ ; _    }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ spawn _  }> |- _ => inversion H; subst
  end.

Ltac inversion_clear_wtr :=
  match goal with
  | H : well_typed_references _ <{ unit     }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ N _      }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ & _ :: _ }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ new _ _  }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ * _      }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ _ = _    }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ var _    }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ fn _ _ _ }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ call _ _ }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ _ ; _    }> |- _ => inversion_subst_clear H
  | H : well_typed_references _ <{ spawn _  }> |- _ => inversion_subst_clear H
  end.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

(* Auxiliary. *)
Local Lemma step_write_wtt : forall m t t' ad v Tr T,
  empty |-- t is T ->
  t --[EF_Write ad v Tr]--> t' ->
  well_typed_references m t ->
  (Tr = m[ad].typ /\ exists V, empty |-- v is V /\ empty |-- m[ad].tm is V).
Proof.
  intros * ? ?.
  assert (exists V, empty |-- v is V) as [? ?].
  { generalize dependent T. induction_step; intros; inversion_type; eauto. }
  intros. generalize dependent T.
  induction_step; intros; inversion_type; inversion_wtr; eauto.
  inversion_type. inversion_wtr. apply_deterministic_typing. eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma wtr_subst_preservation : forall m t tx x,
  well_typed_references m t ->
  well_typed_references m tx ->
  well_typed_references m ([x := tx] t).
Proof.
  intros. induction t; inversion_wtr; eauto using well_typed_references;
  simpl; destruct string_eq_dec; subst; eauto using well_typed_references.
Qed.

Local Lemma wtr_mem_add_preservation : forall m t vT,
  valid_addresses m t ->
  well_typed_references m t ->
  well_typed_references (m +++ vT) t.
Proof.
  intros * ? Hwtr. induction Hwtr;
  try inversion_vad; eauto using well_typed_references;
  (eapply wtr_refM || eapply wtr_refI); simpl_array; assumption.
Qed.

Local Lemma wtr_mem_set_preservation : forall m t ad v T,
  ad < #m ->
  empty |-- v is T ->
  empty |-- m[ad].tm is T ->
  well_typed_references m t ->
  well_typed_references m[ad <- (v, m[ad].typ)] t.
Proof.
  intros * ? ? ? Hwtr. rename ad into ad'. 
  induction Hwtr; eauto using well_typed_references;
  (eapply wtr_refM || eapply wtr_refI);
  decompose sum (lt_eq_lt_dec ad' ad); subst;
  simpl_array; trivial; apply_deterministic_typing; trivial.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma wtr_tstep_none_preservation : forall m t t',
  well_typed_references m t ->
  t --[EF_None]--> t' ->
  well_typed_references m t'.
Proof.
  intros. induction_step; inversion_wtr; eauto using well_typed_references.
  inversion_wtr. eauto using wtr_subst_preservation.
Qed.

Local Lemma wtr_tstep_alloc_preservation : forall m t t' v T,
  well_typed_term t ->
  valid_addresses m t ->
  well_typed_references m t ->
  t --[EF_Alloc (#m) v T]--> t' ->
  well_typed_references (m +++ (v, T)) t'.
Proof.
  intros * [T' ?]. intros. generalize dependent T'.
  induction_step; intros; inversion_vad; inversion_type; inversion_wtr;
  eauto using well_typed_references, wtr_mem_add_preservation;
  (eapply wtr_refM || eapply wtr_refI); simpl_array; trivial.
Qed.

Local Lemma wtr_tstep_read_preservation : forall m t t' ad v,
  well_typed_references m v ->
  well_typed_references m t ->
  t --[EF_Read ad v]--> t' ->
  well_typed_references m t'.
Proof.
  intros. induction_step; inversion_wtr; eauto using well_typed_references.
Qed.

Local Lemma wtr_tstep_write_preservation : forall m t t' ad v T,
  well_typed_term t ->
  valid_addresses m t ->
  well_typed_references m t ->
  t --[EF_Write ad v T]--> t' ->
  well_typed_references m[ad <- (v, T)] t'.
Proof.
  intros * [T' ?]. intros. assert (
    T = m[ad].typ /\
    exists Tv, empty |-- v is Tv /\ empty |-- m[ad].tm is Tv)
    as [? [? [? ?]]] by eauto using step_write_wtt.
  generalize dependent T'.
  induction_step; intros; inversion_type; inversion_vad; inversion_wtr;
  eauto using valid_address_write,
    well_typed_references,
    wtr_mem_set_preservation.
Qed.

Local Lemma wtr_tstep_spawn_preservation : forall m t t' block,
  well_typed_references m t ->
  t --[EF_Spawn block]--> t' ->
  well_typed_references m t'.
Proof.
  intros. induction_step; inversion_wtr; eauto using well_typed_references.
Qed.

Local Corollary wtr_mstep_preservation : forall m m' t t' e,
  well_typed_term t ->
  valid_addresses m t ->
  forall_memory m (well_typed_references m) ->
  well_typed_references m t ->
  m / t ==[e]==> m' / t' ->
  well_typed_references m' t'.
Proof.
  intros * ? ?. eapply mstep_preservation; (* optimization *)
  eauto using wtr_tstep_none_preservation,
    wtr_tstep_alloc_preservation,
    wtr_tstep_read_preservation,
    wtr_tstep_write_preservation.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma wtr_thread_default_preservation : forall m,
  well_typed_references m thread_default.
Proof.
  eauto using well_typed_references.
Qed.

Local Lemma wtr_spawn_block_preservation : forall m t t' block,
  well_typed_references m t ->
  t --[EF_Spawn block]--> t' ->
  well_typed_references m block.
Proof.
  intros. induction_step; inversion_wtr; eauto.
Qed.

Local Lemma wtr_untouched_threads_preservation : forall m m' ths tid tid' e t',
  forall_threads ths well_typed_term ->
  forall_threads ths (valid_addresses m) ->
  forall_threads ths (well_typed_references m) ->
  tid <> tid' ->
  tid' < #ths ->
  m / ths[tid] ==[e]==> m' / t' ->
  well_typed_references m' ths[tid'].
Proof.
  intros *. intros Htype. intros. destruct (Htype tid).
  inversion_mstep; eauto using wtr_mem_add_preservation.
  match goal with
  | _ : _ --[EF_Write _ _ ?T]--> _ |- _ =>
    assert (
      T = m[ad].typ /\
      exists V, empty |-- v is V /\ empty |-- m[ad].tm is V)
      as [Heq [? [? ?]]] by eauto using step_write_wtt
  end.
  rewrite Heq in *. eauto using wtr_mem_set_preservation.
Qed.

Local Corollary wtr_cstep_preservation : forall m m' ths ths' tid e,
  forall_threads ths well_typed_term ->
  forall_threads ths (valid_addresses m) ->
  forall_memory m (well_typed_references m) ->
  forall_threads ths (well_typed_references m) ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  forall_threads ths' (well_typed_references m').
Proof.
  intros * Htype ?. destruct (Htype tid).
  eauto 6 using cstep_preservation,
    wtr_tstep_spawn_preservation,
    wtr_mstep_preservation,
    wtr_thread_default_preservation,
    wtr_spawn_block_preservation,
    wtr_untouched_threads_preservation.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma wtt_alloc_value_generalization : forall t t' ad v T,
  well_typed_term t ->
  t --[EF_Alloc ad v T]--> t' ->
  well_typed_term v.
Proof.
  unfold well_typed_term. intros * [T' ?]. intros. generalize dependent T'.
  induction_step; intros; inversion_type; eauto.
Qed.

Local Lemma wtr_alloc_value_generalization : forall m t t' ad v T,
  well_typed_references m t ->
  t --[EF_Alloc ad v T]--> t' ->
  well_typed_references m v.
Proof.
  intros. induction_step; intros; inversion_wtr; eauto.
Qed.

Local Lemma wtr_write_value_generalization : forall m t t' ad v T,
  well_typed_references m t ->
  t --[EF_Write ad v T]--> t' ->
  well_typed_references m v.
Proof.
  intros. induction_step; intros; inversion_wtr; eauto.
Qed.

Local Lemma wtr_tstep_alloc_mem_preservation : forall m t t' v T,
  well_typed_term t ->
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  well_typed_references m t ->
  forall_memory m (well_typed_references m) ->
  t --[EF_Alloc (#m) v T]--> t' ->
  forall_memory (m +++ (v, T)) (well_typed_references (m +++ (v, T))).
Proof.
  intros. intros ad.
  assert (well_typed_term v) as [? ?]
    by eauto using wtt_alloc_value_generalization.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
  eauto using well_typed_references; (* optimization *)
  eauto using wtr_mem_add_preservation, wtr_alloc_value_generalization.
Qed.

Local Lemma wtr_tstep_write_mem_preservation : forall m t t' ad v T,
  well_typed_term t ->
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  well_typed_references m t ->

  well_typed_references m t ->
  forall_memory m (well_typed_references m) ->
  t --[EF_Write ad v T]--> t' ->
  forall_memory m[ad <- (v, T)] (well_typed_references m[ad <- (v, T)]).
Proof.
  intros * [? ?]. intros.
  match goal with
  | _ : _ --[EF_Write ?ad' _ ?T']--> _ |- _ =>
    assert (
      T' = m[ad'].typ /\
      exists Tv, empty |-- v is Tv /\ empty |-- m[ad'].tm is Tv)
      as [? [? [? ?]]] by eauto using step_write_wtt
  end.
  intros ad'. decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array;
  eauto using step_write_wtt,
    wtr_write_value_generalization,
    wtr_mem_set_preservation.
Qed.

Local Lemma wtr_mstep_mem_preservation : forall m m' t t' e,
  well_typed_term t ->
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  well_typed_references m t ->
  forall_memory m well_typed_term ->
  forall_memory m (well_typed_references m) ->
  m / t ==[e]==> m' / t' ->
  forall_memory m' (well_typed_references m').
Proof.
  intros * Hwtt1 ? ? ? Hwtt2 ? ?. inversion_mstep;
  eauto using wtr_tstep_alloc_mem_preservation.

Qed.

(* ------------------------------------------------------------------------- *)

Theorem well_typed_references_memory_preservation :
  forall m m' ths ths' tid e,
    forall_program m ths well_typed_term ->
    forall_program m ths (valid_addresses m) ->
    (* --- *)
    forall_program m ths (well_typed_references m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_memory m' (well_typed_references m').
Proof.
  intros * [? Htype] [? ?] [? ?]. intros. inversion_clear_cstep; trivial.
  destruct (Htype tid). eauto using mstep_mem_wtr_preservation.
Qed.

