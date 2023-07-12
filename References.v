From Coq Require Import Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import HasAddress.
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
    well_typed_references m <{ fn x Tx --> t }>

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
  | H : well_typed_references _ <{ unit         }> |- _ => inversion H
  | H : well_typed_references _ <{ N _          }> |- _ => inversion H
  | H : well_typed_references _ <{ & _ :: _     }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ new _ _      }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ * _          }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ _ = _        }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ var _        }> |- _ => inversion H
  | H : well_typed_references _ <{ fn _ _ --> _ }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ call _ _     }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ _ ; _        }> |- _ => inversion H; subst
  | H : well_typed_references _ <{ spawn _      }> |- _ => inversion H; subst
  end.

Ltac inversion_clear_wtr :=
  match goal with
  |H: well_typed_references _ <{ unit         }> |- _ => inversion H
  |H: well_typed_references _ <{ N _          }> |- _ => inversion H
  |H: well_typed_references _ <{ & _ :: _     }> |- _ => inversion_subst_clear H
  |H: well_typed_references _ <{ new _ _      }> |- _ => inversion_subst_clear H
  |H: well_typed_references _ <{ * _          }> |- _ => inversion_subst_clear H
  |H: well_typed_references _ <{ _ = _        }> |- _ => inversion_subst_clear H
  |H: well_typed_references _ <{ var _        }> |- _ => inversion H
  |H: well_typed_references _ <{ fn _ _ --> _ }> |- _ => inversion_subst_clear H
  |H: well_typed_references _ <{ call _ _     }> |- _ => inversion_subst_clear H
  |H: well_typed_references _ <{ _ ; _        }> |- _ => inversion_subst_clear H
  |H: well_typed_references _ <{ spawn _      }> |- _ => inversion_subst_clear H
  end.

(* ------------------------------------------------------------------------- *)
(* preservation helpers                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma subst_wtr : forall m x Tx t v,
  well_typed_references m v ->
  well_typed_references m <{ fn x Tx --> t }> ->
  well_typed_references m ([x := v] t).
Proof.
  intros. inversion_clear_wtr.
  induction t; inversion_wtr; eauto using well_typed_references;
  simpl; destruct String.string_dec; eauto using well_typed_references.
Qed.

Local Lemma mem_add_wtr : forall m t v Tr,
  valid_addresses m t ->
  well_typed_references m t ->
  well_typed_references (m +++ (v, Tr)) t.
Proof.
  intros * ? Hwtr.
  induction Hwtr; try inversion_vad; eauto using well_typed_references;
  (eapply wtr_refM || eapply wtr_refI); simpl_array; assumption.
Qed.

Local Lemma mem_set_wtr : forall m t ad v V,
  ad < #m ->
  empty |-- v is V ->
  empty |-- m[ad].tm is V ->
  well_typed_references m t ->
  well_typed_references m[ad <- (v, m[ad].typ)] t.
Proof.
  intros * ? ? ? Hwtr. rename ad into ad'. 
  induction Hwtr; eauto using well_typed_references;
  (eapply wtr_refM || eapply wtr_refI);
  decompose sum (lt_eq_lt_dec ad' ad); subst;
  simpl_array; trivial; apply_deterministic_typing; trivial.
Qed.

Lemma step_spawn_wtr_block : forall m t t' block,
  well_typed_references m t ->
  t --[EF_Spawn block]--> t' ->
  well_typed_references m block.
Proof.
  intros. induction_step; inversion_wtr; eauto using well_typed_references.
Qed.

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
(* term preservation                                                         *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_none_wtr_preservation : forall m t t',
  well_typed_references m t ->
  t --[EF_None]--> t' ->
  well_typed_references m t'.
Proof.
  intros. induction_step; inversion_wtr;
  eauto using subst_wtr, well_typed_references.
Qed.

Local Lemma step_alloc_wtr_preservation : forall m t t' v Tr T,
  empty |-- t is T ->
  valid_addresses m t ->
  well_typed_references m t ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  well_typed_references (m +++ (v, Tr)) t'.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_vad; inversion_type; inversion_wtr;
  eauto using mem_add_wtr, well_typed_references;
  (eapply wtr_refM || eapply wtr_refI); simpl_array; trivial.
Qed.

Local Lemma step_read_wtr_preservation : forall m t t' ad,
  forall_memory m (well_typed_references m) ->
  well_typed_references m t ->
  t --[EF_Read ad m[ad].tm]--> t' ->
  well_typed_references m t'.
Proof.
  intros. induction_step; inversion_wtr; eauto using well_typed_references.
Qed.

Local Lemma step_write_wtr_preservation : forall m t t' ad v Tr T,
  empty |-- t is T ->
  valid_addresses m t ->
  well_typed_references m t ->
  t --[EF_Write ad v Tr]--> t' ->
  well_typed_references m[ad <- (v, Tr)] t'.
Proof.
  intros * ? Hva. intros.
  assert (ad < #m) by eauto using step_write_hasad1.
  assert (
    Tr = m[ad].typ /\
    exists V, empty |-- v is V /\ empty |-- m[ad].tm is V)
    as [? [? [? ?]]] by eauto using step_write_wtt.
  generalize dependent T.
  induction_step; intros; inversion_type; inversion_vad; inversion_wtr;
  eauto using mem_set_wtr, well_typed_references.
Qed.

Local Corollary mstep_wtr_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  valid_addresses m t ->
  well_typed_references m t ->
  forall_memory m (well_typed_references m) ->
  m / t ==[eff]==> m' / t' ->
  well_typed_references m' t'.
Proof.
  intros. inversion_mstep;
  eauto using step_none_wtr_preservation,
    step_alloc_wtr_preservation,
    step_read_wtr_preservation,
    step_write_wtr_preservation.
Qed.

Lemma step_spawn_wtr_preservation : forall m t t' block,
  well_typed_references m t ->
  t --[EF_Spawn block]--> t' ->
  well_typed_references m t'.
Proof.
  intros. induction_step; inversion_wtr; eauto using well_typed_references.
Qed.

(* ------------------------------------------------------------------------- *)
(* memory preservation                                                       *)
(* ------------------------------------------------------------------------- *)

Local Lemma step_alloc_wtt_value : forall t t' ad v Tr T,
  empty |-- t is T ->
  t --[EF_Alloc ad v Tr]--> t' ->
  exists V, empty |-- v is V.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_type; eauto.
Qed.

Local Lemma step_alloc_wtr_value : forall m t t' ad v Tr,
  well_typed_references m t ->
  t --[EF_Alloc ad v Tr]--> t' ->
  well_typed_references m v.
Proof.
  intros. induction_step; intros; inversion_wtr; eauto.
Qed.

Local Lemma step_write_wtr_value : forall m t t' ad v Tr,
  well_typed_references m t ->
  t --[EF_Write ad v Tr]--> t' ->
  well_typed_references m v.
Proof.
  intros. induction_step; intros; inversion_wtr; eauto.
Qed.

Local Lemma mstep_mem_wtr_preservation : forall m m' t t' eff T,
  empty |-- t is T ->
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  well_typed_references m t ->
  forall_memory m well_typed ->
  forall_memory m (well_typed_references m) ->
  m / t ==[eff]==> m' / t' ->
  forall_memory m' (well_typed_references m').
Proof.
  intros * ? ? ? ? Hwtt ? ?. inversion_mstep; trivial;
  intros ad'; specialize (Hwtt ad').
  - assert (exists V, empty |-- v is V) as [? ?]
      by eauto using step_alloc_wtt_value.
    decompose sum (lt_eq_lt_dec ad' (#m)); subst;
    simpl_array; eauto using well_typed_references;
    eauto using step_alloc_wtr_value, mem_add_wtr, well_typed_term.
  - match goal with
    | _ : _ --[EF_Write _ _ ?T]--> _ |- _ => rename T into T'
    end.
    assert (
      T' = m[ad].typ /\
      exists V, empty |-- v is V /\ empty |-- m[ad].tm is V)
      as [? [? [? ?]]] by eauto using step_write_wtt.
    decompose sum (lt_eq_lt_dec ad' ad); subst;
    simpl_array;
    eauto using step_write_wtt, step_write_wtr_value, mem_set_wtr.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem well_typed_references_term_preservation : forall m m' ths ths' tid eff,
  forall_threads ths well_typed ->
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  forall_program m ths (well_typed_references m) ->
  m / ths ~~[tid, eff]~~> m' / ths' ->
  forall_threads ths' (well_typed_references m').
Proof.
  intros * Htype ? [? ?]. intros. eapply cstep_preservation; eauto; intros.
  - destruct (Htype tid'). eauto using mstep_wtr_preservation.
  - inversion_mstep; eauto using mem_add_wtr.
    destruct (Htype tid).
    match goal with
    | _ : _ --[EF_Write _ _ ?T]--> _ |- _ => rename T into T'
    end.
    assert (
      T' = m[ad].typ /\
      exists V, empty |-- v is V /\ empty |-- m[ad].tm is V)
      as [Heq [? [? ?]]] by eauto using step_write_wtt.
    rewrite Heq in *. eauto using mem_set_wtr.
  - eauto using step_spawn_wtr_block.
  - eauto using step_spawn_wtr_preservation.
  - eauto using well_typed_references.
Qed.

Theorem well_typed_references_memory_preservation :
  forall m m' ths ths' tid eff,
    forall_program m ths well_typed ->
    forall_program m ths (valid_addresses m) ->
    (* --- *)
    forall_program m ths (well_typed_references m) ->
    m / ths ~~[tid, eff]~~> m' / ths' ->
    forall_memory m' (well_typed_references m').
Proof.
  intros * [? Htype] [? ?] [? ?]. intros. inversion_clear_cstep; trivial.
  destruct (Htype tid). eauto using mstep_mem_wtr_preservation.
Qed.

