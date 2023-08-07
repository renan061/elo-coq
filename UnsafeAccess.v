From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import ValidAddresses.
From Elo Require Import References.
From Elo Require Import AccessCore.
From Elo Require Import NotAccess.

(* ------------------------------------------------------------------------- *)
(* unsafe-access                                                             *)
(* ------------------------------------------------------------------------- *)

(* There is a mutable pointer to <ad> in the term. *)
Inductive unsafe_access (ad : addr) (m : mem) : tm  -> Prop :=
  | uacc_mem : forall ad' T,
    ad <> ad' ->
    unsafe_access ad m (m[ad'].tm) ->
    unsafe_access ad m <{&ad' :: &T}>

  | uacc_ad : forall T,
    unsafe_access ad m <{&ad :: &T}>

  | uacc_new : forall T t,
    unsafe_access ad m t ->
    unsafe_access ad m <{new T t}>

  | uacc_load : forall t,
    unsafe_access ad m t ->
    unsafe_access ad m <{*t}>

  | uacc_asg1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{t1 = t2}>

  | uacc_asg2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{t1 = t2}>

  | uacc_fun : forall x Tx t,
    unsafe_access ad m t ->
    unsafe_access ad m <{fn x Tx t}>

  | uacc_call1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{call t1 t2}>

  | uacc_call2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{call t1 t2}>

  | uacc_seq1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{t1; t2}>

  | uacc_seq2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{t1; t2}>
  .

(* ------------------------------------------------------------------------- *)
(* unsafe-access inversion                                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_uacc tactic :=
  match goal with
  | H : unsafe_access _ _ thread_default |- _ => tactic H
  | H : unsafe_access _ _ <{unit    }>   |- _ => tactic H
  | H : unsafe_access _ _ <{N _     }>   |- _ => tactic H
  | H : unsafe_access _ _ <{& _ :: _}>   |- _ => tactic H
  | H : unsafe_access _ _ <{new _ _ }>   |- _ => tactic H
  | H : unsafe_access _ _ <{* _     }>   |- _ => tactic H
  | H : unsafe_access _ _ <{_ = _   }>   |- _ => tactic H
  | H : unsafe_access _ _ <{var _   }>   |- _ => tactic H
  | H : unsafe_access _ _ <{fn _ _ _}>   |- _ => tactic H
  | H : unsafe_access _ _ <{call _ _}>   |- _ => tactic H
  | H : unsafe_access _ _ <{_ ; _   }>   |- _ => tactic H
  | H : unsafe_access _ _ <{spawn _ }>   |- _ => tactic H
  end.

Ltac inv_uacc := match_uacc inv.

Ltac inv_clear_uacc := match_uacc inv_clear.

(* ------------------------------------------------------------------------- *)
(* unsafe-access dec                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma uacc_dec : forall m t ad,
  Decidable.decidable (unsafe_access ad m t).
Proof. eauto using classic_decidable. Qed.

(* ------------------------------------------------------------------------- *)
(* unsafe-access inheritance                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma uacc_mem_add_inheritance : forall m t ad vT,
  ~ access (#m) m t ->
  unsafe_access ad (m +++ vT) t ->
  unsafe_access ad m t.
Proof.
  intros * Hnacc Huacc. induction Huacc; subst; inv_nacc Hnacc;
  eauto using unsafe_access.
  eapply uacc_mem; trivial.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; eauto; lia.
Qed.

Lemma uacc_mem_set_inheritance : forall m t ad ad' vT,
  ~ access ad' m t ->
  unsafe_access ad m[ad' <- vT] t ->
  unsafe_access ad m t.
Proof.
  intros * Hnacc Huacc. induction Huacc; inv_nacc Hnacc;
  eauto using unsafe_access. simpl_array. eauto using unsafe_access.
Qed.

Local Lemma uacc_tstep_spawn_inheritance : forall m t t' block ad,
  unsafe_access ad m t' ->
  t --[EF_Spawn block]--> t' ->
  unsafe_access ad m t.
Proof.
  intros. induction_step; inv_uacc; eauto using unsafe_access.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-unsafe-access inversion                                               *)
(* ------------------------------------------------------------------------- *)

Lemma nuacc_unit : forall m ad,
  ~ unsafe_access ad m <{unit}>.
Proof. intros * ?. inv_uacc. Qed.

Local Ltac solve_nuacc_inversion :=
  intros; try (split; intros); eauto using unsafe_access.

Local Lemma inv_nuacc_mem : forall m ad ad' T,
  ad <> ad' ->
  ~ unsafe_access ad m <{&ad' :: &T}> ->
  ~ unsafe_access ad m (m[ad'].tm).
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_new : forall m t ad T,
  ~ unsafe_access ad m <{new T t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_load : forall m t ad,
  ~ unsafe_access ad m <{*t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_asg : forall m t1 t2 ad,
  ~ unsafe_access ad m <{t1 = t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_fun : forall m t ad x Tx,
  ~ unsafe_access ad m <{fn x Tx t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_call : forall m t1 t2 ad,
  ~ unsafe_access ad m <{call t1 t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_seq : forall m t1 t2 ad,
  ~ unsafe_access ad m <{t1; t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc_inversion. Qed.

Ltac inv_nuacc :=
  match goal with
  | H : ~ unsafe_access ?ad _ <{ & ?ad' ::   _ }>, Hneq : ?ad <> ?ad' |- _ =>
    eapply (inv_nuacc_mem _ _ _ _ Hneq) in H
  | H : ~ unsafe_access ?ad _ <{ & ?ad  :: & _ }> |- _ =>
    contradict H; eauto using unsafe_access
  | H : ~ unsafe_access _ _   <{ new _ _       }> |- _ =>
    eapply inv_nuacc_new  in H
  | H : ~ unsafe_access _ _   <{ * _           }> |- _ =>
    eapply inv_nuacc_load in H
  | H : ~ unsafe_access _ _   <{ _ = _         }> |- _ =>
    eapply inv_nuacc_asg  in H as [? ?]
  | H : ~ unsafe_access _ _   <{ fn _ _ _      }> |- _ =>
    eapply inv_nuacc_fun  in H
  | H : ~ unsafe_access _ _   <{ call _ _      }> |- _ =>
    eapply inv_nuacc_call in H as [? ?]
  | H : ~ unsafe_access _ _   <{ _ ; _         }> |- _ =>
    eapply inv_nuacc_seq  in H as [? ?]
  end.

(* ------------------------------------------------------------------------- *)
(* important properties and lemmas                                           *)
(* ------------------------------------------------------------------------- *)

(* unsafe-access ----------------------------------------------------------- *)

Local Theorem uacc_soundness : forall m m' t t' ad e T,
  ad < #m ->
  empty |-- t is T ->
  ~ unsafe_access ad m t ->
  m / t ==[e]==> m' / t' ->
  m[ad].tm = m'[ad].tm.
Proof.
  intros. rename ad into ad'. inversion_clear_mstep; trivial.
  - decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; trivial. lia.
  - decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array; trivial.
    generalize dependent T.
    induction_step; intros; inversion_type; inv_nuacc; eauto.
    inversion_type. exfalso. eauto using unsafe_access.
Qed.

Lemma uacc_then_acc : forall m t ad,
  unsafe_access ad m t ->
  access ad m t.
Proof.
  intros * Huacc. induction Huacc; eauto using access.
Qed.

Theorem immutable_reference_then_nuacc : forall m ad v T,
  value v ->
  empty |-- v is <{{Immut T}}> ->
  unsafe_access ad m v ->
  False.
Proof.
  intros * Hval ? ?. destruct Hval;
  inversion_type; inv_uacc; eauto using unsafe_access.
Qed.

Local Lemma nuacc_from_nacc : forall m t ad,
  ~ access ad m t ->
  ~ unsafe_access ad m t.
Proof.
  intros * ? Huacc. induction Huacc; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-unsafe-access preservation                                            *)
(* ------------------------------------------------------------------------- *)

Local Lemma nuacc_subst_preservation : forall m t tx ad x,
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m tx ->
  ~ unsafe_access ad m ([x := tx] t).
Proof.
  intros. intros ?. induction t; eauto; simpl in *;
  try (destruct string_eq_dec; eauto);
  inv_uacc; inv_nuacc; eauto.
Qed.

Lemma nuacc_mem_add_preservation  : forall m t ad vT,
  ~ unsafe_access (#m) m t ->
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad (m +++ vT) t.
Proof.
  intros. intros Huacc. induction Huacc; inv_nuacc; eauto using unsafe_access.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; simpl in *;
  try inv_uacc; eauto using unsafe_access.
  assert (#m <> ad') by eauto using Nat.lt_neq, Nat.neq_sym.
  inv_nuacc. eauto.
Qed.

Lemma nuacc_mem_set_preservation : forall m t ad ad' v T,
  ~ unsafe_access ad m v ->
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m[ad' <- (v, T)] t.
Proof.
  assert (forall m ad ad' v T,
    unsafe_access ad m[ad' <- (v, T)] m[ad' <- (v, T)][ad'].tm -> ad' < #m). {
      intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
      rewrite (get_set_invalid memory_default) in H; trivial. inversion H.
  }
  (* main proof *)
  intros * ? ? Huacc. induction Huacc; eauto using unsafe_access.
  match goal with _ : _ <> ?ad |- _ => rename ad into ad'' end. 
  destruct (nat_eq_dec ad' ad''); subst;
  try (assert (ad'' < #m) by eauto);
  simpl_array; eauto using unsafe_access.
Qed.

(* alternative for mem_set ------------------------------------------------- *)

Lemma alt_nuacc_mem_set_preservation : forall m t ad ad' vT,
  ~ unsafe_access ad' m t ->
  ~ unsafe_access ad m t ->
  ~ unsafe_access ad m[ad' <- vT] t.
Proof.
  intros * ? ? Huacc.
  induction Huacc; inv_nuacc;
  try solve [inv_nuacc; eauto].
  match goal with Hneq : _ <> ?ad |- _ =>
    destruct (nat_eq_dec ad' ad); subst
  end; inv_nuacc. simpl_array. eauto.
Qed.

(* tstep ------------------------------------------------------------------- *)

Lemma nuacc_tstep_none_preservation : forall m t t' ad,
  ~ unsafe_access ad m t ->
  t --[EF_None]--> t' ->
  ~ unsafe_access ad m t'.
Proof.
  intros. induction_step; inv_nuacc; trivial;
  try solve [do 2 auto_specialize; intros ?; inv_uacc; eauto].
  inv_nuacc. eauto using nuacc_subst_preservation. 
Qed.

Lemma nuacc_tstep_alloc_preservation : forall m t t' ad v T,
  ad < #m ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ unsafe_access ad m t ->
  t --[EF_Alloc (#m) v T]--> t' ->
  ~ unsafe_access ad (m +++ (v, T)) t'.
Proof.
  intros. intros ?. induction_step; inversion_vad; inv_nuacc; inv_clear_uacc;
  eauto; try lia;
  match goal with F : unsafe_access _ (_ +++ _) _ |- _ => contradict F end;
  try simpl_array;
  eauto using nacc_vad_length, nuacc_from_nacc, nuacc_mem_add_preservation.
Qed.

Lemma nuacc_tstep_read_preservation : forall m t t' ad ad' T,
  forall_memory m value ->
  empty |-- t is T ->
  consistently_typed_references m t ->
  ~ unsafe_access ad m t ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  ~ unsafe_access ad m t'.
Proof.
  intros. intros ?. generalize dependent T.
  induction_step; intros;
  inversion_type; inversion_ctr; inv_nuacc; try inv_clear_uacc; eauto;
  inversion_type; destruct (nat_eq_dec ad' ad); subst;
  eauto using unsafe_access;
  inversion_ctr;
  match goal with F : unsafe_access _ _ _[_].tm |- _ => contradict F end;
  eauto using immutable_reference_then_nuacc.
Qed.

Lemma nuacc_tstep_write_preservation : forall m t t' ad ad' v T,
  ~ unsafe_access ad m t ->
  t --[EF_Write ad' v T]--> t' ->
  ~ unsafe_access ad m[ad' <- (v, T)] t'.
Proof.
  assert (forall m t t' ad ad' v T,
    ~ unsafe_access ad m t ->
    t --[EF_Write ad' v T]--> t' ->
    ~ unsafe_access ad m v)
    by (intros; induction_step; eauto using unsafe_access).
  (* main proof *)
  intros. intros ?. induction_step; inv_nuacc; inv_clear_uacc; eauto;
  match goal with _ : unsafe_access _ _ ?t |- _ => rename t into tx end;
  eapply (nuacc_mem_set_preservation _ tx _ _ v); eauto.
Qed.

Lemma nuacc_tstep_spawn_preservation : forall m t t' ad block,
  ~ unsafe_access ad m t ->
  t --[EF_Spawn block]--> t' ->
  ~ unsafe_access ad m t'.
Proof.
  intros. intros ?. induction_step; try inv_nuacc; inv_uacc; eauto.
Qed.

Local Corollary nuacc_mstep_preservation : forall m m' t t' e ad T,
  forall_memory m value ->
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  empty |-- t is T ->
  consistently_typed_references m t ->
  (* --- *)
  ad < #m ->
  ~ unsafe_access ad m t ->
  m / t ==[e]==> m' / t' ->
  ~ unsafe_access ad m' t'.
Proof.
  intros. inversion_mstep;
  eauto using nuacc_tstep_none_preservation,
    nuacc_tstep_alloc_preservation,
    nuacc_tstep_read_preservation,
    nuacc_tstep_write_preservation.
Qed.

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma memtyp_mstep_nuacc_then_immut : forall m m' t t' e T,
  empty |-- t is T ->
  (* --- *)
  m / t ==[e]==> m' / t' ->
  #m' > #m ->
  ~ unsafe_access (#m) m' t' ->
  exists Tm, m'[#m].typ = <{{i&Tm}}>.
Proof.
  intros * ? ? Hlen. intros. inversion_clear_mstep;
  try rewrite set_preserves_length in Hlen; try lia.
  simpl_array. simpl. generalize dependent T.
  induction_step; intros; inversion_type; try inv_nuacc; eauto;
  try match goal with
  | _ : ?t --[_]--> _ , H : _ |-- ?t is _ |- _ =>
    specialize (IHtstep _ H) as [? ?]; eauto
  end.
Qed.

Lemma memtyp_mstep_uacc_then_mut : forall m m' t t' e T,
  valid_accesses m t ->
  empty |-- t is T ->
  (* --- *)
  m / t ==[e]==> m' / t' ->
  #m' > #m ->
  unsafe_access (#m) m' t' ->
  exists Tm, m'[#m].typ = <{{&Tm}}>.
Proof.
  intros * ? ? ? Hlen. intros. inversion_clear_mstep;
  try rewrite set_preserves_length in Hlen; try lia.
  simpl_array. simpl. generalize dependent T.
  induction_step; intros; inv_vac; inversion_type; try inv_clear_uacc;
  eauto; exfalso;
  match goal with
  | H : valid_accesses _ ?t, _ : unsafe_access _ _ ?t |- _ =>
    assert (~ access (#m) m t) by (intros F; specialize (H (#m) F); lia)
  end;
  eauto using uacc_then_acc, uacc_mem_add_inheritance.
Qed.

