From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Classical_Prop.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import ValidAccesses.
From Elo Require Import References.

Inductive RefType : Prop :=
  | Immut : RefType
  | Mut : RefType
  .

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

Local Lemma hasad_dec : forall ad t,
  Decidable.decidable (HasAddress ad t).
Proof. intros. eauto using classic_decidable. Qed.

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

Local Ltac inversion_nha :=
  match goal with
  | H : ~ HasAddress _ <{ & _ :: _ }> |- _ => eapply inv_nha_ref in H
  | H : ~ HasAddress _ <{ new _ _  }> |- _ => eapply inv_nha_new  in H
  | H : ~ HasAddress _ <{ * _      }> |- _ => eapply inv_nha_load in H
  | H : ~ HasAddress _ <{ _ = _    }> |- _ => eapply inv_nha_asg  in H as [? ?]
  | H : ~ HasAddress _ <{ fn _ _ --> _ }> |- _ => eapply inv_nha_fun in H
  | H : ~ HasAddress _ <{ call _ _ }> |- _ => eapply inv_nha_call  in H as [? ?]
  | H : ~ HasAddress _ <{ _ ; _    }> |- _ => eapply inv_nha_seq   in H as [? ?]
  | H : ~ HasAddress _ <{ spawn _  }> |- _ => eapply inv_nha_spawn in H
  end.

(* -------------------------------------------------------------------------- *)
(* terms                                                                      *)
(* -------------------------------------------------------------------------- *)

(*
  | forall_refs_refI : forall T,
    ForallRefs ad T <{ &ad :: T }>
*)

Inductive ForallRefs (ad : addr) : RefType -> tm -> Prop :=
  | forall_refs_unit : forall rt,
    ForallRefs ad rt <{ unit }>

  | forall_refs_num : forall rt n,
    ForallRefs ad rt <{ N n }>

  | forall_refs_ref : forall rt ad' T,
    ad <> ad' ->
    ForallRefs ad rt <{ &ad' :: T }>

  | forall_refs_refI : forall T,
    ForallRefs ad Immut <{ &ad :: i&T }>

  | forall_refs_refM : forall T,
    ForallRefs ad Mut <{ &ad :: &T }>

  | forall_refs_new : forall rt t T,
    ForallRefs ad rt t ->
    ForallRefs ad rt <{ new T t }>

  | forall_refs_load : forall rt t,
    ForallRefs ad rt t ->
    ForallRefs ad rt <{ *t }>

  | forall_refs_asg : forall rt t1 t2,
    ForallRefs ad rt t1 ->
    ForallRefs ad rt t2 ->
    ForallRefs ad rt <{ t1 = t2 }>

  | forall_refs_var : forall rt x,
    ForallRefs ad rt <{ var x }>

  | forall_refs_fun : forall rt t x Tx,
    ForallRefs ad rt t ->
    ForallRefs ad rt <{ fn x Tx --> t }>

  | forall_refs_call : forall rt t1 t2,
    ForallRefs ad rt t1 ->
    ForallRefs ad rt t2 ->
    ForallRefs ad rt <{ call t1 t2 }>

  | forall_refs_seq : forall rt t1 t2,
    ForallRefs ad rt t1 ->
    ForallRefs ad rt t2 ->
    ForallRefs ad rt <{ t1; t2 }>

  | forall_refs_spawn : forall rt t,
    ForallRefs ad rt t ->
    ForallRefs ad rt <{ spawn t }>
  .

Definition ForallRefsMem (m : mem) (rt : RefType) := forall ad,
  forall_memory m (ForallRefs ad rt).

(* -------------------------------------------------------------------------- *)
(* properties                                                                 *)
(* -------------------------------------------------------------------------- *)

Local Lemma not_hasad_then_forall_refs : forall rt t ad,
  ~ HasAddress ad t ->
  ForallRefs ad rt t.
Proof.
  intros. induction t; try inversion_nha; eauto using ForallRefs.
Qed.

(* -------------------------------------------------------------------------- *)
(* valid-references                                                           *)
(* -------------------------------------------------------------------------- *)

Definition valid_references (rt : RefType) (t : tm) := forall ad,
  HasAddress ad t -> ForallRefs ad rt t.

(* -------------------------------------------------------------------------- *)
(* constructor-vr                                                             *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_con_vr1 :=
  intros * ? ? Hha; inversion_subst_clear Hha; eauto using ForallRefs.

Local Ltac solve_con_vr2 :=
  intros * ? ? ? Hha; inversion_subst_clear Hha; eauto using ForallRefs;
  match goal with
  | _ : HasAddress ?ad ?tA |- ForallRefs _ _ (_ ?tA ?tB) =>
    destruct (hasad_dec ad tB)
  | _ : HasAddress ?ad ?tA |- ForallRefs _ _ (_ ?tB ?tA) =>
    destruct (hasad_dec ad tB)
  end;
  eauto using not_hasad_then_forall_refs, ForallRefs.

Local Lemma vr_con_new : forall rt t T,
  valid_references rt t ->
  valid_references rt <{ new T t }>.
Proof. solve_con_vr1. Qed.

Local Lemma vr_con_load : forall rt t,
  valid_references rt t ->
  valid_references rt <{ *t }>.
Proof. solve_con_vr1. Qed.

Local Lemma vr_con_asg : forall rt t1 t2,
  valid_references rt t1 ->
  valid_references rt t2 ->
  valid_references rt <{ t1 = t2 }>.
Proof. solve_con_vr2. Qed. 

Local Lemma vr_con_call : forall rt t1 t2,
  valid_references rt t1 ->
  valid_references rt t2 ->
  valid_references rt <{ call t1 t2 }>.
Proof. solve_con_vr2. Qed. 

Local Lemma vr_con_fun : forall rt t x Tx,
  valid_references rt t ->
  valid_references rt <{ fn x Tx --> t }>.
Proof. solve_con_vr1. Qed. 

Local Lemma vr_con_seq : forall rt t1 t2,
  valid_references rt t1 ->
  valid_references rt t2 ->
  valid_references rt <{ t1; t2 }>.
Proof. solve_con_vr2. Qed.

Local Lemma vr_con_spawn : forall rt t,
  valid_references rt t ->
  valid_references rt <{ spawn t }>.
Proof. solve_con_vr1. Qed.

(* -------------------------------------------------------------------------- *)
(* inversion-vad                                                              *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_inv_vr :=
  intros * Hvr; try split; intros ad ?; specialize (Hvr ad);
  unshelve (match goal with
  | Hvr : HasAddress ad ?t -> _ |- _ =>
    assert (Hhasad : HasAddress ad t) by shelve; specialize (Hvr Hhasad)
  end;
  inversion_subst_clear Hvr; assumption);
  eauto using HasAddress.

Local Lemma inv_vr_new : forall rt t T,
  valid_references rt <{ new T t }> ->
  valid_references rt t.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_load : forall rt t,
  valid_references rt <{ *t }> ->
  valid_references rt t.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_asg : forall rt t1 t2,
  valid_references rt <{ t1 = t2 }> ->
  valid_references rt t1 /\ valid_references rt t2.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_call : forall rt t1 t2,
  valid_references rt <{ call t1 t2 }> ->
  valid_references rt t1 /\ valid_references rt t2.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_fun : forall rt t x Tx,
  valid_references rt <{ fn x Tx --> t }> ->
  valid_references rt t.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_seq : forall rt t1 t2,
  valid_references rt <{ t1; t2 }> ->
  valid_references rt t1 /\ valid_references rt t2.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_spawn : forall rt t,
  valid_references rt <{ spawn t }> ->
  valid_references rt t.
Proof. solve_inv_vr. Qed.

Ltac inversion_vr :=
  match goal with
  |H: valid_references _ <{ new _ _  }> |- _ => eapply inv_vr_new  in H
  |H: valid_references _ <{ * _      }> |- _ => eapply inv_vr_load in H
  |H: valid_references _ <{ _ = _    }> |- _ => eapply inv_vr_asg  in H as [? ?]
  |H: valid_references _ <{ call _ _ }> |- _ => eapply inv_vr_call in H as [? ?]
  |H: valid_references _ <{ fn _ _ --> _ }> |- _ => eapply inv_vr_fun in H
  |H: valid_references _ <{ _; _     }> |- _ => eapply inv_vr_seq  in H as [? ?]
  |H: valid_references _ <{ spawn _  }> |- _ => eapply inv_vr_spawn in H
  end.

(* -------------------------------------------------------------------------- *)
(* subst                                                                      *)
(* -------------------------------------------------------------------------- *)

Local Lemma subst_vr : forall rt t tx x,
  valid_references rt t ->
  valid_references rt tx ->
  valid_references rt ([x := tx] t).
Proof.
  intros. induction t; eauto; try inversion_vr; simpl;
  eauto using vr_con_new, vr_con_load, vr_con_asg, vr_con_call,
    vr_con_seq, vr_con_spawn;
  destruct String.string_dec; eauto using vr_con_fun.
Qed.

(* -------------------------------------------------------------------------- *)
(* mem                                                                        *)
(* -------------------------------------------------------------------------- *)

(*
Local Lemma mem_add_vad : forall rt m t v,
  valid_references rt t ->
  valid_references rt v ->
  valid_references rt (m +++ v) t.
Proof.
  intros * HvadT HvadV ad.
  destruct (HvadT ad) as [HartT Harm]; clear HvadT.
  destruct (HvadV ad) as [? _]; clear HvadV.
  split; trivial. clear HartT.
  induction m; eauto; unfold add; inversion_subst_clear Harm;
  try (rewrite app_nil_l || rewrite <- app_comm_cons); eauto using AllRefsMem.
Qed.
*)

(* -------------------------------------------------------------------------- *)
(* vad-preservation                                                           *)
(* -------------------------------------------------------------------------- *)

Local Lemma step_none_vr_preservation : forall rt t t',
  valid_references rt t ->
  t --[EF_None]--> t' ->
  valid_references rt t'.
Proof.
  intros. induction_step; inversion_vr;
  eauto using vr_con_new, vr_con_load, vr_con_asg, vr_con_call, vr_con_seq.
  inversion_vr. eauto using subst_vr. 
Qed.

Definition todo (rt : RefType) (t : tm) (ad : addr) :=
  HasAddress ad t -> ForallRefs ad rt t.

Local Lemma step_alloc_vr_preservation : forall rt m t t' ad v,
  valid_accesses m t ->
  HasAddress ad t ->
  ForallRefs ad rt t ->
  t --[EF_Alloc (@length tm m) v]--> t' ->
  ForallRefs ad rt t'.
Proof.
  intros. induction_step.
  - admit.
  - inversion_va. inversion_subst_clear H0. inversion_subst_clear H1.
    destruct (Nat.eq_dec ad (length m)); subst; eauto using ForallRefs.
    specialize (H (length m)). shelve.
  -
  
  eauto using vr_con_new, vr_con_load.
  - intros ? Hhasad. inversion_subst_clear Hhasad. eauto using ForallRefs.
  - intros ? Hhasad. inversion_subst_clear Hhasad. admit.
Qed.


Local Lemma mstep_vr_preservation : forall rt m m' t t' eff,
  valid_references rt m t ->
  m / t ==[eff]==> m' / t' ->
  valid_references rt m' t'.
Proof.
Admitted.























