From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Classical_Prop.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import ValidAddresses.
From Elo Require Import References.

Inductive RefType : Prop :=
  | Immut : RefType
  | Mut : RefType
  .

(* -------------------------------------------------------------------------- *)
(* consistent-refs                                                            *)
(* -------------------------------------------------------------------------- *)

(*
  | conrefs_ref : forall T,
    ConsistentRefs ad T <{ &ad :: T }>
*)

(* Quando vc da alloc o tipo da ref não muda nunca mais. *)

(* All references to ad inside the term have the same type regarding
mutability. *)
Inductive ConsistentRefs (ad : addr) : RefType -> tm -> Prop :=
  | conrefs_unit : forall rt,
    ConsistentRefs ad rt <{ unit }>

  | conrefs_num : forall rt n,
    ConsistentRefs ad rt <{ N n }>

  | conrefs_ref : forall rt ad' T,
    ad <> ad' ->
    ConsistentRefs ad rt <{ &ad' :: T }>

  | conrefs_refI : forall T,
    ConsistentRefs ad Immut <{ &ad :: i&T }>

  | conrefs_refM : forall T,
    ConsistentRefs ad Mut <{ &ad :: &T }>

  | conrefs_new : forall rt t T,
    ConsistentRefs ad rt t ->
    ConsistentRefs ad rt <{ new T t }>

  | conrefs_load : forall rt t,
    ConsistentRefs ad rt t ->
    ConsistentRefs ad rt <{ *t }>

  | conrefs_asg : forall rt t1 t2,
    ConsistentRefs ad rt t1 ->
    ConsistentRefs ad rt t2 ->
    ConsistentRefs ad rt <{ t1 = t2 }>

  | conrefs_var : forall rt x,
    ConsistentRefs ad rt <{ var x }>

  | conrefs_fun : forall rt t x Tx,
    ConsistentRefs ad rt t ->
    ConsistentRefs ad rt <{ fn x Tx --> t }>

  | conrefs_call : forall rt t1 t2,
    ConsistentRefs ad rt t1 ->
    ConsistentRefs ad rt t2 ->
    ConsistentRefs ad rt <{ call t1 t2 }>

  | conrefs_seq : forall rt t1 t2,
    ConsistentRefs ad rt t1 ->
    ConsistentRefs ad rt t2 ->
    ConsistentRefs ad rt <{ t1; t2 }>

  | conrefs_spawn : forall rt t,
    ConsistentRefs ad rt t ->
    ConsistentRefs ad rt <{ spawn t }>
  .

Definition ConsistentRefsMem (m : mem) (rt : RefType) := forall ad,
  forall_memory m (ConsistentRefs ad rt).

(* -------------------------------------------------------------------------- *)
(* properties                                                                 *)
(* -------------------------------------------------------------------------- *)

Local Lemma nha_then_conrefs : forall rt t ad,
  ~ HasAddress ad t ->
  ConsistentRefs ad rt t.
Proof.
  intros. induction t; try inversion_nha; eauto using ConsistentRefs.
Qed.

(* -------------------------------------------------------------------------- *)
(* valid-references                                                           *)
(* -------------------------------------------------------------------------- *)

Definition valid_references (rt : RefType) (ad : addr) (t : tm) :=
  HasAddress ad t -> ConsistentRefs ad rt t.

Local Ltac solve_con_vr1 :=
  intros; intros ?; inversion_ha; eauto using ConsistentRefs.

Local Ltac solve_con_vr2 :=
  intros; intros ?; inversion_ha; eauto using ConsistentRefs;
  match goal with
  | _ : HasAddress ?ad ?tA |- ConsistentRefs _ _ (_ ?tA ?tB) =>
    destruct (hasad_dec ad tB)
  | _ : HasAddress ?ad ?tA |- ConsistentRefs _ _ (_ ?tB ?tA) =>
    destruct (hasad_dec ad tB)
  end;
  eauto using nha_then_conrefs, ConsistentRefs.

Local Lemma vr_new : forall rt t ad T,
  valid_references rt ad t ->
  valid_references rt ad <{ new T t }>.
Proof. solve_con_vr1. Qed.

Local Lemma vr_load : forall rt t ad,
  valid_references rt ad t ->
  valid_references rt ad <{ *t }>.
Proof. solve_con_vr1. Qed.

Local Lemma vr_asg : forall rt t1 t2 ad,
  valid_references rt ad t1 ->
  valid_references rt ad t2 ->
  valid_references rt ad <{ t1 = t2 }>.
Proof. solve_con_vr2. Qed. 

Local Lemma vr_call : forall rt t1 t2 ad,
  valid_references rt ad t1 ->
  valid_references rt ad t2 ->
  valid_references rt ad <{ call t1 t2 }>.
Proof. solve_con_vr2. Qed. 

Local Lemma vr_fun : forall rt t ad x Tx,
  valid_references rt ad t ->
  valid_references rt ad <{ fn x Tx --> t }>.
Proof. solve_con_vr1. Qed. 

Local Lemma vr_seq : forall rt t1 t2 ad,
  valid_references rt ad t1 ->
  valid_references rt ad t2 ->
  valid_references rt ad <{ t1; t2 }>.
Proof. solve_con_vr2. Qed.

Local Lemma vr_spawn : forall rt t ad,
  valid_references rt ad t ->
  valid_references rt ad <{ spawn t }>.
Proof. solve_con_vr1. Qed.

(* -------------------------------------------------------------------------- *)
(* inversion-vr                                                               *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_inv_vr :=
  intros * Hvr; try split; intros ?; unfold valid_references in *;
  unshelve (match goal with
  | Hvr : HasAddress ?ad ?t -> _ |- _ =>
    assert (Hhasad : HasAddress ad t) by shelve; specialize (Hvr Hhasad)
  end;
  inversion_subst_clear Hvr; assumption);
  eauto using HasAddress.

Local Lemma inv_vr_new : forall rt t ad T,
  valid_references rt ad <{ new T t }> ->
  valid_references rt ad t.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_load : forall rt t ad,
  valid_references rt ad <{ *t }> ->
  valid_references rt ad t.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_asg : forall rt t1 t2 ad,
  valid_references rt ad <{ t1 = t2 }> ->
  valid_references rt ad t1 /\ valid_references rt ad t2.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_call : forall rt t1 t2 ad,
  valid_references rt ad <{ call t1 t2 }> ->
  valid_references rt ad t1 /\ valid_references rt ad t2.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_fun : forall rt t ad x Tx,
  valid_references rt ad <{ fn x Tx --> t }> ->
  valid_references rt ad t.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_seq : forall rt t1 t2 ad,
  valid_references rt ad <{ t1; t2 }> ->
  valid_references rt ad t1 /\ valid_references rt ad t2.
Proof. solve_inv_vr. Qed.

Local Lemma inv_vr_spawn : forall rt t ad,
  valid_references rt ad <{ spawn t }> ->
  valid_references rt ad t.
Proof. solve_inv_vr. Qed.

Ltac inversion_vr :=
  match goal with
  | H : valid_references _ _ <{ new _ _      }> |- _ => eapply inv_vr_new  in H
  | H : valid_references _ _ <{ * _          }> |- _ => eapply inv_vr_load in H
  | H : valid_references _ _ <{ _ = _        }> |- _ =>
                                                eapply inv_vr_asg  in H as [? ?]
  | H : valid_references _ _ <{ call _ _     }> |- _ =>
                                                eapply inv_vr_call in H as [? ?]
  | H : valid_references _ _ <{ fn _ _ --> _ }> |- _ => eapply inv_vr_fun in H
  | H : valid_references _ _ <{ _; _         }> |- _ =>
                                                eapply inv_vr_seq  in H as [? ?]
  | H : valid_references _ _ <{ spawn _      }> |- _ => eapply inv_vr_spawn in H
  end.

(* -------------------------------------------------------------------------- *)
(* subst                                                                      *)
(* -------------------------------------------------------------------------- *)

Local Lemma subst_vr : forall rt t tx ad x,
  valid_references rt ad t ->
  valid_references rt ad tx ->
  valid_references rt ad ([x := tx] t).
Proof.
  intros. induction t; eauto; try inversion_vr; simpl;
  eauto using vr_new, vr_load, vr_asg, vr_call, vr_seq, vr_spawn;
  destruct String.string_dec; eauto using vr_fun.
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
(* vr-preservation                                                            *)
(* -------------------------------------------------------------------------- *)

Local Lemma step_none_vr_preservation : forall rt t t' ad,
  valid_references rt ad t ->
  t --[EF_None]--> t' ->
  valid_references rt ad t'.
Proof.
  intros. induction_step; inversion_vr;
  eauto using vr_new, vr_load, vr_asg, vr_call, vr_seq.
  inversion_vr. eauto using subst_vr. 
Qed.

Local Lemma step_alloc_vr_preservation1 : forall rt t t' ad ad' v,
  ad <> ad' ->
  ConsistentRefs ad rt t ->
  t --[EF_Alloc ad' v]--> t' ->
  ConsistentRefs ad rt t'.
Proof.
  intros * ? Hconrefs ?.
  induction_step; inversion Hconrefs; subst; eauto using ConsistentRefs.
Qed.

Local Lemma step_alloc_vr_preservation2 : forall t t' ad v T,
  empty |-- t is T ->
  t --[EF_Alloc ad v]--> t' ->
  exists rt, ConsistentRefs ad rt t'.
Proof.
  intros. generalize dependent T. induction_step; intros; inversion_type;
  eauto using ConsistentRefs;
  match goal with
  | H : empty |-- ?t is ?T |- _ => destruct (IHstep eq_refl T H); trivial
  end;
  eauto using ConsistentRefs; eexists;
  match goal with
  | _ : ConsistentRefs _ _ ?t1 |- ConsistentRefs _ _ (_ ?t1 ?t2) => 
    destruct (hasad_dec ad t2); eauto using nha_then_conrefs, ConsistentRefs
  | _ : ConsistentRefs _ _ ?t2 |- ConsistentRefs _ _ (_ ?t1 ?t2) => 
    destruct (hasad_dec ad t1); eauto using nha_then_conrefs, ConsistentRefs
  end;
  exfalso.
Abort.

Local Lemma mstep_vr_preservation : forall rt m m' t t' eff,
  valid_references rt m t ->
  m / t ==[eff]==> m' / t' ->
  valid_references rt m' t'.
Proof.
Admitted.























