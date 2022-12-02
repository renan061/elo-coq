From Elo Require Import Util.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import UnsafeAccess.

(* ------------------------------------------------------------------------- *)
(* well-typed-references                                                     *)
(* ------------------------------------------------------------------------- *)

Inductive WellTypedReferences (m : mem) : tm -> Prop :=
  | wtr_unit :
    WellTypedReferences m <{ unit }> 

  | wtr_num : forall n,
    WellTypedReferences m <{ N n }>

  | wtr_refM : forall T ad,
    empty |-- m[ad].tm is T ->
    m[ad].typ = <{{ &T }}> ->
    WellTypedReferences m <{ &ad :: &T }>

  | wtr_refI : forall T ad,
    empty |-- m[ad].tm is <{{ Immut T }}> ->
    m[ad].typ = <{{ i&T }}> ->
    WellTypedReferences m <{ &ad :: i&T }>

  | wtr_new : forall T t,
    WellTypedReferences m t ->
    WellTypedReferences m <{ new T t }> 

  | wtr_load : forall t,
    WellTypedReferences m t ->
    WellTypedReferences m <{ *t }> 

  | wtr_asg : forall t1 t2,
    WellTypedReferences m t1 ->
    WellTypedReferences m t2 ->
    WellTypedReferences m <{ t1 = t2 }> 

  | wtr_var : forall x,
    WellTypedReferences m <{ var x }>

  | wtr_fun : forall x Tx t,
    WellTypedReferences m t ->
    WellTypedReferences m <{ fn x Tx --> t }>

  | wtr_call : forall t1 t2,
    WellTypedReferences m t1 ->
    WellTypedReferences m t2 ->
    WellTypedReferences m <{ call t1 t2 }> 

  | wtr_seq : forall t1 t2,
    WellTypedReferences m t1 ->
    WellTypedReferences m t2 ->
    WellTypedReferences m <{ t1; t2 }>

  | wtr_spawn : forall t,
    WellTypedReferences m t ->
    WellTypedReferences m <{ spawn t }>
  .

Ltac inversion_wtr :=
  match goal with
  | H : WellTypedReferences _ <{ unit         }> |- _ => inversion H
  | H : WellTypedReferences _ <{ N _          }> |- _ => inversion H
  | H : WellTypedReferences _ <{ & _ :: _     }> |- _ => inversion H; subst
  | H : WellTypedReferences _ <{ new _ _      }> |- _ => inversion H; subst
  | H : WellTypedReferences _ <{ * _          }> |- _ => inversion H; subst
  | H : WellTypedReferences _ <{ _ = _        }> |- _ => inversion H; subst
  | H : WellTypedReferences _ <{ var _        }> |- _ => inversion H
  | H : WellTypedReferences _ <{ fn _ _ --> _ }> |- _ => inversion H; subst
  | H : WellTypedReferences _ <{ call _ _     }> |- _ => inversion H; subst
  | H : WellTypedReferences _ <{ _ ; _        }> |- _ => inversion H; subst
  | H : WellTypedReferences _ <{ spawn _      }> |- _ => inversion H; subst
  end.

Ltac inversion_clear_wtr :=
  match goal with
  | H : WellTypedReferences _ <{ unit         }> |- _ => inversion H
  | H : WellTypedReferences _ <{ N _          }> |- _ => inversion H
  | H : WellTypedReferences _ <{ & _ :: _     }> |- _ => inversion_subst_clear H
  | H : WellTypedReferences _ <{ new _ _      }> |- _ => inversion_subst_clear H
  | H : WellTypedReferences _ <{ * _          }> |- _ => inversion_subst_clear H
  | H : WellTypedReferences _ <{ _ = _        }> |- _ => inversion_subst_clear H
  | H : WellTypedReferences _ <{ var _        }> |- _ => inversion H
  | H : WellTypedReferences _ <{ fn _ _ --> _ }> |- _ => inversion_subst_clear H
  | H : WellTypedReferences _ <{ call _ _     }> |- _ => inversion_subst_clear H
  | H : WellTypedReferences _ <{ _ ; _        }> |- _ => inversion_subst_clear H
  | H : WellTypedReferences _ <{ spawn _      }> |- _ => inversion_subst_clear H
  end.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* consistency                                                               *)
(* ------------------------------------------------------------------------- *)

Definition memory_consistency (m m' : mem) :=
  forall ad, ad < length m -> m[ad].typ = m'[ad].typ.

Local Lemma uacc_then_mut : forall m ad v T,
  value v ->
  UnsafeAccess m v ad ->
  empty |-- v is <{{ Immut T }}> ->
  False.
Proof.
  intros * Hval Huacc ?. generalize dependent T.
  induction Huacc; intros; inversion Hval; subst; inversion_type; eauto.
Qed.

Local Lemma consistent_memtyp : forall m t ad T,
  forall_memory_terms m value ->
  forall_memory_terms m (WellTypedReferences m) ->
  WellTypedReferences m t ->
  m[ad].typ = <{{ &T }}> ->
  access m t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * ? ? ? Heq Hacc. induction Hacc;
  inversion_wtr; eauto using UnsafeAccess;
  exfalso; eauto using uacc_then_mut.
  rewrite Heq in *. discriminate.
Qed.

Local Lemma wtr_uacc_memtyp : forall m t ad,
  forall_memory_terms m (WellTypedReferences m) ->
  WellTypedReferences m t ->
  UnsafeAccess m t ad ->
  exists T, m[ad].typ = <{{ &T }}>.
Proof.
  intros * ? ? Huacc. induction Huacc; inversion_wtr; eauto.
Qed.

Lemma consistent_uacc : forall m t t' ad,
  forall_memory_terms m value ->
  forall_memory_terms m (WellTypedReferences m) ->
  WellTypedReferences m t ->
  WellTypedReferences m t' ->
  UnsafeAccess m t ad ->
  access m t' ad ->
  UnsafeAccess m t' ad.
Proof.
  intros.
  assert (exists T, m[ad].typ = <{{ &T }}>) as [? ?]
    by eauto using wtr_uacc_memtyp.
  eauto using consistent_memtyp.
Qed.

