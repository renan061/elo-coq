From Elo Require Import Util.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import UnsafeAccess.

(* ------------------------------------------------------------------------- *)
(* contains                                                                  *)
(* ------------------------------------------------------------------------- *)

Reserved Notation " t 'contains' t' " (at level 30, no associativity).

Inductive Contains (t' : tm) : tm -> Prop :=
  | contains_eq : forall t,
    t = t' ->
    t contains t'

  | contains_new : forall t T,
    t contains t' ->
    <{ new T t }> contains t'

  | contains_load : forall t,
    t contains t' ->
    <{ *t }> contains t'

  | contains_asg1 : forall t1 t2,
    t1 contains t' ->
    <{ t1 = t2 }> contains t'

  | contains_asg2 : forall t1 t2,
    t2 contains t' ->
    <{ t1 = t2 }> contains t'

  | contains_fun : forall t x Tx,
    t contains t' ->
    <{ fn x Tx --> t }> contains t'

  | contains_call1 : forall t1 t2,
    t1 contains t' ->
    <{ call t1 t2 }> contains t'

  | contains_call2 : forall t1 t2,
    t2 contains t' ->
    <{ call t1 t2 }> contains t'

  | contains_seq1 : forall t1 t2,
    t1 contains t' ->
    <{ t1; t2 }> contains t'

  | contains_seq2 : forall t1 t2,
    t2 contains t' ->
    <{ t1; t2 }> contains t'

  | contains_spawn : forall t,
    t contains t' ->
    <{ spawn t }> contains t'

  where "t 'contains' t'" := (Contains t' t).

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

(* ------------------------------------------------------------------------- *)
(* well-typed-references                                                     *)
(* ------------------------------------------------------------------------- *)

Definition memory_consistency (m m' : mem) :=
  forall ad, ad < length m -> m[ad].typ = m'[ad].typ.

Lemma unsafe_access_ref_type : forall m t ad,
  forall_memory_terms m (WellTypedReferences m) ->
  WellTypedReferences m t ->
  UnsafeAccess m t ad ->
  exists T, m[ad].typ = <{{ &T }}>.
Proof.
  intros * ? ? Huacc. induction Huacc; inversion_wtr; eauto.
Qed.

Lemma consistent_unsafe_access : forall m t t' ad,
  forall_memory_terms m (WellTypedReferences m) ->
  WellTypedReferences m t ->
  WellTypedReferences m t' ->
  UnsafeAccess m t ad ->
  access m t' ad ->
  UnsafeAccess m t' ad.
Proof.
  intros * HwtrM ? ? Huacc Hacc. induction Hacc. 
  - inversion_wtr.
    + eapply uacc_mem; eauto.
    + exfalso.
      assert (WellTypedReferences m m [ad'].tm) by eauto; do 2 auto_specialize.
      assert (exists T, m[ad].typ = <{{ &T }}>) as [T ?]
        by eauto using unsafe_access_ref_type.
      assert (exists v, m[ad'].tm = v) as [v Hv] by admit.
      rewrite Hv in *; clear Hv.

      empty |-- t is <{{ Immut T }}> ->

  ; inversion_wtr; inversion_uacc; eauto.
  - destruct (uacc_dec m t1 ad); eauto; clear IHstep. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
Abort.

