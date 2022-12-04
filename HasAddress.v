From Coq Require Classical_Prop.

From Elo Require Import Util.
From Elo Require Import Core.

(* A term has an address <ad> if it contains
a reference term poiting to <ad>. *)
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

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* properties                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma step_alloc_hasad : forall t t' ad ad' v V,
  HasAddress ad v ->
  t --[EF_Alloc ad' v V]--> t' ->
  HasAddress ad t.
Proof. intros. induction_step; eauto using HasAddress. Qed.

Lemma step_write_hasad1 : forall t t' ad v V,
  t --[EF_Write ad v V]--> t' ->
  HasAddress ad t.
Proof. intros. induction_step; eauto using HasAddress. Qed.

Lemma step_write_hasad2 : forall t t' ad ad' v V,
  HasAddress ad v ->
  t --[EF_Write ad' v V]--> t' ->
  HasAddress ad t.
Proof. intros. induction_step; eauto using HasAddress. Qed.

