From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Arith.Arith.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import References.

Inductive SafeAccess (m : mem) : tm -> addr -> Prop :=
  | sacc_mem : forall ad ad' T,
    ad <> ad' ->
    SafeAccess m m[ad'] ad ->
    SafeAccess m <{ &ad' :: T }> ad

  | sacc_ref : forall ad T,
    SafeAccess m <{ &ad :: i&T }> ad

  | sacc_new : forall t ad T,
    SafeAccess m t ad ->
    SafeAccess m <{ new T t }> ad

  | sacc_load : forall t ad,
    SafeAccess m t ad ->
    SafeAccess m <{ *t }> ad

  | sacc_asg : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m t2 ad ->
    SafeAccess m <{ t1 = t2 }> ad

  | sacc_asg1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    ~ access m t2 ad ->
    SafeAccess m <{ t1 = t2 }> ad

  | sacc_asg2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    ~ access m t1 ad ->
    SafeAccess m <{ t1 = t2 }> ad

  | sacc_fun : forall x Tx t ad,
    SafeAccess m t ad ->
    SafeAccess m <{ fn x Tx --> t }> ad

  | sacc_call : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m t2 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  | sacc_call1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    ~ access m t2 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  | sacc_call2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    ~ access m t1 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  | sacc_seq : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m t2 ad ->
    SafeAccess m <{ t1; t2 }> ad

  | sacc_seq1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    ~ access m t2 ad ->
    SafeAccess m <{ t1; t2 }> ad

  | sacc_seq2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    ~ access m t1 ad ->
    SafeAccess m <{ t1; t2 }> ad
  .

Ltac inversion_sacc :=
  match goal with
  | H : SafeAccess _ <{ unit         }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ N _          }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ & _ :: _     }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ new _ _      }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ * _          }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ _ = _        }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ var _        }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ fn _ _ --> _ }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ call _ _     }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ _ ; _        }> _ |- _ => inversion_subst_clear H
  | H : SafeAccess _ <{ spawn _      }> _ |- _ => inversion_subst_clear H
  end.

Lemma sacc_then_access : forall m t ad,
  SafeAccess m t ad ->
  access m t ad.
Proof.
  intros * H. induction H; eauto using access.
Qed.

Lemma not_access_then_not_sacc : forall m t ad,
  ~ access m t ad ->
  ~ SafeAccess m t ad.
Proof.
  intros * H F. induction F; eauto using access.
Qed.

(*

SafeAccess m t ad ->
t --> t'
m[ad] = m'[ad]

m[ad] <> m'[ad]
t --> t'
UnsafeAccess m t ad

*)
