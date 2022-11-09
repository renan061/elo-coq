From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Arith.Arith.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import References.

(* ------------------------------------------------------------------------- *)
(* SafeAccess & UnsafeAccess                                                 *)
(* ------------------------------------------------------------------------- *)

Inductive UnsafeAccess (m : mem) : tm -> addr -> Prop :=
  | uacc_mem : forall ad ad' T,
    ad <> ad' ->
    UnsafeAccess m m[ad'] ad ->
    UnsafeAccess m <{ &ad' :: T }> ad

  | uacc_ref : forall ad T,
    UnsafeAccess m <{ &ad :: &T }> ad

  | uacc_new : forall T t ad,
    UnsafeAccess m t ad ->
    UnsafeAccess m <{ new T t }> ad

  | uacc_load : forall t ad,
    UnsafeAccess m t ad ->
    UnsafeAccess m <{ *t }> ad

  | uacc_asg1 : forall t1 t2 ad,
    UnsafeAccess m t1 ad ->
    UnsafeAccess m <{ t1 = t2 }> ad

  | uacc_asg2 : forall t1 t2 ad,
    UnsafeAccess m t2 ad ->
    UnsafeAccess m <{ t1 = t2 }> ad

  | uacc_fun : forall x Tx t ad,
    UnsafeAccess m t ad ->
    UnsafeAccess m <{ fn x Tx --> t }> ad

  | uacc_call1 : forall t1 t2 ad,
    UnsafeAccess m t1 ad ->
    UnsafeAccess m <{ call t1 t2 }> ad

  | uacc_call2 : forall t1 t2 ad,
    UnsafeAccess m t2 ad ->
    UnsafeAccess m <{ call t1 t2 }> ad

  | uacc_seq1 : forall t1 t2 ad,
    UnsafeAccess m t1 ad ->
    UnsafeAccess m <{ t1; t2 }> ad

  | uacc_seq2 : forall t1 t2 ad,
    UnsafeAccess m t2 ad ->
    UnsafeAccess m <{ t1; t2 }> ad
  .

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
    ~ UnsafeAccess m t2 ad ->
    SafeAccess m <{ t1 = t2 }> ad

  | sacc_asg2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    ~ UnsafeAccess m t1 ad ->
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
    ~ UnsafeAccess m t2 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  | sacc_call2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    ~ UnsafeAccess m t1 ad ->
    SafeAccess m <{ call t1 t2 }> ad

  (* TODO: redundante *)
  | sacc_seq : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    SafeAccess m t2 ad ->
    SafeAccess m <{ t1; t2 }> ad

  | sacc_seq1 : forall t1 t2 ad,
    SafeAccess m t1 ad ->
    ~ UnsafeAccess m t2 ad ->
    SafeAccess m <{ t1; t2 }> ad

  | sacc_seq2 : forall t1 t2 ad,
    SafeAccess m t2 ad ->
    ~ UnsafeAccess m t1 ad ->
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

Ltac inversion_uacc :=
  match goal with
  | H : UnsafeAccess _ <{ unit         }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ N _          }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ & _ :: _     }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ new _ _      }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ * _          }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ _ = _        }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ var _        }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ fn _ _ --> _ }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ call _ _     }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ _ ; _        }> _ |- _ => inversion_subst_clear H
  | H : UnsafeAccess _ <{ spawn _      }> _ |- _ => inversion_subst_clear H
  end.

(* ------------------------------------------------------------------------- *)
(* Properties                                                                *)
(* ------------------------------------------------------------------------- *)

Theorem sacc_then_access : forall m t ad,
  SafeAccess m t ad ->
  access m t ad.
Proof.
  intros * H. induction H; eauto using access.
Qed.

Theorem uacc_then_access : forall m t ad,
  UnsafeAccess m t ad ->
  access m t ad.
Proof.
  intros * H. induction H; eauto using access.
Qed.

Theorem not_uacc_sacc : forall m t ad,
  UnsafeAccess m t ad ->
  SafeAccess m t ad ->
  False.
Proof.
  intros * Huacc ?. induction Huacc; inversion_sacc; eauto.
Qed.

Theorem access_to_uacc : forall Gamma m t ad T,
  Gamma |-- t is T ->
  well_typed_memory m ->
  access m t ad ->
  ~ SafeAccess m t ad ->
  UnsafeAccess m t ad.
Proof.
  intros * ? Hwtm Hacc ?.
  generalize dependent Gamma. generalize dependent T.
  induction Hacc; intros; inversion_type; eauto using UnsafeAccess;
  unshelve solve 
    [ exfalso; eauto using SafeAccess
    | assert (~ SafeAccess m t ad) by shelve; eauto using UnsafeAccess
    | assert (H1' : ~ (SafeAccess m t1 ad /\ SafeAccess m t2 ad)) by shelve;
      assert (H2' : ~ (SafeAccess m t1 ad /\ ~ UnsafeAccess m t2 ad)) by shelve;
      assert (H3' : ~ (SafeAccess m t2 ad /\ ~ UnsafeAccess m t1 ad)) by shelve;
      eapply not_and_or in H1' as [? | ?];
      eapply not_and_or in H2' as [? | H1''];
      eapply not_and_or in H3' as [? | H2''];
      try (eapply NNPP in H1'');
      try (eapply NNPP in H2'');
      eauto using UnsafeAccess
    | assert (Hlen : ad' < length m) by eauto using access_length;
      assert (~ SafeAccess m m[ad'] ad) by eauto using SafeAccess;
      specialize (Hwtm _ Hlen) as [[? Htype'] ?]; eauto using UnsafeAccess
    ];
  intros F; destruct F; eauto using SafeAccess.
Qed.

Theorem access_to_sacc : forall Gamma m t ad T,
  Gamma |-- t is T ->
  well_typed_memory m ->
  access m t ad ->
  ~ UnsafeAccess m t ad ->
  SafeAccess m t ad.
Proof.
  intros * ? Hwtm Hacc ?.
  generalize dependent Gamma. generalize dependent T.
  induction Hacc; intros; inversion_type; eauto using SafeAccess;
  unshelve solve 
    [ exfalso; eauto using UnsafeAccess
    | assert (~ UnsafeAccess m t ad) by shelve; eauto using SafeAccess
    | assert (~ UnsafeAccess m t1 ad) by shelve;
      assert (~ UnsafeAccess m t2 ad) by shelve;
      eauto using SafeAccess
    | assert (Hlen : ad' < length m) by eauto using access_length;
      assert (~ UnsafeAccess m m[ad'] ad) by eauto using UnsafeAccess;
      specialize (Hwtm _ Hlen) as [[? Htype'] ?]; eauto using SafeAccess
    ];
  intros F; destruct F; eauto using UnsafeAccess.
Qed.

Corollary sacc_uacc_dec : forall Gamma m t ad T,
  well_typed_memory m ->
  Gamma |-- t is T ->
  access m t ad ->
  (SafeAccess m t ad \/ UnsafeAccess m t ad).
Proof.
  intros. 
  assert (decidable (UnsafeAccess m t ad)) as [? | ?] (* TODO *)
      by eauto using classic_decidable.
  - right. assumption.
  - left. eauto using access_to_sacc.
Qed.

