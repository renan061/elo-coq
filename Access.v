From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.

(* A term accesses an address if it refers to the address directly or 
indirectly. *)
Inductive access (m : mem) : tm -> addr -> Prop :=
  | acc_mem : forall ad ad' T,
    ad <> ad' ->
    access m m[ad'].tm ad ->
    access m <{ &ad' :: T }> ad

  | acc_ref : forall ad T,
    access m <{ &ad :: T }> ad

  | acc_new : forall T t ad,
    access m t ad ->
    access m <{ new T t }> ad

  | acc_load : forall t ad,
    access m t ad ->
    access m <{ *t }> ad

  | acc_asg1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ t1 = t2 }> ad

  | acc_asg2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ t1 = t2 }> ad

  | acc_fun : forall x Tx t ad,
    access m t ad ->
    access m <{ fn x Tx --> t }> ad

  | acc_call1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ call t1 t2 }> ad

  | acc_call2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ call t1 t2 }> ad

  | acc_seq1 : forall t1 t2 ad,
    access m t1 ad ->
    access m <{ t1; t2 }> ad

  | acc_seq2 : forall t1 t2 ad,
    access m t2 ad ->
    access m <{ t1; t2 }> ad
  .

Ltac inversion_acc :=
  match goal with
  | H : access _ <{ unit         }> _ |- _ => inversion H
  | H : access _ <{ N _          }> _ |- _ => inversion H
  | H : access _ <{ & _ :: _     }> _ |- _ => inversion H; subst
  | H : access _ <{ new _ _      }> _ |- _ => inversion H; subst
  | H : access _ <{ * _          }> _ |- _ => inversion H; subst
  | H : access _ <{ _ = _        }> _ |- _ => inversion H; subst
  | H : access _ <{ var _        }> _ |- _ => inversion H
  | H : access _ <{ fn _ _ --> _ }> _ |- _ => inversion H; subst
  | H : access _ <{ call _ _     }> _ |- _ => inversion H; subst
  | H : access _ <{ _ ; _        }> _ |- _ => inversion H; subst
  | H : access _ <{ spawn _      }> _ |- _ => inversion H
  end.

Ltac inversion_clear_acc :=
  match goal with
  | H : access _ <{ unit         }> _ |- _ => inversion H
  | H : access _ <{ N _          }> _ |- _ => inversion H
  | H : access _ <{ & _ :: _     }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ new _ _      }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ * _          }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ _ = _        }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ var _        }> _ |- _ => inversion H
  | H : access _ <{ fn _ _ --> _ }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ call _ _     }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ _ ; _        }> _ |- _ => inversion_subst_clear H
  | H : access _ <{ spawn _      }> _ |- _ => inversion H
  end.

(* ------------------------------------------------------------------------- *)
(* properties                                                                *)
(* ------------------------------------------------------------------------- *)

(* strong acc_mem *)
Theorem acc_mem_trans : forall m t ad ad',
  ad <> ad' ->
  access m t ad' ->
  access m m[ad'].tm ad ->
  access m t ad.
Proof.
  intros * ? Hacc ?. induction Hacc; eauto using access.
  destruct (Nat.eq_dec ad ad'); subst; eauto using access.
Qed.

Lemma acc_length : forall m ad ad',
  access m m[ad'].tm ad ->
  ad' < length m.
Proof.
  intros * Hacc.
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; trivial;
  simpl_array; try lia; inversion Hacc.
Qed.

Lemma acc_dec : forall m t ad,
  Decidable.decidable (access m t ad).
Proof. eauto using classic_decidable. Qed.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Inductive not_access (m : mem) : tm -> addr -> Prop :=
  | nacc_unit : forall ad,
    not_access m <{ unit }> ad

  | nacc_num : forall n ad,
    not_access m <{ N n }> ad

  | nacc_ref : forall T ad ad',
    ad <> ad' ->
    ~ access m m[ad].tm ad' ->
    not_access m <{ &ad :: T }> ad'

  | nacc_new : forall T t ad,
    ~ access m t ad ->
    not_access m <{ new T t }> ad

  | nacc_load : forall t ad,
    ~ access m t ad ->
    not_access m <{ *t }> ad

  | nacc_asg : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1 = t2 }> ad

  | nacc_var : forall x ad,
    not_access m <{ var x }> ad

  | nacc_fun : forall x Tx t ad,
    ~ access m t ad ->
    not_access m <{ fn x Tx --> t }> ad

  | nacc_call : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ call t1 t2 }> ad

  | nacc_seq : forall t1 t2 ad,
    ~ access m t1 ad ->
    ~ access m t2 ad ->
    not_access m <{ t1; t2 }> ad

  | nacc_spawn : forall t ad,
    not_access m <{ spawn t }> ad
  .

Theorem nacc_iff : forall m t ad,
  ~ access m t ad <-> not_access m t ad.
Proof.
  intros. split; intros Hnacc; destruct t;
  try (eapply nacc_ref
    || eapply nacc_asg
    || eapply nacc_call
    || eapply nacc_seq);
  eauto using access, not_access;
  intros ?; subst;
  try (inversion_acc; inversion_clear Hnacc); eauto using access.
  match goal with
  | Hnacc : ~ access _ <{ & ?ad :: _ }> ?ad' |- _ =>
    destruct (Nat.eq_dec ad ad'); subst; eauto using access
  end.
Qed.

Ltac inversion_nacc Hnacc :=
  eapply nacc_iff in Hnacc; inversion Hnacc; subst; eauto using access.

(* ------------------------------------------------------------------------- *)
(* preservation helpers                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma subst_acc : forall m x Tx t t' ad,
  access m ([x := t'] t) ad ->
  access m <{ call <{ fn x Tx --> t }> t' }> ad.
Proof.
  intros. induction t; eauto using access; simpl in *;
  try (destruct String.string_dec; eauto using access);
  inversion_clear_acc; auto_specialize; do 2 inversion_acc; eauto using access.
Qed.

Local Lemma subst_nacc' : forall m t tx ad x,
  ~ access m t ad ->
  ~ access m tx ad ->
  ~ access m ([x := tx] t) ad.
Proof.
  intros * Hnacc ?. generalize dependent tx.
  induction t; intros; trivial; simpl;
  try solve [eapply nacc_iff; inversion_nacc Hnacc; eauto using not_access];
  destruct String.string_dec; trivial.
  inversion_nacc Hnacc. eapply nacc_iff. eauto using not_access.
Qed.

Lemma subst_nacc : forall m t tx ad x Tx,
  ~ access m <{ fn x Tx --> t }> ad ->
  ~ access m tx ad ->
  ~ access m ([x := tx] t) ad.
Proof.
  intros * Hnacc ?. inversion_nacc Hnacc; eauto using subst_nacc'.
Qed.

