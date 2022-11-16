From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import References.

Inductive SafeAccess (m : mem) : tm -> addr -> Prop :=
  | sacc_memI : forall ad ad' T,
    ad <> ad' ->
    access m m[ad'] ad ->
    SafeAccess m <{ &ad' :: i&T }> ad

  | sacc_memM : forall ad ad' T,
    ad <> ad' ->
    SafeAccess m m[ad'] ad ->
    SafeAccess m <{ &ad' :: &T }> ad

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

(* TODO: standardize *)
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

Lemma sacc_dec : forall m t ad,
  Decidable.decidable (SafeAccess m t ad).
Proof. eauto using classic_decidable. Qed.

Theorem sacc_strong_transitivity : forall m ad v T,
  value v ->
  access m v ad ->
  empty |-- v is (TY_Immut T) ->
  SafeAccess m v ad.
Proof.
  intros * Hval ? ?. destruct Hval;
  inversion_access; inversion_type; eauto using SafeAccess.
Qed.

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

Lemma sacc_correctness : forall m m' t t' ad' eff T,
  ad' < length m ->
  empty |-- t is T ->
  SafeAccess m t ad' ->
  m / t ==[eff]==> m' / t' ->
  m[ad'] = m'[ad'].
Proof.
  assert (forall m t t' ad v,
    ~ access m t ad ->
    ~ t --[EF_Write ad v]--> t').
  { intros * Hnacc ?. induction_step; inversion_not_access Hnacc. }

  intros * ? ? Hsacc ?. inversion_mstep; trivial.
  - decompose sum (lt_eq_lt_dec ad' (length m)); subst; rewrite_term_array. lia.
  - decompose sum (lt_eq_lt_dec ad ad'); subst; rewrite_term_array.
    generalize dependent t'. generalize dependent T.
    induction Hsacc; intros; inversion_type; inversion_step; eauto;
    solve
      [ inversion_type; inversion_sacc; lia
      | exfalso; unfold not in *; eauto
      | inversion_type;
        match goal with
        | F : ~ access _ _ _ |- _ =>
          inversion_not_access F; lia
        end
      ].
Qed.

Lemma nacc_then_not_write : forall m t t' ad v,
  ~ access m t ad ->
  t --[EF_Write ad v]--> t' ->
  False.
Proof.
  intros * Hnacc ?. induction_step;
  inversion_not_access Hnacc; clear Hnacc.
Qed.

Lemma write_then_nsacc : forall m t t' ad v T,
  empty |-- t is T ->
  t --[EF_Write ad v]--> t' ->
  ~ SafeAccess m t ad.
Proof.
  intros * ? ?. generalize dependent T.
  induction_step; intros * ? ?; unfold not in *;
  inversion_type; inversion_sacc; eauto using nacc_then_not_write, access;
  inversion_type; inversion_sacc; lia.
Qed.

(* TODO *)
Definition UnsafeAccess m t ad :=
  access m t ad /\ ~ SafeAccess m t ad.

(* TODO: session for examples! *)

