From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import ValidAccesses.
From Elo Require Import References.
From Elo Require Import AccessProp.

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
  - decompose sum (lt_eq_lt_dec ad' (length m)); subst;
    simpl_array; trivial. lia.
  - decompose sum (lt_eq_lt_dec ad ad'); subst; simpl_array; trivial.
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

(* ------------------------------------------------------------------------- *)
(* properties -- subst                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma sacc_subst1 : forall m t tx ad x,
  ~ access m tx ad ->
  SafeAccess m t ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * ? Hsacc. induction Hsacc; simpl;
  eauto using SafeAccess, not_access_subst.
  destruct String.string_dec; subst; eauto using SafeAccess.
Qed.

Lemma sacc_subst2 : forall m t tx ad x,
  ~ access m t ad ->
  access m ([x := tx] t) ad ->
  SafeAccess m tx ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * Hnacc ? ?. induction t; simpl in *;
  try (destruct String.string_dec);
  try inversion_access; inversion_not_access Hnacc;
  eauto using SafeAccess; try contradiction;
  match goal with
  | _ : not_access m (_ ?t1 ?t2) _, _ : access m ([_ := _] ?t1) _ |- _ =>
    destruct (access_dec m ([x := tx] t2) ad) as [? | ?]
  | _ : not_access m (_ ?t1 ?t2) _, _ : access m ([_ := _] ?t2) _ |- _ =>
    destruct (access_dec m ([x := tx] t1) ad) as [? | ?]
  end;
  eauto using SafeAccess.
Qed.

Lemma sacc_subst3 : forall m t tx ad x,
  SafeAccess m t ad ->
  SafeAccess m tx ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * Hsacc ?.
  induction Hsacc; simpl; try (destruct String.string_dec);
  eauto using SafeAccess;
  match goal with
  | _ : SafeAccess _ ?t1 _, _ : ~ access _ ?t2 _ |- _ =>
    destruct (sacc_dec m ([x := tx] t2) ad) as [? | ?];
    destruct (access_dec m ([x := tx] t2) ad) as [? | ?]
  end;
  eauto using sacc_subst2, SafeAccess.
Qed.

Corollary sacc_subst_call : forall m x Tx t tx ad,
  access m ([x := tx] t) ad ->
  ~ access m <{ fn x Tx --> t }> ad ->
  SafeAccess m tx ad ->
  SafeAccess m ([x := tx] t) ad.
Proof.
  intros * ? Hnacc ?. inversion_not_access Hnacc. eauto using sacc_subst2.
Qed.

(* ------------------------------------------------------------------------- *)
(* properties -- memory -- add                                               *)
(* ------------------------------------------------------------------------- *)

Lemma mem_add_preserves_sacc : forall Gamma m t ad v T,
  well_typed_memory m ->
  Gamma |-- t is T ->
  ~ access m t (length m) ->
  SafeAccess m t ad ->
  SafeAccess (m +++ v) t ad.
Proof.
  intros * Hwtm Htype Hnacc Hsacc.
  generalize dependent Gamma. generalize dependent T.
  induction Hsacc; intros;
  inversion_type; inversion_not_access Hnacc;
  eauto using SafeAccess, mem_add_nacc_lt;
  (eapply sacc_memI || eapply sacc_memM); trivial;
  decompose sum (lt_eq_lt_dec ad' (length m)); subst; try lia;
  simpl_array.
  + eauto using mem_add_preserves_access.
  + exfalso. do 2 simpl_array. inversion_access.
  + destruct (Hwtm ad') as [[? ?] _]; eauto.
  + exfalso. do 3 simpl_array. inversion_sacc.
Qed.

(* ------------------------------------------------------------------------- *)
(* properties -- mstep sacc preservation                                     *)
(* ------------------------------------------------------------------------- *)

Local Lemma mstep_none_preserves_sacc : forall m m' t t' ad,
  SafeAccess m t ad ->
  m / t ==[EF_None]==> m' / t' ->
  access m' t' ad ->
  SafeAccess m' t' ad.
Proof.
  intros * Hsacc ? Hacc. inversion_mstep. rename m' into m.
  induction_step; inversion_sacc; try inversion_access;
  eauto using sacc_subst_call, step_none_preserves_not_access, SafeAccess;
  solve
    [ match goal with
      | IH : _ -> access _ ?t _ -> _ -> _ |- _ =>
        destruct (access_dec m t ad) as [? | ?]; eauto using SafeAccess
      end
    | exfalso; eauto
    | inversion_sacc; eauto using sacc_subst1, sacc_subst3
    ].
Qed.

Local Lemma mstep_alloc_preserves_sacc : forall m t t' ad v T,
  well_typed_memory m ->
  valid_accesses m t ->
  empty |-- t is T ->
  SafeAccess m t ad ->
  t --[EF_Alloc (length m) v]--> t' ->
  SafeAccess (m +++ v) t' ad.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_va; inversion_type; inversion_sacc;
  eauto using mem_add_preserves_sacc, va_nacc_length, SafeAccess;
  destruct (Nat.eq_dec ad (length m)); subst;
  eauto using mem_add_preserves_sacc, step_alloc_preserves_nacc,
    mem_add_nacc_lt, va_nacc_length, SafeAccess;
  try solve [ match goal with
  | _ : SafeAccess _ ?t _ |- _ =>
    exfalso; eapply (va_nacc_length _ t); eauto using sacc_then_access
  end ];
  (eapply sacc_memI || eapply sacc_memM); trivial; simpl_array;
  eauto using mem_add_preserves_sacc, mem_add_preserves_access,
    va_nacc_length, mem_add_preserves_access, sacc_then_access.
Qed.

Local Lemma mstep_read_preserves_sacc : forall m m' t t' ad ad' v,
  forall_memory m value ->
  well_typed_references m t ->
  SafeAccess m t ad ->
  m / t ==[EF_Read ad' v]==> m' / t' ->
  access m' t' ad ->
  SafeAccess m' t' ad.
Proof.
  intros. inversion_mstep. rename m' into m.
  induction_step; inversion_wtr m; inversion_sacc; try inversion_access;
  eauto using SafeAccess, step_read_preserves_not_access;
  solve
    [ match goal with
      | IH : _ -> _ -> access _ ?t _ -> _ -> _ |- _ =>
        destruct (access_dec m t ad) as [? | ?]; eauto using SafeAccess
      end
    | exfalso; eauto
    | inversion_wtr m; inversion_sacc; eauto using sacc_strong_transitivity 
    ].
Qed.

Local Lemma mstep_write_preserves_sacc : forall m m' t t' ad ad' v,
  SafeAccess m t ad ->
  m / t ==[EF_Write ad' v]==> m' / t' ->
  access m' t' ad ->
  SafeAccess m' t' ad.
Proof.
  intros * Hsacc ? Hacc. inversion_mstep.
  induction_step; inversion_sacc; try inversion_access; eauto using SafeAccess.
  - do 3 auto_specialize. clear H6.
    assert (access m t2 ad) by eauto using sacc_then_access.
    eapply sacc_asg; trivial.
    (* TODO
      Se  SafeAccess m t1 ad        e
          t1 --[Write ad' v]--> t1' então

      (1) ~ access   m v ad  ou
      (2) SafeAccess m v ad

      Se (2):
        SafeAccess m v ad ->
        SafeAccess m t ad ->
        SafeAccess m[ad' <- v] t ad

    *)
Abort.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Definition UnsafeAccess m t ad :=
  access m t ad /\ ~ SafeAccess m t ad.

(* TODO: session for examples! *)

