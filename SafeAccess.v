From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Contains.
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

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

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

Lemma nacc_then_nsacc : forall m t ad,
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

(* TODO *)
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
  simpl_array; eauto using mem_add_preserves_access.
  - exfalso. do 2 simpl_array. inversion_access.
  - destruct (Hwtm ad') as [[? ?] _]; eauto.
  - exfalso. do 3 simpl_array. inversion_sacc.
Qed.

(* ------------------------------------------------------------------------- *)
(* properties -- memory -- set                                               *)
(* ------------------------------------------------------------------------- *)

Lemma mem_set_preserves_sacc1 : forall m t ad ad' v,
  ~ access m t ad' ->
  SafeAccess m t ad ->
  SafeAccess m[ad' <- v] t ad.
Proof.
  intros * Hnacc Hsacc. induction Hsacc;
  inversion_not_access Hnacc; eauto using mem_set_preserves_nacc2, SafeAccess;
  (eapply sacc_memI || eapply sacc_memM); trivial;
  simpl_array; eauto using mem_set_preserves_acc1.
Qed.

Lemma todo : forall m t ad ad' v,
  ~ access m t ad ->
  access m t ad' ->
  SafeAccess m v ad ->
  SafeAccess m[ad' <- v] t ad.
Proof.
  intros * Hnacc Hacc Hsacc. induction t.
  - inversion_access.
  - inversion_access.
  - inversion_not_access Hnacc. inversion_access.
    + destruct t.
      * destruct i.
        ** admit.
        ** admit.
        ** eapply sacc_memI; eauto. simpl_array.
           admit.
      * admit.
      * admit.
    + admit.
Abort.

Lemma mem_set_sacc1 : forall m t ad ad' v,
  access m t ad' ->
  SafeAccess m t ad ->
  SafeAccess m v ad ->
  SafeAccess m[ad' <- v] t ad.
Proof.
  intros * Hacc Hsacc ?. induction Hsacc; eauto using SafeAccess.
  - inversion_access.
    + eapply sacc_memI; trivial.
      simpl_array.
      admit.
    + eapply sacc_memI; trivial.
      assert (ad' < length m) by admit.
      simpl_array.
      admit.
  - admit.
  - inversion_access. eauto using SafeAccess.
  - inversion_access. eauto using SafeAccess.
  - inversion_access.
    + do 2 auto_specialize.
      destruct (access_dec m t2 ad');
      eauto using mem_set_preserves_sacc1, SafeAccess.
    + do 2 auto_specialize.
      destruct (access_dec m t1 ad');
      eauto using mem_set_preserves_sacc1, SafeAccess.
  - inversion_access.
    + do 2 auto_specialize.
      destruct (access_dec m t2 ad').
      * admit.
      * eauto using mem_set_preserves_nacc2, SafeAccess.
Abort.

(* ------------------------------------------------------------------------- *)
(* properties -- mstep sacc preservation                                     *)
(* ------------------------------------------------------------------------- *)

Lemma mstep_none_preserves_sacc : forall m m' t t' ad,
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

Lemma mstep_alloc_preserves_sacc : forall m t t' ad v T,
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

Lemma mstep_read_preserves_sacc : forall m m' t t' ad ad' v,
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

Lemma contains_acc : forall m t t' ad,
  access m t' ad ->
  t contains t' ->
  access m t ad.
Proof.
  intros * ? Hcon. induction Hcon; subst; eauto using access.
Qed.

Lemma contains_sacc : forall m t t' ad,
  SafeAccess m t ad ->
  t contains t' ->
  access m t' ad ->
  SafeAccess m t' ad.
Proof.
  intros * ? Hcon ?. induction Hcon; subst; trivial;
  inversion_sacc; eauto; exfalso; eauto using contains_acc.
Qed.

Lemma nope : forall m ad ad' v,
  ad <> ad' ->
  access m v ad ->
  access m[ad' <- v] v ad.
Proof.
  intros * Hneq H. induction H; eauto using access; auto_specialize.
  - admit.
  - eapply access_new.
Abort.

Lemma mem_set_acc : forall m t ad ad' v,
  ad <> ad' ->
  access m t ad ->
  access m v ad ->
  access m[ad' <- v] t ad.
Proof.
  intros * ? Hacc ?. induction Hacc; eauto using access.
  do 2 auto_specialize.
  rename ad'0 into ad''.
  eapply access_mem; trivial.
  assert (ad'' < length m) by admit.
  destruct (Nat.eq_dec ad' ad''); subst; simpl_array; trivial.
  destruct (access_dec m v ad''); eauto using mem_set_preserves_acc1.
  (* TODO : (~ access m m[ad] ad)  levaria à contradiction *)
  
Abort.

Lemma mem_set_sacc : forall m t ad ad' v,
  ad <> ad' ->
  SafeAccess m t ad ->
  SafeAccess m v ad ->
  SafeAccess m[ad' <- v] t ad.
Proof.
  intros * Hneq Hsacc ?. induction Hsacc; eauto using SafeAccess.
  - rename ad'0 into ad''.
    eapply sacc_memI; trivial.
    assert (ad'' < length m) by admit.
    destruct (Nat.eq_dec ad'' ad'); subst; simpl_array.
    + admit.
    + admit.
  - admit.
  - do 2 auto_specialize.
    destruct (access_dec m t2 ad').
    + admit.
    + eauto using mem_set_preserves_nacc2, SafeAccess.
Abort.

Lemma one_more_time : forall m t ad ad' v,
  ~ SafeAccess m[ad' <- v] t ad ->
  (~ SafeAccess m t ad \/ ~ SafeAccess m v ad).
Proof.
  intros. eapply not_and_or. intros [? ?].
Abort.

Lemma again : forall m ad ad' v T,
  value v ->
  value m[ad'] ->
  empty |-- m[ad'] is T ->
  empty |-- v is T ->
  SafeAccess m m[ad'] ad ->
  SafeAccess m v ad ->
  SafeAccess m[ad' <- v] v ad.
Proof.
  intros * Hval1 Hval2 Htype1 Htype2 ? ?.
  destruct Hval1; try solve [inversion_sacc].
  - inversion Htype2; subst.
    + destruct Hval2; try solve [inversion_sacc].
      * inversion Htype1; subst.
        inversion_sacc.
        inversion_sacc.
        eapply sacc_memM; trivial.
        assert (ad0 < length m) by admit.
        destruct (Nat.eq_dec ad' ad0); subst; simpl_array.
        ** eapply sacc_memM; trivial.
           simpl_array.
           eapply sacc_memM; trivial.
           simpl_array.
           eapply sacc_memM; trivial.
           simpl_array.
           eapply sacc_memM; trivial.
           simpl_array.
           eapply sacc_memM; trivial.
           simpl_array.
           eapply sacc_memM; trivial.
           simpl_array.
Abort.


Local Lemma todo : forall m t ad ad' v,
  SafeAccess m t ad ->
  access m[ad' <- v] t ad ->
  SafeAccess m[ad' <- v] t ad.
Proof.
Abort.

Lemma mstep_write_preserves_sacc : forall m m' t t' ad ad' v,
  SafeAccess m t ad ->
  m / t ==[EF_Write ad' v]==> m' / t' ->
  access m' t' ad ->
  SafeAccess m' t' ad.
Proof.
  intros. inversion_mstep. induction_step;
  try solve [inversion_sacc; inversion_access; eauto using SafeAccess].
  - inversion_sacc.
    + inversion_access.
      * do 3 auto_specialize.
        destruct (access_dec m[ad' <- v] t2 ad); eauto using SafeAccess.
        eapply sacc_asg; eauto.

        destruct (access_dec m t2 ad'); eauto using mem_set_preserves_sacc1.
        destruct (access_dec m v ad).
        ** assert (SafeAccess m v ad)
              by eauto using step_write_contains_val, contains_sacc.
           admit.
        ** admit.
Abort.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Definition UnsafeAccess m t ad :=
  access m t ad /\ ~ SafeAccess m t ad.

(* TODO: session for examples! *)

