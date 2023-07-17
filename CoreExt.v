From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* dec                                                                       *)
(* ------------------------------------------------------------------------- *)

Theorem ityp_eq_dec : forall (T1 T2 : ityp),
  {T1 = T2} + {T1 <> T2}.
Proof. intros. decide equality; eauto. Qed.

Theorem typ_eq_dec : forall (T1 T2 : typ),
  {T1 = T2} + {T1 <> T2}.
Proof. intros. decide equality; eauto using ityp_eq_dec. Qed.

Theorem tm_eq_dec : forall (t1 t2 : tm),
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros. decide equality; eauto using nat_eq_dec, string_eq_dec, typ_eq_dec.
Qed.

Theorem effect_eq_dec : forall (e1 e2 : effect),
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros. decide equality; eauto using nat_eq_dec, typ_eq_dec, tm_eq_dec.
Qed.

(* ------------------------------------------------------------------------- *)
(* array properties                                                          *)
(* ------------------------------------------------------------------------- *)

Definition forall_memory (m : mem) (P : tm -> _) : Prop :=
  forall_array memory_default (fun tT => P (fst tT)) m.

Definition forall_threads (ths : threads) (P : tm -> _) : Prop :=
  forall_array thread_default P ths.

Definition forall_program (m : mem) (ths : threads) (P : tm -> _) : Prop :=
  (forall_memory m P) /\ (forall_threads ths P).

#[export] Hint Unfold forall_program : core.

Definition well_typed_term (t : tm) := exists T, empty |-- t is T.

(* ------------------------------------------------------------------------- *)
(* determinism                                                               *)
(* ------------------------------------------------------------------------- *)

Lemma deterministic_typing : forall Gamma t T1 T2,
  Gamma |-- t is T1 ->
  Gamma |-- t is T2 ->
  T1 = T2.
Proof.
  intros * Htype1. generalize dependent T2.
  induction Htype1; intros ? Htype2;
  inversion Htype2; subst; eauto;
  repeat match goal with
  | IH : forall _, _ |-- ?t is _ -> _, H : _ |-- ?t is _ |- _ =>
    eapply IH in H; subst
  end;
  congruence.
Qed.

Ltac apply_deterministic_typing :=
  match goal with
  | H1 : _ |-- ?t is ?T1, H2 : _ |-- ?t is ?T2 |- _ =>
    assert (Heq : T1 = T2) by eauto using deterministic_typing; subst;
    try (inversion Heq; subst; clear Heq)
  end.

(* ------------------------------------------------------------------------- *)
(* auxiliary tactics                                                         *)
(* ------------------------------------------------------------------------- *)

Ltac induction_step :=
  match goal with
  | H : _ --[?e]--> _ |- _ =>
    remember e as eff; induction H; inversion Heqeff; subst
  end.

Ltac inversion_step :=
  match goal with
  | H : _ --[_]--> _ |- _ => inversion H; subst; clear H
  end.

Ltac inversion_mstep :=
  match goal with
  | H : _ / _ ==[_]==> _ / _ |- _ => inversion H; subst
  end.

Ltac inversion_clear_mstep :=
  match goal with
  | H : _ / _ ==[_]==> _ / _ |- _ => inversion_subst_clear H
  end.

Ltac inversion_cstep :=
  match goal with
  | H : _ / _ ~~[_, _]~~> _ / _ |- _ => inversion H; subst
  end.

Ltac inversion_clear_cstep :=
  match goal with
  | H : _ / _ ~~[_, _]~~> _ / _ |- _ => inversion_subst_clear H
  end.

Ltac induction_multistep :=
  match goal with
  | H : _ / _ ~~[_]~~>* _ / _ |- _ => induction H
  end.

Ltac inversion_multistep :=
  match goal with
  | H : _ / _ ~~[_]~~>* _ / _ |- _ => inversion H; subst
  end.

Ltac inversion_clear_multistep :=
  match goal with
  | H : _ / _ ~~[_]~~>* _ / _ |- _ => inversion_subst_clear H
  end.

Ltac induction_type :=
  match goal with
  | H : _ |-- _ is _ |- _ => induction H
  end.

Ltac inversion_type :=
  match goal with
  | H : _ |-- <{ unit     }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ N _      }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ & _ :: _ }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ new _ _  }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ * _      }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ _ = _    }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ var _    }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ fn _ _ _ }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ call _ _ }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ _ ; _    }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ spawn _  }> is _ |- _ => inversion H; subst
  end.

Ltac inversion_clear_type :=
  match goal with
  | H : _ |-- <{ unit     }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ N _      }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ & _ :: _ }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ new _ _  }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ * _      }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ _ = _    }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ var _    }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ fn _ _ _ }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ call _ _ }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ _ ; _    }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ spawn _  }> is _ |- _ => inversion_subst_clear H
  end.

(* ------------------------------------------------------------------------- *)
(* auxiliary lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma step_length_tid : forall t ths tid e,
  ths[tid] --[e]--> t ->
  tid < #ths.
Proof.
  intros. decompose sum (lt_eq_lt_dec tid (#ths)); subst; trivial;
  simpl_array; try lia; inversion_step.
Qed.

Corollary mstep_length_tid : forall m m' t' ths tid e,
  m / ths[tid] ==[e]==> m' / t' ->
  tid < #ths.
Proof.
  intros. inversion_mstep; eauto using step_length_tid.
Qed.

Corollary cstep_length_tid : forall m m' ths ths' tid e,
  m / ths ~~[tid, e]~~> m' / ths' ->
  tid < #ths.
Proof.
  intros. inversion_cstep; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* meta                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma cstep_preservation :
  forall (P : mem -> tm -> Prop) m m' ths ths' tid e,
    (* Memory step preserves the property. *)
    (forall tid' t',
      m / ths[tid'] ==[e]==> m' / t' ->
      P m' t'
    ) ->
    (* The untouched threads and the new memory still preserve the property. *)
    (forall tid' t',
      tid <> tid' ->
      tid' < #ths ->
      m / ths[tid] ==[e]==> m' / t' ->
      P m' ths[tid']
    ) ->
    (* The new thread preserves the property. *)
    (forall block t',
      ths[tid] --[EF_Spawn block]--> t' ->
      P m block
    ) ->
    (* The term after the spawn preserves the property. *)
    (forall block t',
      ths[tid] --[EF_Spawn block]--> t' ->
      P m t' 
    ) ->
    (* `unit` preserves the property. *)
    P m' thread_default ->
    (* What we want to prove. *)
    forall_threads ths (P m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' (P m').
Proof.
  intros. inversion_cstep; intros tid'.
  - destruct (nat_eq_dec tid' (#ths)); subst.
    + rewrite <- (set_preserves_length _ tid t'). simpl_array. eauto.
    + destruct (lt_eq_lt_dec tid' (length ths)) as [[Ha | ?] | Hb]; subst;
      try lia.
      * rewrite <- (set_preserves_length _ tid t') in Ha. simpl_array.
        destruct (nat_eq_dec tid tid'); subst; simpl_array; eauto.
      * rewrite <- (set_preserves_length _ tid t') in Hb. simpl_array. eauto.
  - destruct (nat_eq_dec tid tid'); subst; simpl_array; eauto.
    decompose sum (lt_eq_lt_dec tid' (#ths)); subst; eauto;
    simpl_array; eauto.
Qed.
