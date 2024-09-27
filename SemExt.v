From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Sem.

(* ------------------------------------------------------------------------- *)
(* typeof inversion & induction                                              *)
(* ------------------------------------------------------------------------- *)

Ltac _typeof tt :=
  match goal with
  | H : _ |-- <{unit     }> is _ |- _ => tt H
  | H : _ |-- <{nat _    }> is _ |- _ => tt H
  | H : _ |-- <{var _    }> is _ |- _ => tt H
  | H : _ |-- <{fn _ _ _ }> is _ |- _ => tt H
  | H : _ |-- <{call _ _ }> is _ |- _ => tt H
  | H : _ |-- <{& _ : _  }> is _ |- _ => tt H
  | H : _ |-- <{new _ : _}> is _ |- _ => tt H
  | H : _ |-- <{* _      }> is _ |- _ => tt H
  | H : _ |-- <{_ := _   }> is _ |- _ => tt H
  | H : _ |-- <{acq _ _  }> is _ |- _ => tt H
  | H : _ |-- <{cr _ _   }> is _ |- _ => tt H
  | H : _ |-- <{ptm _ _  }> is _ |- _ => tt H
  | H : _ |-- <{spawn _  }> is _ |- _ => tt H
  end.

Ltac inv_typeof  := _typeof inv.
Ltac invc_typeof := _typeof invc.

Ltac ind_typeof := match goal with H : _ |-- _ is _ |- _ => induction H end.

(* ------------------------------------------------------------------------- *)
(* step inversion & induction                                                *)
(* ------------------------------------------------------------------------- *)

Ltac _tstep tt := match goal with H : _     --[_]-->    _     |- _ => tt H end.
Ltac _mstep tt := match goal with H : _ / _ ==[_]==>    _ / _ |- _ => tt H end.
Ltac _cstep tt := match goal with H : _ / _ ~~[_, _]~~> _ / _ |- _ => tt H end.
Ltac _ustep tt := match goal with H : _ / _ ~~[_]~~>*   _ / _ |- _ => tt H end.

Ltac inv_tstep := _tstep inv.
Ltac inv_mstep := _mstep inv.
Ltac inv_cstep := _cstep inv.
Ltac inv_ustep := _ustep inv.

Ltac invc_tstep := _tstep invc.
Ltac invc_mstep := _mstep invc.
Ltac invc_cstep := _cstep invc.
Ltac invc_ustep := _ustep invc.

Ltac ind_tstep :=
  match goal with H : _ --[?e]--> _ |- _ =>
    remember e eqn:Heq; induction H; inv Heq
  end.

Ltac ind_ustep :=
  match goal with H : _ / _ ~~[_]~~>* _ / _ |- _ =>
    induction H as [| ? ? ? ? ? ? ? ? ? Hustep ? Hcstep]
  end.

(* ------------------------------------------------------------------------- *)
(* decidability & equality                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma value_dec : forall t,
  value t \/ ~ value t.
Proof.
  intros. induction t; eauto using value; right; intros F; inv F.
Qed.

Lemma styp_eq_dec : forall (T1 T2 : sty), {T1 = T2} + {T1 <> T2}
with  typ_eq_dec  : forall (T1 T2 : ty),  {T1 = T2} + {T1 <> T2}.
Proof.
  - decide equality.
  - decide equality.
Qed.

Lemma tm_eq_dec : forall (t1 t2 : tm),
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros.
  decide equality; eauto using nat_eq_dec, str_eq_dec, typ_eq_dec.
  decide equality. eauto using nat_eq_dec.
Qed.

Lemma eff_eq_dec : forall (e1 e2 : eff),
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros. decide equality; eauto using nat_eq_dec, typ_eq_dec, tm_eq_dec.
Qed.

(* ------------------------------------------------------------------------- *)
(* forall properties                                                         *)
(* ------------------------------------------------------------------------- *)

Definition forall_memory (m : mem) (P : tm -> _) : Prop :=
  forall_array mem_default (fun tT => P (fst tT)) m.

Definition forall_threads (ths : threads) (P : tm -> _) : Prop :=
  forall_array tm_default P ths.

Definition forall_program (m : mem) (ths : threads) (P : tm -> _) : Prop :=
  (forall_memory m P) /\ (forall_threads ths P).

#[export] Hint Unfold forall_program : core.

(* ------------------------------------------------------------------------- *)
(* determinism                                                               *)
(* ------------------------------------------------------------------------- *)

Lemma deterministic_typing : forall Gamma t T1 T2,
  Gamma |-- t is T1 ->
  Gamma |-- t is T2 ->
  T1 = T2.
Proof.
  intros * Htype1. generalize dependent T2.
  induction Htype1; intros ? Htype2; inv Htype2; eauto;
  repeat match goal with
  | IH : forall _, _ |-- ?t is _ -> _, H : _ |-- ?t is _ |- _ =>
    eapply IH in H; subst
  end;
  congruence.
Qed.

Ltac apply_deterministic_typing :=
  match goal with
  | H1 : _ |-- ?t is ?T1
  , H2 : _ |-- ?t is ?T2
  |- _ =>
    assert (Heq : T1 = T2) by eauto using deterministic_typing; subst;
    try (invc Heq)
  end.

(* ------------------------------------------------------------------------- *)
(* auxiliary lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma tstep_tid_bound : forall t ths tid e,
  ths[tid] --[e]--> t ->
  tid < #ths.
Proof.
  intros. decompose sum (lt_eq_lt_dec tid (#ths)); subst; trivial; simpl_array;
  solve [lia | inv_tstep].
Qed.

Lemma mstep_tid_bound : forall m m' t' ths tid e,
  m / ths[tid] ==[e]==> m' / t' ->
  tid < #ths.
Proof.
  intros. inv_mstep; eauto using tstep_tid_bound.
Qed.

Lemma cstep_tid_bound : forall m m' ths ths' tid e,
  m / ths ~~[tid, e]~~> m' / ths' ->
  tid < #ths.
Proof.
  intros. inv_cstep; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* context equivalence                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma ctx_eqv_safe : forall Gamma1 Gamma2,
  Gamma1 === Gamma2 ->
  safe Gamma1 === safe Gamma2.
Proof.
  unfold map_eqv, safe. intros * Heq k.
  specialize (Heq k). rewrite Heq. trivial.
Qed.

Lemma ctx_eqv_typeof : forall Gamma1 Gamma2 t T,
  Gamma1 === Gamma2 ->
  Gamma1 |-- t is T ->
  Gamma2 |-- t is T.
Proof.
  intros. generalize dependent Gamma2. ind_typeof; intros;
  eauto using MapEqv.lookup, MapEqv.update_eqv, type_of, ctx_eqv_safe.
Qed.

Lemma ctx_eqv_safe_lookup : forall Gamma x,
  Gamma x = None ->
  (safe Gamma) x = None.
Proof.
  unfold safe. intros * H. rewrite H. reflexivity.
Qed.

