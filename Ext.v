From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Sem.

(* ------------------------------------------------------------------------- *)
(* step tactics                                                              *)
(* ------------------------------------------------------------------------- *)

Ltac inv_tstep := match goal with H : _     --[_]-->    _     |- _ => inv H end.
Ltac inv_mstep := match goal with H : _ / _ ==[_]==>    _ / _ |- _ => inv H end.
Ltac inv_cstep := match goal with H : _ / _ ~~[_, _]~~> _ / _ |- _ => inv H end.
Ltac inv_mulst := match goal with H : _ / _ ~~[_]~~>*   _ / _ |- _ => inv H end.

Ltac invc_mstep :=
  match goal with H : _ / _ ==[_]==>    _ / _ |- _ => invc H end.
Ltac invc_cstep :=
  match goal with H : _ / _ ~~[_, _]~~> _ / _ |- _ => invc H end.
Ltac invc_mulst :=
  match goal with H : _ / _ ~~[_]~~>*   _ / _ |- _ => invc H end.

Ltac induction_tstep :=
  match goal with H : _ --[?e]--> _ |- _ =>
    remember e eqn:Heq; induction H; inv Heq
  end.

Ltac induction_mulst :=
  match goal with
  | H : _ / _ ~~[_]~~>* _ / _ |- _ =>
    induction H as [| ? ? ? ? ? ? ? ? ? Hmulst ? Hcstep]
  end.

(* ------------------------------------------------------------------------- *)
(* type tactics                                                              *)
(* ------------------------------------------------------------------------- *)

Ltac inv_type :=
  match goal with
  | H : _ |-- <{ unit     }> is _ |- _ => inv H
  | H : _ |-- <{ N _      }> is _ |- _ => inv H
  | H : _ |-- <{ & _ :: _ }> is _ |- _ => inv H
  | H : _ |-- <{ new _ _  }> is _ |- _ => inv H
  | H : _ |-- <{ * _      }> is _ |- _ => inv H
  | H : _ |-- <{ _ = _    }> is _ |- _ => inv H
  | H : _ |-- <{ var _    }> is _ |- _ => inv H
  | H : _ |-- <{ fn _ _ _ }> is _ |- _ => inv H
  | H : _ |-- <{ call _ _ }> is _ |- _ => inv H
  | H : _ |-- <{ _ ; _    }> is _ |- _ => inv H
  | H : _ |-- <{ spawn _  }> is _ |- _ => inv H
  end.

Ltac invc_type :=
  match goal with
  | H : _ |-- <{ unit     }> is _ |- _ => invc H
  | H : _ |-- <{ N _      }> is _ |- _ => invc H
  | H : _ |-- <{ & _ :: _ }> is _ |- _ => invc H
  | H : _ |-- <{ new _ _  }> is _ |- _ => invc H
  | H : _ |-- <{ * _      }> is _ |- _ => invc H
  | H : _ |-- <{ _ = _    }> is _ |- _ => invc H
  | H : _ |-- <{ var _    }> is _ |- _ => invc H
  | H : _ |-- <{ fn _ _ _ }> is _ |- _ => invc H
  | H : _ |-- <{ call _ _ }> is _ |- _ => invc H
  | H : _ |-- <{ _ ; _    }> is _ |- _ => invc H
  | H : _ |-- <{ spawn _  }> is _ |- _ => invc H
  end.

Ltac induction_type :=
  match goal with
  | H : _ |-- _ is _ |- _ => induction H
  end.

(* ------------------------------------------------------------------------- *)
(* dec                                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma value_dec : forall t,
  value t \/ ~ value t.
Proof.
  intros. induction t; eauto using value; right; intros F; inv F.
Qed.

Lemma ityp_eq_dec : forall (T1 T2 : ityp),
  {T1 = T2} + {T1 <> T2}.
Proof. intros. decide equality; eauto. Qed.

Lemma typ_eq_dec : forall (T1 T2 : typ),
  {T1 = T2} + {T1 <> T2}.
Proof. intros. decide equality; eauto using ityp_eq_dec. Qed.

Lemma tm_eq_dec : forall (t1 t2 : tm),
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros. decide equality; eauto using nat_eq_dec, string_eq_dec, typ_eq_dec.
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
  forall_array memory_default (fun tT => P (fst tT)) m.

Definition forall_threads (ths : threads) (P : tm -> _) : Prop :=
  forall_array thread_default P ths.

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

Lemma tstep_length_tid : forall t ths tid e,
  ths[tid] --[e]--> t ->
  tid < #ths.
Proof.
  intros. decompose sum (lt_eq_lt_dec tid (#ths)); subst; trivial;
  simpl_array; try lia; inv_tstep.
Qed.

Lemma mstep_length_tid : forall m m' t' ths tid e,
  m / ths[tid] ==[e]==> m' / t' ->
  tid < #ths.
Proof.
  intros. inv_mstep; eauto using tstep_length_tid.
Qed.

Lemma cstep_length_tid : forall m m' ths ths' tid e,
  m / ths ~~[tid, e]~~> m' / ths' ->
  tid < #ths.
Proof.
  intros. inv_cstep; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* hints                                                                     *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Unfold forall_array   : fall.
#[export] Hint Unfold forall_memory  : fall.
#[export] Hint Unfold forall_threads : fall.

#[export] Hint Extern 4 => unfold forall_array   : fall.
#[export] Hint Extern 4 => unfold forall_memory  : fall.
#[export] Hint Extern 4 => unfold forall_threads : fall.

(* ------------------------------------------------------------------------- *)
(* context equivalences                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma ctx_eqv_safe : forall Gamma1 Gamma2,
  Gamma1 === Gamma2 ->
  safe Gamma1 === safe Gamma2.
Proof.
  unfold map_equivalence, safe. intros * Heq k.
  specialize (Heq k). rewrite Heq. trivial.
Qed.

Lemma ctx_eqv_typing  : forall Gamma1 Gamma2 t T,
  Gamma1 === Gamma2 ->
  Gamma1 |-- t is T ->
  Gamma2 |-- t is T.
Proof.
  intros. generalize dependent Gamma2. induction_type; intros;
  eauto using type_of, ctx_eqv_safe,
    MapEquivalence.lookup, MapEquivalence.update_equivalence.
Qed.

Lemma ctx_eqv_safe_lookup : forall Gamma x,
  Gamma x = None ->
  (safe Gamma) x = None.
Proof.
  unfold safe. intros * H. rewrite H. reflexivity.
Qed.
