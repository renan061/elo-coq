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
  | H : _ |-- <{unit                  }> is _ |- _ => tt H
  | H : _ |-- <{nat _                 }> is _ |- _ => tt H
  | H : _ |-- <{_ + _                 }> is _ |- _ => tt H
  | H : _ |-- <{_ - _                 }> is _ |- _ => tt H
  | H : _ |-- <{_; _                  }> is _ |- _ => tt H
  | H : _ |-- <{if _ then _ else _ end}> is _ |- _ => tt H
  | H : _ |-- <{while _ do _ end      }> is _ |- _ => tt H
  | H : _ |-- <{var _                 }> is _ |- _ => tt H
  | H : _ |-- <{fn _ _ _              }> is _ |- _ => tt H
  | H : _ |-- <{call _ _              }> is _ |- _ => tt H
  | H : _ |-- <{& _ : _               }> is _ |- _ => tt H
  | H : _ |-- <{new _ : _             }> is _ |- _ => tt H
  | H : _ |-- <{init _ _ : _          }> is _ |- _ => tt H
  | H : _ |-- <{* _                   }> is _ |- _ => tt H
  | H : _ |-- <{_ := _                }> is _ |- _ => tt H
  | H : _ |-- <{acq _ _ _             }> is _ |- _ => tt H
  | H : _ |-- <{cr _ _                }> is _ |- _ => tt H
  | H : _ |-- <{spawn _               }> is _ |- _ => tt H
  end.

Ltac inv_typeof  := _typeof inv.
Ltac invc_typeof := _typeof invc.

Ltac ind_typeof := match goal with H : _ |-- _ is _ |- _ => induction H end.

(* ------------------------------------------------------------------------- *)
(* step inversion & induction                                                *)
(* ------------------------------------------------------------------------- *)

Ltac _tstep tt := match goal with H : _     --[_]-->     _     |- _ => tt H end.
Ltac _mstep tt := match goal with H : _ / _ ==[_]==>     _ / _ |- _ => tt H end.
Ltac _cstep tt := match goal with H : _ / _ ~~[_, _]~~>  _ / _ |- _ => tt H end.
Ltac _rstep tt := match goal with H : _ / _ ~~~[_, _]~~> _ / _ |- _ => tt H end.
Ltac _ustep tt := match goal with H : _ / _ ~~[_]~~>*    _ / _ |- _ => tt H end.

Ltac inv_tstep := _tstep inv.
Ltac inv_mstep := _mstep inv.
Ltac inv_cstep := _cstep inv.
Ltac inv_rstep := _rstep inv.
Ltac inv_ustep := _ustep inv.

Ltac invc_tstep := _tstep invc.
Ltac invc_mstep := _mstep invc.
Ltac invc_cstep := _cstep invc.
Ltac invc_rstep := _rstep invc.
Ltac invc_ustep := _ustep invc.

Ltac ind_tstep :=
  match goal with H : _ --[?e]--> _ |- _ =>
    remember e eqn:Heqe; induction H; inv Heqe; clean
  end.

Ltac ind_ustep :=
  match goal with H : _ / _ ~~[?tc]~~>* _ / _ |- _ =>
    induction H as [| ? ? ? ? ? ? ? ? ? Hustep ? Hrstep]
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
  intros. decide equality; eauto using _nat_eq_dec, _str_eq_dec, typ_eq_dec.
Qed.

Lemma eff_eq_dec : forall (e1 e2 : eff),
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros. decide equality; eauto using _nat_eq_dec, typ_eq_dec, tm_eq_dec.
Qed.

(* ------------------------------------------------------------------------- *)
(* forall & forone properties                                                *)
(* ------------------------------------------------------------------------- *)

Definition forall_memory (m : mem) (P : tm -> Prop) : Prop :=
  forall ad t, m[ad].t = Some t -> P t.

Definition forall_threads (ths : threads) (P : tm -> _) : Prop :=
  forall_array tm_default P ths.

Definition forall_program (m : mem) (ths : threads) (P : tm -> _) : Prop :=
  (forall_memory m P) /\ (forall_threads ths P).

(* P1 holds for one thread. P2 holds for the other threads. *)
Definition forone_thread (ths : threads) (P1: tm -> Prop) (P2 : tm -> Prop) :=
  exists tid, P1 ths[tid] /\ forall tid', tid <> tid' -> P2 ths[tid'].

(* ------------------------------------------------------------------------- *)
(* determinism                                                               *)
(* ------------------------------------------------------------------------- *)

Lemma deterministic_typing : forall Gamma t T1 T2,
  Gamma |-- t is T1 ->
  Gamma |-- t is T2 ->
  T1 = T2.
Proof.
  intros * Htype1. generalize dependent T2.
  induction Htype1; intros ? Htype2; inv Htype2; trivial;
  repeat match goal with
  | IH : forall _, _ |-- ?t is _ -> _
  , H  : _ |-- ?t is _ |- _ =>
    eapply IH in H; subst
  end; try congruence.
  repeat match goal with H : `x&_` = `x&_` |- _ => invc H end.
  auto.
Qed.

Ltac apply_deterministic_typing :=
  match goal with
  | H1 : _ |-- ?t is ?T1
  , H2 : _ |-- ?t is ?T2
  |- _ =>
    assert (Heqty : T1 = T2) by eauto using deterministic_typing; subst;
    try (invc Heqty)
  end.

(* ------------------------------------------------------------------------- *)
(* auxiliary lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma tstep_tid_bound : forall t ths tid e,
  ths[tid] --[e]--> t ->
  tid < #ths.
Proof.
  intros. lt_eq_gt tid (#ths); trivial; sigma; inv_tstep.
Qed.

Lemma mstep_tid_bound : forall m m' t' ths tid e,
  m / ths[tid] ==[e]==> m' / t' ->
  tid < #ths.
Proof.
  intros. invc_mstep; eauto using tstep_tid_bound.
Qed.

Lemma cstep_tid_bound : forall m m' ths ths' tid e,
  m / ths ~~[tid, e]~~> m' / ths' ->
  tid < #ths.
Proof.
  intros. invc_cstep; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* context weakening                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma safe_preserves_inclusion : forall Gamma1 Gamma2,
  Gamma1 includes Gamma2 ->
  (safe Gamma1) includes (safe Gamma2).
Proof.
  unfold inclusion, safe. intros * H *.
  destruct (Gamma1 k) eqn:E1; destruct (Gamma2 k) eqn:E2;
  solve [ intros F; inv F
        | eapply H in E2; rewrite E1 in E2; inv E2; trivial
        ].
Qed.

Lemma update_safe_includes_safe_update : forall Gamma k T,
  (safe Gamma)[k <== T] includes (safe Gamma[k <== T]).
Proof.
  intros ? ? ? k' ? H. unfold safe in H. str_eq_dec k k'.
  - rewrite lookup_update_eq in *. destruct T; inv H; trivial.
  - rewrite lookup_update_neq in *; trivial.
Qed.

Lemma context_weakening : forall Gamma1 Gamma2 t T,
  Gamma2 |-- t is T ->
  Gamma1 includes Gamma2 ->
  Gamma1 |-- t is T.
Proof.
  intros. generalize dependent Gamma1.
  ind_typeof; intros;
  eauto 6 using type_of, safe_preserves_inclusion, MapInc.update_inclusion.
Qed.

Corollary context_weakening_empty : forall Gamma t T,
  empty |-- t is T ->
  Gamma |-- t is T.
Proof.
  intros. eapply (context_weakening _ empty); trivial. discriminate.
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
  intros. gendep Gamma2. ind_typeof; intros;
  eauto 6 using MapEqv.lookup, MapEqv.update_eqv, type_of, ctx_eqv_safe.
Qed.

Lemma ctx_eqv_safe_lookup : forall Gamma x,
  Gamma x = None ->
  (safe Gamma) x = None.
Proof.
  unfold safe. intros * H. rewrite H. reflexivity.
Qed.

Lemma empty_eq_safe_empty :
  empty = safe empty.
Proof. eauto. Qed.

#[export] Hint Extern 4 =>
  match goal with
  | H : safe empty |-- _ is _ |- _ => rewrite empty_eq_safe_empty in H
  | _ : _ |- safe empty |-- _ is _ => rewrite empty_eq_safe_empty
  end : core.

(* ------------------------------------------------------------------------- *)
(* lookup-update on types                                                    *)
(* ------------------------------------------------------------------------- *)

Corollary safe_safe_lookup_update_eq_some : forall Gamma x T,
  safe Gamma[x <== `Safe T`] x = Some `Safe T`.
Proof.
  intros. unfold safe. rewrite lookup_update_eq. reflexivity.
Qed.

Corollary safe_refW_lookup_update_eq_none : forall Gamma x T,
  safe Gamma[x <== `w&T`] x = None.
Proof.
  intros. unfold safe. rewrite lookup_update_eq. reflexivity.
Qed.

Corollary safe_fun_lookup_update_eq_none : forall Gamma x T1 T2,
  safe Gamma[x <== `T1 --> T2`] x = None.
Proof.
  intros. unfold safe. rewrite lookup_update_eq. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* misc. tactics                                                             *)
(* ------------------------------------------------------------------------- *)

Ltac value_does_not_step :=
  match goal with
  | H1 : value ?t
  , H2 : ?t --[_]--> _
  |- _ =>
    solve [invc H1; inv H2]
  end.

(* ------------------------------------------------------------------------- *)
(* base                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma forallmemory_base : forall P,
  forall_memory nil P.
Proof.
  unfold forall_memory. simpl. repeat intro.
  destruct ad; simpl in *; auto.
Qed.

Lemma forallprogram_base : forall (P : tm -> Prop) t,
  P <{unit}> ->
  P t ->
  forall_program nil (base t) (fun t' => P t').
Proof.
  unfold base. intros. split.
  - intros ? ? Had. simpl in Had. destruct ad; simpl in Had; auto.
  - intros ad. nat_eq_dec 0 ad; simpl; trivial. repeat (destruct ad; trivial).
Qed.

