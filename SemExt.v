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
  | H : _ |-- <{unit        }> is _ |- _ => tt H
  | H : _ |-- <{nat _       }> is _ |- _ => tt H
  | H : _ |-- <{var _       }> is _ |- _ => tt H
  | H : _ |-- <{fn _ _ _    }> is _ |- _ => tt H
  | H : _ |-- <{call _ _    }> is _ |- _ => tt H
  | H : _ |-- <{& _ : _     }> is _ |- _ => tt H
  | H : _ |-- <{new _ : _   }> is _ |- _ => tt H
  | H : _ |-- <{init _ _ : _}> is _ |- _ => tt H
  | H : _ |-- <{* _         }> is _ |- _ => tt H
  | H : _ |-- <{_ := _      }> is _ |- _ => tt H
  | H : _ |-- <{acq _ _     }> is _ |- _ => tt H
  | H : _ |-- <{cr _ _      }> is _ |- _ => tt H
  | H : _ |-- <{spawn _     }> is _ |- _ => tt H
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
    remember e eqn:Heqe; induction H; inv Heqe; clean
  end.

Ltac ind_ustep :=
  match goal with H : _ / _ ~~[?tc]~~>* _ / _ |- _ =>
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
  intros. decide equality; eauto using nat_eq_dec, str_eq_dec, typ_eq_dec.
Qed.

Lemma eff_eq_dec : forall (e1 e2 : eff),
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros. decide equality; eauto using nat_eq_dec, typ_eq_dec, tm_eq_dec.
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
  intros. decompose sum (lt_eq_lt_dec tid (#ths)); subst; trivial;
  sigma; inv_tstep.
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

(* ------------------------------------------------------------------------- *)

Lemma empty_eq_safe_empty :
  empty = safe empty.
Proof. eauto. Qed.

#[export] Hint Extern 4 =>
  match goal with
  | H : safe empty |-- _ is _ |- _ => rewrite empty_eq_safe_empty in H
  | _ : _ |- safe empty |-- _ is _ => rewrite empty_eq_safe_empty
  end : core.

(* ------------------------------------------------------------------------- *)
(* upsilon simplification                                                    *)
(* ------------------------------------------------------------------------- *)

Local Lemma setx_get_eq : forall m ad ad' X,
  m[ad.X <- X][ad'].t = m[ad'].t.
Proof.
  intros. repeat omicron; trivial.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma add_get_eq_none : forall m ad T,
  (m +++ (None, T, false))[ad].t = None ->
  m[ad].t = None.
Proof.
  intros. omicron; eauto.
Qed.

Local Lemma add_get_neq_none : forall m ad T,
  (m +++ (None, T, false))[ad].t <> None ->
  (m[ad].t <> None /\ ad < #m).
Proof.
  intros. omicron; eauto.
Qed.

Local Lemma set_get_eq_none : forall m ad ad' t,
  ad' < #m ->
  m[ad'.t <- t][ad].t = None ->
  (m[ad].t = None /\ ad <> ad').
Proof.
  intros. repeat omicron; eauto. discriminate.
Qed.

Local Lemma set_get_neq_none : forall m ad ad' t,
  ad <> ad'->
  m[ad'.t <- t][ad].t <> None ->
  m[ad].t <> None.
Proof.
  intros. destruct (nat_eq_dec ad' ad); subst; sigma; eauto.
Qed.
   
(* ------------------------------------------------------------------------- *)

Local Lemma forallprogram_step {P : tm -> Prop} : forall m ths tid t,
  P <{unit}> ->
  P t ->
  forall_program m ths P ->
  forall_program m ths[tid <- t] P.
Proof.
  intros * ? ? [? ?]. split; trivial.
  intros ?. repeat omicron; eauto.
Qed.

Local Lemma forallprogram_add_step {P : tm -> Prop} : forall m ths tid t T,
  P <{unit}> ->
  P t ->
  forall_program m ths P ->
  forall_program (m +++ (None, T, false)) ths[tid <- t] P.
Proof.
  intros * ? ? [? ?]. split.
  - intros until 1. omicron; eauto; discriminate.
  - intros ?. repeat omicron; trivial.
Qed.

Local Lemma forallprogram_sett_step {P : tm -> Prop} :
  forall m ths ad t1 tid t2,
    P <{unit}> ->
    (P t1 /\ P t2) -> 
    forall_program m ths P ->
    forall_program m[ad.t <- t1] ths[tid <- t2] P.
Proof.
  intros * ? [? ?] [? ?]. split.
  - intros until 1. repeat omicron; eauto.
    + discriminate.
    + invc_eq. assumption.
  - intros ?. repeat omicron; trivial.
Qed.

Local Lemma forallprogram_setx_step {P : tm -> Prop} : forall m ths ad X tid t,
  P <{unit}> ->
  P t ->
  forall_program m ths P ->
  forall_program m[ad.X <- X] ths[tid <- t] P.
Proof.
  intros * ? ? [? ?]. split.
  - intros until 1. repeat omicron; eauto. discriminate.
  - intros ?. repeat omicron; trivial.
Qed.

Local Lemma forallprogram_spawn {P : tm -> Prop} : forall m ths tid t1 t2,
  P <{unit}> ->
  (P t1 /\ P t2) -> 
  forall_program m ths P ->
  forall_program m (ths[tid <- t1] +++ t2) P.
Proof.
  intros * ? [? ?] [? ?]. split.
  - intros until 1. repeat omicron; eauto.
  - intros ?. repeat omicron; trivial.
Qed.

(* ------------------------------------------------------------------------- *)

Ltac upsilon_once :=
  match goal with
  (* ---------------------------------------- *)
  (* setx-get-eq                              *)
  (* ---------------------------------------- *)
  | H : context C [ _[_.X <- _][_].t ] |- _ => rewrite setx_get_eq in H
  |  |- context C [ _[_.X <- _][_].t ]      => rewrite setx_get_eq 
  (* ---------------------------------------- *)
  (* add-get-eq-none                          *)
  (* ---------------------------------------- *)
  | H : (_ +++ (None, _, false))[_].t = None |- _ =>
    eapply add_get_eq_none in H
  (* ---------------------------------------- *)
  (* add-get-neq-none                         *)
  (* ---------------------------------------- *)
  | H : (_ +++ (None, _, false))[_].t <> None |- _ =>
    eapply add_get_neq_none in H as [?Ha ?Hb]; clear H
  (* ---------------------------------------- *)
  (* set-get-eq-none                          *)
  (* ---------------------------------------- *)
  | Had : ?ad < #?m, H : ?m[?ad.t <- _][_].t = None |- _ =>
    eapply set_get_eq_none in H as [?Ha ?Hb]; trivial; clear H
  (* ---------------------------------------- *)
  (* set-get-neq-none                          *)
  (* ---------------------------------------- *)
  | Had : ?ad <> ?ad', H : ?m[?ad.t <- _][?ad'].t = None |- _ =>
    eapply set_get_neq_none in H; trivial
  (* ---------------------------------------- *)
  (* forall-program goals                     *)
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program ?m ?ths[_ <- _] ?P =>
    eapply forallprogram_step; eauto; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program (?m +++ (None, _, false)) ?ths[_ <- _] ?P =>
    eapply forallprogram_add_step; eauto; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program ?m[_.t <- _] ?ths[_ <- _] ?P =>
    eapply forallprogram_sett_step; eauto; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program ?m[_.X <- _] ?ths[_ <- _] ?P =>
    eapply forallprogram_setx_step; eauto; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program ?m (?ths[_ <- _] +++ _) ?P =>
      eapply forallprogram_spawn; eauto; try solve [constructor]
  end.

Ltac upsilon := repeat upsilon_once.

