From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import ValidTerm.
From Elo Require Import NoWaits.
From Elo Require Import ReservedWaits.
From Elo Require Import ValidWaits.

(* ------------------------------------------------------------------------- *)
(* consistent-waits                                                          *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_waits (o : option addr) : tm -> Prop :=
  | cwaits_unit  :                  consistent_waits o <{unit              }>
  | cwaits_nat   : forall n,        consistent_waits o <{nat n             }>
  | cwaits_plus  : forall t1 t2,    consistent_waits o t1 ->
                                    consistent_waits o t2 ->
                                    consistent_waits o <{t1 + t2           }>
  | cwaits_monus : forall t1 t2,    consistent_waits o t1 ->
                                    consistent_waits o t2 ->
                                    consistent_waits o <{t1 - t2           }>
  | cwaits_seq   : forall t1 t2,    consistent_waits o t1 ->
                                    consistent_waits o t2 ->
                                    consistent_waits o <{t1; t2            }>
  | cwaits_if    : forall t1 t2 t3, consistent_waits o t1 ->
                                    consistent_waits o t2 ->
                                    consistent_waits o t3 ->
                                    consistent_waits o (tm_if t1 t2 t3     )
  | cwaits_while : forall t1 t2,    consistent_waits o t1 ->
                                    consistent_waits o t2 ->
                                    consistent_waits o <{while t1 do t2 end}>
  | cwaits_var   : forall x,        consistent_waits o <{var x             }>
  | cwaits_fun   : forall x Tx t,   consistent_waits o t  ->
                                    consistent_waits o <{fn x Tx t         }>
  | cwaits_call  : forall t1 t2,    consistent_waits o t1 ->
                                    consistent_waits o t2 ->
                                    consistent_waits o <{call t1 t2        }>
  | cwaits_ref   : forall ad T,     consistent_waits o <{&ad : T           }>
  | cwaits_new   : forall t T,      consistent_waits o t  ->
                                    consistent_waits o <{new t : T         }>
  | cwaits_init  : forall ad t T,   consistent_waits o t  ->
                                    consistent_waits o <{init ad t : T     }>
  | cwaits_load  : forall t,        consistent_waits o t  ->
                                    consistent_waits o <{*t                }>
  | cwaits_asg   : forall t1 t2,    consistent_waits o t1 ->
                                    consistent_waits o t2 ->
                                    consistent_waits o <{t1 := t2          }>
  | cwaits_acq   : forall t1 x t2,  consistent_waits o t1 ->
                                    reserved_waits t2     ->
                                    consistent_waits o <{acq t1 x t2       }>
  | cwaits_cr    : forall ad t,     consistent_waits (Some ad) t ->
                                    consistent_waits o <{cr ad t           }>
  | cwaits_wait1 :                  o = None    ->
                                    consistent_waits o <{wait (var SELF)   }>
  | cwaits_wait2 : forall ad T,     o = Some ad ->
                                    consistent_waits o <{wait (&ad : T)    }>
  | cwaits_reacq : forall ad,       consistent_waits o <{reacq ad          }>
  | cwaits_spawn : forall t,        consistent_waits None t ->
                                    consistent_waits o <{spawn t           }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _cwaits tt :=
  match goal with
  | H : consistent_waits _ <{unit                  }> |- _ => clear H
  | H : consistent_waits _ <{nat _                 }> |- _ => clear H
  | H : consistent_waits _ <{_ + _                 }> |- _ => tt H
  | H : consistent_waits _ <{_ - _                 }> |- _ => tt H
  | H : consistent_waits _ <{_; _                  }> |- _ => tt H
  | H : consistent_waits _ <{if _ then _ else _ end}> |- _ => tt H
  | H : consistent_waits _ <{while _ do _ end      }> |- _ => tt H
  | H : consistent_waits _ <{var _                 }> |- _ => tt H
  | H : consistent_waits _ <{fn _ _ _              }> |- _ => tt H
  | H : consistent_waits _ <{call _ _              }> |- _ => tt H
  | H : consistent_waits _ <{&_ : _                }> |- _ => clear H
  | H : consistent_waits _ <{new _ : _             }> |- _ => tt H
  | H : consistent_waits _ <{init _ _ : _          }> |- _ => tt H
  | H : consistent_waits _ <{* _                   }> |- _ => tt H
  | H : consistent_waits _ <{_ := _                }> |- _ => tt H
  | H : consistent_waits _ <{acq _ _ _             }> |- _ => tt H
  | H : consistent_waits _ <{cr _ _                }> |- _ => tt H
  | H : consistent_waits _ <{wait _                }> |- _ => tt H
  | H : consistent_waits _ <{reacq _               }> |- _ => clear H
  | H : consistent_waits _ <{spawn _               }> |- _ => tt H
  end.

Ltac inv_cwaits  := _cwaits inv.
Ltac invc_cwaits := _cwaits invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma cwaits_from_nowaits : forall o t,
  no_waits t ->
  consistent_waits o t.
Proof.
  intros. gendep o. induction t; intros; invc_nowaits;
  auto using rwaits_from_nowaits, consistent_waits.
Qed.

Lemma cwaits_from_rwaits : forall t,
  no_crs t ->
  (* --- *)
  reserved_waits t ->
  consistent_waits None t.
Proof.
  intros. induction t; invc_nocrs; invc_rwaits; auto using consistent_waits.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma cwaits_subst : forall t ad T,
  no_crs t      ->
  valid_waits t ->
  (* --- *)
  reserved_waits t ->
  consistent_waits (Some ad) <{[SELF := &ad : T] t}>.
Proof.
  intros. induction t; invc_nocrs; invc_vwaits; invc_rwaits;
  remember SELF as x; simpl; repeat destruct _str_eq_dec; subst;
  auto using cwaits_from_rwaits, consistent_waits.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_cwaits_preservation :=
  intros o **; gendep o; ind_tstep; intros;
  repeat invc_vtm; repeat invc_vwaits; repeat invc_cwaits; repeat constructor;
  auto using nowaits_from_value, nowaits_subst, cwaits_from_nowaits.

Lemma cwaits_preservation_none : forall o t1 t2,
  valid_waits t1 ->
  (* --- *)
  consistent_waits o t1 ->
  t1 --[e_none]--> t2 ->
  consistent_waits o t2.
Proof. solve_cwaits_preservation. Qed.

Lemma cwaits_preservation_alloc : forall o t1 t2 ad' T',
  consistent_waits o t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  consistent_waits o t2.
Proof. solve_cwaits_preservation. Qed.

Lemma cwaits_preservation_init : forall o t1 t2 ad' t',
  consistent_waits o t1 ->
  t1 --[e_init ad' t']--> t2 ->
  consistent_waits o t2.
Proof. solve_cwaits_preservation. Qed.

Lemma cwaits_preservation_read : forall o t1 t2 ad' t',
  value t'       ->
  valid_waits t' ->
  (* --- *)
  consistent_waits o t1 ->
  t1 --[e_read ad' t']--> t2 ->
  consistent_waits o t2.
Proof. solve_cwaits_preservation. Qed.

Lemma cwaits_preservation_write : forall o t1 t2 ad' t',
  consistent_waits o t1 ->
  t1 --[e_write ad' t']--> t2 ->
  consistent_waits o t2.
Proof. solve_cwaits_preservation. Qed.

Lemma cwaits_preservation_acq : forall o m t1 t2 ad' t',
  value t'        ->
  valid_term m t' ->
  valid_waits  t' ->
  valid_term m t1 ->
  valid_waits  t1 ->
  (* --- *)
  consistent_waits o t1     ->
  t1 --[e_acq ad' t']--> t2 ->
  consistent_waits o t2.
Proof.
  solve_cwaits_preservation.
  eauto 7 using cwaits_subst,
                nocrs_from_value, nocrs_subst,
                vwaits_subst,
                nowaits_from_value, rwaits_subst.
Qed.

Lemma cwaits_preservation_rel : forall o t1 t2 ad',
  valid_waits t1  ->
  (* --- *)
  consistent_waits o t1  ->
  t1 --[e_rel ad']--> t2 ->
  consistent_waits o t2.
Proof. solve_cwaits_preservation. Qed.

Lemma cwaits_preservation_wacq : forall o t1 t2 ad',
  consistent_waits o t1  ->
  t1 --[e_wacq ad']--> t2 ->
  consistent_waits o t2.
Proof. solve_cwaits_preservation. Qed.

Lemma cwaits_preservation_wrel : forall o t1 t2 ad',
  consistent_waits o t1  ->
  t1 --[e_wrel ad']--> t2 ->
  consistent_waits o t2.
Proof. solve_cwaits_preservation. Qed.

Lemma cwaits_preservation_spawn : forall o t1 t2 t',
  consistent_waits o t1  ->
  t1 --[e_spawn t']--> t2 ->
  consistent_waits o t2.
Proof. solve_cwaits_preservation. Qed.

Lemma cwaits_preservation_spawned : forall m t1 t2 t',
  valid_term m t1 ->
  valid_waits  t1 ->
  (* --- *)
  t1 --[e_spawn t']--> t2 ->
  consistent_waits None t'.
Proof.
  eauto using nocrs_spawn_term, rwaits_spawn_term, cwaits_from_rwaits.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem cwaits_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   value           ->
  forall_memory  m1   (valid_term m1) ->
  forall_memory  m1   valid_waits     ->
  forall_threads ths1 (valid_term m1) ->
  forall_threads ths1 valid_waits     ->
  (* --- *)
  forall_threads ths1 (consistent_waits None) ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2           ->
  forall_threads ths2 (consistent_waits None).
Proof.
  intros. invc_cstep; try invc_mstep; upsilon.
  - eauto using cwaits_preservation_none.
  - eauto using cwaits_preservation_alloc.
  - eauto using cwaits_preservation_init.
  - eauto using cwaits_preservation_read.
  - eauto using cwaits_preservation_write.
  - eauto using cwaits_preservation_acq.
  - eauto using cwaits_preservation_rel.
  - eauto using cwaits_preservation_wacq.
  - eauto using cwaits_preservation_wrel.
  - eauto using cwaits_preservation_spawn.
  - eauto using cwaits_preservation_spawned.
Qed.

Theorem cwaits_preservation_base : forall t,
  no_crs         t ->
  reserved_waits t ->
  (* --- *)
  forall_threads (base t) (consistent_waits None).
Proof.
  auto using forallthreads_base, cwaits_from_rwaits, consistent_waits.
Qed.
