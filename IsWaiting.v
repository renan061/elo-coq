From Elo Require Import Core.

From Elo Require Import NoReacq.
From Elo Require Import ValidTerm.

(* ------------------------------------------------------------------------- *)
(* is-waiting                                                                *)
(* ------------------------------------------------------------------------- *)

Inductive is_waiting (ad : addr) : tm -> Prop :=
  | isw_plus1  : forall t1 t2,    is_waiting ad t1 ->
                                  no_reacq   ad t2 ->
                                  is_waiting ad <{t1 + t2               }>
  | isw_plus2  : forall t1 t2,    value t1         ->
                                  is_waiting ad t2 ->
                                  is_waiting ad <{t1 + t2               }>
  | isw_monus1 : forall t1 t2,    is_waiting ad t1 ->
                                  no_reacq   ad t2 ->
                                  is_waiting ad <{t1 - t2               }>
  | isw_monus2 : forall t1 t2,    value t1         ->
                                  is_waiting ad t2 ->
                                  is_waiting ad <{t1 - t2               }>
  | isw_seq    : forall t1 t2,    is_waiting ad t1 ->
                                  is_waiting ad <{t1; t2                }>
  | isw_if     : forall t1 t2 t3, is_waiting ad t1 ->
                                  is_waiting ad (tm_if t1 t2 t3) 
  | isw_call1  : forall t1 t2,    is_waiting ad t1 ->
                                  no_reacq   ad t2 ->
                                  is_waiting ad <{call t1 t2            }>
  | isw_call2  : forall t1 t2,    value t1         ->
                                  is_waiting ad t2 ->
                                  is_waiting ad <{call t1 t2           }>
  | isw_init   : forall ad' t T,  is_waiting ad t  ->
                                  is_waiting ad <{init ad' t : T       }>
  | isw_load   : forall t,        is_waiting ad t  ->
                                  is_waiting ad <{*t                   }>
  | isw_asg1   : forall t1 t2,    is_waiting ad t1 ->
                                  no_reacq   ad t2 ->
                                  is_waiting ad <{t1 := t2             }>
  | isw_asg2   : forall t1 t2,    value t1         ->
                                  is_waiting ad t2 ->
                                  is_waiting ad <{t1 := t2             }>
  | isw_acq    : forall t1 x t2,  is_waiting ad t1 ->
                                  is_waiting ad <{acq t1 x t2          }>
  | isw_cr     : forall ad' t,    is_waiting ad t  ->
                                  is_waiting ad <{cr ad' t             }>
  | isw_wait   : forall t,        is_waiting ad t  ->
                                  is_waiting ad <{wait t               }>
  | isw_reacq  :                  is_waiting ad <{reacq ad             }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _isw tt :=
  match goal with
  | H : is_waiting _   <{unit                  }> |- _ => invc H
  | H : is_waiting _   <{nat _                 }> |- _ => invc H
  | H : is_waiting _   <{_ + _                 }> |- _ => tt H
  | H : is_waiting _   <{_ - _                 }> |- _ => tt H
  | H : is_waiting _   <{_; _                  }> |- _ => tt H
  | H : is_waiting _   <{if _ then _ else _ end}> |- _ => tt H
  | H : is_waiting _   <{while _ do _ end      }> |- _ => invc H
  | H : is_waiting _   <{var _                 }> |- _ => invc H
  | H : is_waiting _   <{fn _ _ _              }> |- _ => invc H
  | H : is_waiting _   <{call _ _              }> |- _ => tt H
  | H : is_waiting _   <{&_ : _                }> |- _ => invc H
  | H : is_waiting _   <{new _ : _             }> |- _ => invc H
  | H : is_waiting _   <{init _ _ : _          }> |- _ => tt H
  | H : is_waiting _   <{* _                   }> |- _ => tt H
  | H : is_waiting _   <{_ := _                }> |- _ => tt H
  | H : is_waiting _   <{acq _ _ _             }> |- _ => tt H
  | H : is_waiting _   <{cr _ _                }> |- _ => tt H
  | H : is_waiting _   <{wait _                }> |- _ => tt H
  | H : is_waiting ?ad <{reacq ?ad             }> |- _ => clear H
  | H : is_waiting _   <{reacq _               }> |- _ => tt H
  | H : is_waiting _   <{spawn _               }> |- _ => invc H
  end.

Ltac inv_isw  := _isw inv.
Ltac invc_isw := _isw invc.

(* preservation lemmas ----------------------------------------------------- *)

Lemma isw_subst : forall ad m x tx t,
  valid_term m t ->
  (* --- *)
  no_reacq   ad tx -> 
  is_waiting ad t  ->
  is_waiting ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_vtm; invc_isw;
  simpl; repeat destruct _str_eq_dec;
  auto using value_subst, noreacq_subst, is_waiting.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma _value_does_not_wait : forall ad t,
  value t ->
  is_waiting ad t ->
  False.
Proof.
  intros * Hval ?. invc Hval; invc_isw.
Qed.

Ltac value_does_not_wait :=
  match goal with _ : value ?t, _ : is_waiting _ ?t |- _ =>
    solve [exfalso; eauto using _value_does_not_wait]
  end.

Lemma isw_ad_bound : forall ad m t,
  valid_term m t ->
  (* --- *)
  is_waiting ad t ->
  ad < #m.
Proof.
  intros. induction t; invc_vtm; invc_isw; auto.
Qed.

Lemma noreacq_isw_contradiction : forall ad t,
  no_reacq  ad t ->
  is_waiting ad t ->
  False.
Proof.
  intros. induction t; invc_noreacq; invc_isw; auto.
Qed.

Corollary noreacqs_isw_contradiction : forall ad t,
  no_reacqs t ->
  is_waiting ad t ->
  False.
Proof.
  unfold no_reacqs. eauto using noreacq_isw_contradiction.
Qed.

Lemma noreacq_to_isw : forall t1 t2 ad,
  no_reacq ad t1 ->
  t1 --[e_wrel ad]--> t2 ->
  is_waiting ad t2.
Proof.
  intros. ind_tstep; invc_noreacq;
  auto using noreacq_subst, no_reacq, is_waiting.
Qed.

Lemma isw_to_noreacq : forall m t1 t2 ad,
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t1 ->
  t1 --[e_wacq ad]--> t2 ->
  no_reacq ad t2.
Proof.
  intros. ind_tstep; invc_vtm; invc_isw; try value_does_not_step;
  eauto using noreacq_from_value, no_reacq;
  exfalso; eauto using noreacq_wacq_contradiction.
Qed.

Lemma isw_to_isw_contradiction : forall t1 t2 ad,
  is_waiting ad t1 ->
  t1 --[e_wrel ad]--> t2 ->
  is_waiting ad t2 ->
  False.
Proof.
  intros. ind_tstep; repeat invc_isw; auto;
  try value_does_not_step; try value_does_not_wait;
  eauto using isw_subst, noreacq_to_isw, noreacq_isw_contradiction.
Qed.

Lemma isw_effect_contradiction : forall m t1 t2 ad e,
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t1 ->
  t1 --[e]--> t2   ->
  e <> e_wacq ad   ->
  False.
Proof.
  intros * ? ? ? Hneq. apply Hneq.
  ind_tstep; invc_vtm; repeat invc_isw; auto;
  value_does_not_step || value_does_not_wait.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_isw_preservation L :=
  intros; ind_tstep; try invc_vtm; repeat invc_isw;
  try value_does_not_step; try value_does_not_wait;
  eauto using L, isw_subst, is_waiting;
  exfalso; eauto using noreacqs_from_value, noreacqs_isw_contradiction.

Lemma isw_preservation_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t1 ->
  t1 --[e_none]--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_none. Qed.

Lemma isw_preservation_alloc : forall ad t1 t2 ad' T',
  is_waiting ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_alloc. Qed.

Lemma isw_preservation_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_init. Qed.

Lemma isw_preservation_read : forall ad t1 t2 ad' t',
  no_reacq ad t' ->
  (* --- *)
  is_waiting ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_read. Qed.

Lemma isw_preservation_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_write. Qed.

Lemma isw_preservation_acq : forall ad t1 t2 ad' t',
  no_reacq ad t' ->
  (* --- *)
  is_waiting ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_acq. Qed.

Lemma isw_preservation_rel : forall ad t1 t2 ad',
  is_waiting ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_rel. Qed.

Lemma isw_preservation_wacq : forall ad t1 t2 ad',
  ad <> ad' ->
  is_waiting ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_wacq. Qed.

Lemma isw_preservation_wrel : forall ad t1 t2 ad',
  is_waiting ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_wrel. Qed.

Lemma isw_preservation_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  is_waiting ad t2.
Proof. solve_isw_preservation noreacq_preservation_spawn. Qed.

(* inheritance ------------------------------------------------------------- *)

(*
Local Ltac solve_isw_inheritance L :=
  intros; ind_tstep; repeat invc_vtm; try invc_isw; auto;
  eauto using L, noreacq_from_value, is_waiting; exfalso;
  match goal with H : is_waiting ?ad ?t |- _ =>
    apply (noreacq_isw_contradiction ad t);
    eauto using noreacq_from_value, noreacq_subst, no_reacq
  end.

Lemma isw_inheritance_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t2 ->
  t1 --[e_none]--> t2 ->
  is_waiting ad t1.
Proof. solve_isw_inheritance noreacq_inheritance_none. Qed.

Lemma isw_inheritance_alloc : forall ad t1 t2 ad' T',
  is_waiting ad t2 ->
  t1 --[e_alloc ad' T']--> t2 ->
  is_waiting ad t1.
Proof. solve_isw_inheritance noreacq_inheritance_alloc. Qed.

Lemma isw_inheritance_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t2 ->
  t1 --[e_init ad' t']--> t2 ->
  is_waiting ad t1.
Proof. solve_isw_inheritance noreacq_inheritance_init. Qed.

Lemma isw_inheritance_read : forall ad t1 t2 ad' t',
  no_reacqs t' ->
  (* --- *)
  is_waiting ad t2 ->
  t1 --[e_read ad' t']--> t2 ->
  is_waiting ad t1.
Proof. solve_isw_inheritance noreacq_inheritance_read. Qed.

Lemma isw_inheritance_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t2 ->
  t1 --[e_write ad' t']--> t2 ->
  is_waiting ad t1.
Proof. solve_isw_inheritance noreacq_inheritance_write. Qed.

Lemma isw_inheritance_acq : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  no_reacqs t' ->
  (* --- *)
  ad <> ad' ->
  is_waiting ad t2 ->
  t1 --[e_acq ad' t']--> t2 ->
  is_waiting ad t1.
Proof. solve_isw_inheritance noreacq_inheritance_acq. Qed.

Lemma isw_inheritance_rel : forall ad t1 t2 ad',
  ad <> ad' ->
  is_waiting ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  is_waiting ad t1.
Proof. solve_isw_inheritance noreacq_inheritance_rel. Qed.

Lemma isw_inheritance_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  is_waiting ad t2 ->
  t1 --[e_spawn t']--> t2 ->
  is_waiting ad t1.
Proof. solve_isw_inheritance noreacq_inheritance_spawn. Qed.
*)

