From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import NoReacq.
From Elo Require Import ValidTerm.
From Elo Require Import OneCR.

(* ------------------------------------------------------------------------- *)
(* waiting                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive waiting (ad : addr) : tm -> Prop :=
  | wg_plus1  : forall t1 t2,    waiting  ad t1 ->
                                 no_reacq ad t2 ->
                                 waiting ad <{t1 + t2               }>
  | wg_plus2  : forall t1 t2,    value t1       ->
                                 waiting  ad t2 ->
                                 waiting  ad <{t1 + t2              }>
  | wg_monus1 : forall t1 t2,    waiting  ad t1 ->
                                 no_reacq ad t2 ->
                                 waiting  ad <{t1 - t2              }>
  | wg_monus2 : forall t1 t2,    value t1       ->
                                 waiting  ad t2 ->
                                 waiting  ad <{t1 - t2              }>
  | wg_seq    : forall t1 t2,    waiting  ad t1 ->
                                 waiting  ad <{t1; t2               }>
  | wg_if     : forall t1 t2 t3, waiting  ad t1 ->
                                 waiting  ad (tm_if t1 t2 t3) 
  | wg_call1  : forall t1 t2,    waiting  ad t1 ->
                                 no_reacq ad t2 ->
                                 waiting  ad <{call t1 t2           }>
  | wg_call2  : forall t1 t2,    value t1       ->
                                 waiting  ad t2 ->
                                 waiting  ad <{call t1 t2           }>
  | wg_init   : forall ad' t T,  waiting  ad t  ->
                                 waiting  ad <{init ad' t : T       }>
  | wg_load   : forall t,        waiting  ad t  ->
                                 waiting  ad <{*t                   }>
  | wg_asg1   : forall t1 t2,    waiting  ad t1 ->
                                 no_reacq ad t2 ->
                                 waiting  ad <{t1 := t2             }>
  | wg_asg2   : forall t1 t2,    value t1       ->
                                 waiting  ad t2 ->
                                 waiting  ad <{t1 := t2             }>
  | wg_acq    : forall t1 x t2,  waiting  ad t1 ->
                                 waiting  ad <{acq t1 x t2          }>
  | wg_cr     : forall ad' t,    waiting  ad t  ->
                                 waiting  ad <{cr ad' t             }>
  | wg_wait   : forall t,        waiting  ad t  ->
                                 waiting  ad <{wait t               }>
  | wg_reacq  :                  waiting  ad <{reacq ad             }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _wg tt :=
  match goal with
  | H : waiting _   <{unit                  }> |- _ => invc H
  | H : waiting _   <{nat _                 }> |- _ => invc H
  | H : waiting _   <{_ + _                 }> |- _ => tt H
  | H : waiting _   <{_ - _                 }> |- _ => tt H
  | H : waiting _   <{_; _                  }> |- _ => tt H
  | H : waiting _   <{if _ then _ else _ end}> |- _ => tt H
  | H : waiting _   <{while _ do _ end      }> |- _ => invc H
  | H : waiting _   <{var _                 }> |- _ => invc H
  | H : waiting _   <{fn _ _ _              }> |- _ => invc H
  | H : waiting _   <{call _ _              }> |- _ => tt H
  | H : waiting _   <{&_ : _                }> |- _ => invc H
  | H : waiting _   <{new _ : _             }> |- _ => invc H
  | H : waiting _   <{init _ _ : _          }> |- _ => tt H
  | H : waiting _   <{* _                   }> |- _ => tt H
  | H : waiting _   <{_ := _                }> |- _ => tt H
  | H : waiting _   <{acq _ _ _             }> |- _ => tt H
  | H : waiting _   <{cr _ _                }> |- _ => tt H
  | H : waiting _   <{wait _                }> |- _ => tt H
  | H : waiting ?ad <{reacq ?ad             }> |- _ => clear H
  | H : waiting _   <{reacq _               }> |- _ => tt H
  | H : waiting _   <{spawn _               }> |- _ => invc H
  end.

Ltac inv_wg  := _wg inv.
Ltac invc_wg := _wg invc.

(* preservation lemmas ----------------------------------------------------- *)

Lemma wg_subst : forall ad m x tx t,
  valid_term m t ->
  (* --- *)
  no_reacq   ad tx -> 
  waiting ad t  ->
  waiting ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_vtm; invc_wg;
  simpl; repeat destruct _str_eq_dec;
  auto using value_subst, noreacq_subst, waiting.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma _value_does_not_wait : forall ad t,
  value t ->
  waiting ad t ->
  False.
Proof.
  intros * Hval ?. invc Hval; invc_wg.
Qed.

Ltac value_does_not_wait :=
  match goal with _ : value ?t, _ : waiting _ ?t |- _ =>
    solve [exfalso; eauto using _value_does_not_wait]
  end.

Lemma wg_ad_bound : forall ad m t,
  valid_term m t ->
  (* --- *)
  waiting ad t ->
  ad < #m.
Proof.
  intros. induction t; invc_vtm; invc_wg; auto.
Qed.

Lemma noreacq_wg_contradiction : forall ad t,
  no_reacq ad t ->
  waiting  ad t ->
  False.
Proof.
  intros. induction t; invc_noreacq; invc_wg; auto.
Qed.

Corollary noreacqs_wg_contradiction : forall ad t,
  no_reacqs t ->
  waiting ad t ->
  False.
Proof.
  unfold no_reacqs. eauto using noreacq_wg_contradiction.
Qed.

Lemma noreacq_to_wg : forall t1 t2 ad,
  no_reacq ad t1 ->
  t1 --[e_wrel ad]--> t2 ->
  waiting ad t2.
Proof.
  intros. ind_tstep; invc_noreacq;
  auto using noreacq_subst, no_reacq, waiting.
Qed.

Lemma wg_to_noreacq : forall m t1 t2 ad,
  valid_term m t1 ->
  (* --- *)
  waiting ad t1 ->
  t1 --[e_wacq ad]--> t2 ->
  no_reacq ad t2.
Proof.
  intros. ind_tstep; invc_vtm; invc_wg; try value_does_not_step;
  eauto using noreacq_from_value, no_reacq;
  exfalso; eauto using noreacq_wacq_contradiction.
Qed.

Lemma wg_to_wg_contradiction : forall t1 t2 ad,
  waiting ad t1 ->
  t1 --[e_wrel ad]--> t2 ->
  waiting ad t2 ->
  False.
Proof.
  intros. ind_tstep; repeat invc_wg; auto;
  try value_does_not_step; try value_does_not_wait;
  eauto using wg_subst, noreacq_to_wg, noreacq_wg_contradiction.
Qed.

Lemma wg_effect_contradiction : forall m t1 t2 ad e,
  valid_term m t1 ->
  (* --- *)
  waiting ad t1 ->
  t1 --[e]--> t2   ->
  e <> e_wacq ad   ->
  False.
Proof.
  intros * ? ? ? Hneq. apply Hneq.
  ind_tstep; invc_vtm; repeat invc_wg; auto;
  value_does_not_step || value_does_not_wait.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_wg_preservation L :=
  intros; ind_tstep; try invc_vtm; repeat invc_wg;
  try value_does_not_step; try value_does_not_wait;
  eauto using L, wg_subst, waiting;
  exfalso; eauto using noreacqs_from_value, noreacqs_wg_contradiction.

Lemma wg_preservation_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  waiting ad t1 ->
  t1 --[e_none]--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_none. Qed.

Lemma wg_preservation_alloc : forall ad t1 t2 ad' T',
  waiting ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_alloc. Qed.

Lemma wg_preservation_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  waiting ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_init. Qed.

Lemma wg_preservation_read : forall ad t1 t2 ad' t',
  no_reacq ad t' ->
  (* --- *)
  waiting ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_read. Qed.

Lemma wg_preservation_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  waiting ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_write. Qed.

Lemma wg_preservation_acq : forall ad t1 t2 ad' t',
  no_reacq ad t' ->
  (* --- *)
  waiting ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_acq. Qed.

Lemma wg_preservation_rel : forall ad t1 t2 ad',
  waiting ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_rel. Qed.

Lemma wg_preservation_wacq : forall ad t1 t2 ad',
  ad <> ad' ->
  waiting ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_wacq. Qed.

Lemma wg_preservation_wrel : forall ad t1 t2 ad',
  waiting ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_wrel. Qed.

Lemma wg_preservation_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  waiting ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  waiting ad t2.
Proof. solve_wg_preservation noreacq_preservation_spawn. Qed.

(* inheritance ------------------------------------------------------------- *)

(*
Local Ltac solve_wg_inheritance L :=
  intros; ind_tstep; repeat invc_vtm; try invc_wg; auto;
  eauto using L, noreacq_from_value, waiting; exfalso;
  match goal with H : waiting ?ad ?t |- _ =>
    apply (noreacq_wg_contradiction ad t);
    eauto using noreacq_from_value, noreacq_subst, no_reacq
  end.

Lemma wg_inheritance_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  waiting ad t2 ->
  t1 --[e_none]--> t2 ->
  waiting ad t1.
Proof. solve_wg_inheritance noreacq_inheritance_none. Qed.

Lemma wg_inheritance_alloc : forall ad t1 t2 ad' T',
  waiting ad t2 ->
  t1 --[e_alloc ad' T']--> t2 ->
  waiting ad t1.
Proof. solve_wg_inheritance noreacq_inheritance_alloc. Qed.

Lemma wg_inheritance_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  waiting ad t2 ->
  t1 --[e_init ad' t']--> t2 ->
  waiting ad t1.
Proof. solve_wg_inheritance noreacq_inheritance_init. Qed.

Lemma wg_inheritance_read : forall ad t1 t2 ad' t',
  no_reacqs t' ->
  (* --- *)
  waiting ad t2 ->
  t1 --[e_read ad' t']--> t2 ->
  waiting ad t1.
Proof. solve_wg_inheritance noreacq_inheritance_read. Qed.

Lemma wg_inheritance_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  waiting ad t2 ->
  t1 --[e_write ad' t']--> t2 ->
  waiting ad t1.
Proof. solve_wg_inheritance noreacq_inheritance_write. Qed.

Lemma wg_inheritance_acq : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  no_reacqs t' ->
  (* --- *)
  ad <> ad' ->
  waiting ad t2 ->
  t1 --[e_acq ad' t']--> t2 ->
  waiting ad t1.
Proof. solve_wg_inheritance noreacq_inheritance_acq. Qed.

Lemma wg_inheritance_rel : forall ad t1 t2 ad',
  ad <> ad' ->
  waiting ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  waiting ad t1.
Proof. solve_wg_inheritance noreacq_inheritance_rel. Qed.

Lemma wg_inheritance_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  waiting ad t2 ->
  t1 --[e_spawn t']--> t2 ->
  waiting ad t1.
Proof. solve_wg_inheritance noreacq_inheritance_spawn. Qed.
*)

