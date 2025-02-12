From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import ValidTerm.
From Elo Require Import InheritanceNoCR.

(* ------------------------------------------------------------------------- *)
(* one-cr                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive one_cr (ad : addr) : tm -> Prop :=
  | onecr_plus1  : forall t1 t2,    one_cr ad t1 ->
                                    no_cr  ad t2 ->
                                    one_cr ad <{t1 + t2                  }>
  | onecr_plus2  : forall t1 t2,    no_cr  ad t1 ->
                                    one_cr ad t2 ->
                                    one_cr ad <{t1 + t2                  }>
  | onecr_monus1 : forall t1 t2,    one_cr ad t1 ->
                                    no_cr  ad t2 ->
                                    one_cr ad <{t1 - t2                  }>
  | onecr_monus2 : forall t1 t2,    no_cr  ad t1 ->
                                    one_cr ad t2 ->
                                    one_cr ad <{t1 - t2                  }>
  | onecr_seq1   : forall t1 t2,    one_cr ad t1 ->
                                    one_cr ad <{t1; t2                   }>
  | onecr_if     : forall t1 t2 t3, one_cr ad t1 ->
                                    one_cr ad <{if t1 then t2 else t3 end}>
  | onecr_call1  : forall t1 t2,    one_cr ad t1 ->
                                    no_cr  ad t2 ->
                                    one_cr ad <{call t1 t2               }>
  | onecr_call2  : forall t1 t2,    no_cr  ad t1 ->
                                    one_cr ad t2 ->
                                    one_cr ad <{call t1 t2               }>
  | onecr_init   : forall ad' t T,  one_cr ad t  ->
                                    one_cr ad <{init ad' t : T           }>
  | onecr_load   : forall t,        one_cr ad t  ->
                                    one_cr ad <{*t                       }>
  | onecr_asg1   : forall t1 t2,    one_cr ad t1 ->
                                    no_cr  ad t2 ->
                                    one_cr ad <{t1 := t2                 }>
  | onecr_asg2   : forall t1 t2,    no_cr  ad t1 ->
                                    one_cr ad t2 ->
                                    one_cr ad <{t1 := t2                 }>
  | onecr_acq    : forall t1 x t2,  one_cr ad t1 ->
                                    one_cr ad <{acq t1 x t2              }>
  | onecr_crA    : forall t,        no_cr  ad t  ->
                                    one_cr ad <{cr ad t                  }>
  | onecr_crB    : forall ad' t,    ad <> ad'    ->
                                    one_cr ad t  ->
                                    one_cr ad <{cr ad' t                 }>
  | onecr_wait   : forall t,        one_cr ad t  ->
                                    one_cr ad <{wait t                   }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _onecr tt :=
  match goal with
  | H : one_cr _ <{unit                  }> |- _ => invc H
  | H : one_cr _ <{nat _                 }> |- _ => invc H
  | H : one_cr _ <{_ + _                 }> |- _ => tt H
  | H : one_cr _ <{_ - _                 }> |- _ => tt H
  | H : one_cr _ <{_; _                  }> |- _ => tt H
  | H : one_cr _ <{if _ then _ else _ end}> |- _ => tt H
  | H : one_cr _ <{while _ do _ end      }> |- _ => invc H
  | H : one_cr _ <{var _                 }> |- _ => invc H
  | H : one_cr _ <{fn _ _ _              }> |- _ => invc H
  | H : one_cr _ <{call _ _              }> |- _ => tt H
  | H : one_cr _ <{&_ : _                }> |- _ => invc H
  | H : one_cr _ <{new _ : _             }> |- _ => invc H
  | H : one_cr _ <{init _ _ : _          }> |- _ => tt H
  | H : one_cr _ <{* _                   }> |- _ => tt H
  | H : one_cr _ <{_ := _                }> |- _ => tt H
  | H : one_cr _ <{acq _ _ _             }> |- _ => tt H
  | H : one_cr _ <{cr _ _                }> |- _ => tt H
  | H : one_cr _ <{wait _                }> |- _ => tt H
  | H : one_cr _ <{reacq _               }> |- _ => invc H
  | H : one_cr _ <{spawn _               }> |- _ => invc H
  end.

Ltac inv_onecr  := _onecr inv.
Ltac invc_onecr := _onecr invc.

(* preservation lemmas ----------------------------------------------------- *)

Lemma onecr_subst : forall ad x tx t,
  no_cr  ad tx -> 
  one_cr ad t  ->
  one_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_onecr;
  simpl; repeat destruct _str_eq_dec;
  auto using nocr_subst, one_cr.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma onecr_ad_bound : forall ad m t,
  valid_term m t ->
  (* --- *)
  one_cr ad t ->
  ad < #m.
Proof.
  intros. induction t; invc_vtm; invc_onecr; auto.
Qed.

Lemma nocr_onecr_contradiction : forall ad t,
  no_cr  ad t ->
  one_cr ad t ->
  False.
Proof.
  intros. induction t; invc_nocr; invc_onecr; auto.
Qed.

Corollary nocrs_onecr_contradiction : forall ad t,
  no_crs t ->
  one_cr ad t ->
  False.
Proof.
  unfold no_crs. eauto using nocr_onecr_contradiction.
Qed.

Lemma nocr_to_onecr : forall t1 t2 ad t,
  no_crs t ->
  (* --- *)
  no_cr ad t1 ->
  t1 --[e_acq ad t]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_nocr; auto using nocr_subst, no_cr, one_cr.
Qed.

Lemma onecr_to_nocr : forall m t1 t2 ad,
  valid_term m t1 ->
  (* --- *)
  one_cr ad t1          ->
  t1 --[e_rel ad]--> t2 ->
  no_cr ad t2.
Proof.
  intros. ind_tstep; invc_vtm; invc_onecr; auto using no_cr;
  exfalso; eauto using nocr_rel_contradiction.
Qed.

Lemma onecr_to_onecr_contradiction : forall t1 t2 ad' t',
  no_crs t' ->
  (* --- *)
  one_cr ad' t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  one_cr ad' t2 ->
  False.
Proof.
  intros. ind_tstep; repeat invc_onecr;
  eauto using onecr_subst, nocr_to_onecr, nocr_onecr_contradiction.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_onecr_preservation L :=
  intros; ind_tstep; try invc_vtm; repeat invc_onecr;
  eauto using L, onecr_subst, one_cr;
  exfalso; eauto using nocr_from_value, nocr_onecr_contradiction.

Lemma onecr_preservation_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_none. Qed.

Lemma onecr_preservation_alloc : forall ad t1 t2 ad' T',
  one_cr ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_alloc. Qed.

Lemma onecr_preservation_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_init. Qed.

Lemma onecr_preservation_read : forall ad t1 t2 ad' t',
  no_cr ad t' ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_read. Qed.

Lemma onecr_preservation_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_write. Qed.

Lemma onecr_preservation_acq : forall ad t1 t2 ad' t',
  no_cr ad t' ->
  (* --- *)
  ad <> ad' ->
  one_cr ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_acq. Qed.

Lemma onecr_preservation_rel : forall ad t1 t2 ad',
  ad <> ad' ->
  one_cr ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_rel. Qed.

Lemma onecr_preservation_wacq : forall ad t1 t2 ad',
  one_cr ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_wacq. Qed.

Lemma onecr_preservation_wrel : forall ad t1 t2 ad',
  one_cr ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_wrel. Qed.

Lemma onecr_preservation_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_spawn. Qed.

(* inheritance ------------------------------------------------------------- *)

Local Ltac solve_onecr_inheritance L :=
  intros; ind_tstep; repeat invc_vtm; try invc_onecr; auto;
  eauto using L, nocr_from_value, one_cr; exfalso;
  match goal with H : one_cr ?ad ?t |- _ =>
    apply (nocr_onecr_contradiction ad t);
    eauto using nocr_from_value, nocr_subst, no_cr
  end.

Lemma onecr_inheritance_none : forall ad m t1 t2,
  valid_term m t1 ->
  (* --- *)
  one_cr ad t2 ->
  t1 --[e_none]--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_none. Qed.

Lemma onecr_inheritance_alloc : forall ad m t1 t2 ad' T',
  valid_term m t1 ->
  (* --- *)
  one_cr ad t2 ->
  t1 --[e_alloc ad' T']--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_alloc. Qed.

Lemma onecr_inheritance_init : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  one_cr ad t2 ->
  t1 --[e_init ad' t']--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_init. Qed.

Lemma onecr_inheritance_read : forall ad t1 t2 ad' t',
  no_cr ad t' ->
  (* --- *)
  one_cr ad t2 ->
  t1 --[e_read ad' t']--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_read. Qed.

Lemma onecr_inheritance_write : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  (* --- *)
  one_cr ad t2 ->
  t1 --[e_write ad' t']--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_write. Qed.

Lemma onecr_inheritance_acq : forall ad m t1 t2 ad' t',
  valid_term m t1 ->
  no_cr ad t'     ->
  (* --- *)
  ad <> ad' ->
  one_cr ad t2 ->
  t1 --[e_acq ad' t']--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_acq. Qed.

Lemma onecr_inheritance_rel : forall ad t1 t2 ad',
  ad <> ad' ->
  one_cr ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_rel. Qed.

Lemma onecr_inheritance_wacq : forall ad t1 t2 ad',
  one_cr ad t2 ->
  t1 --[e_wacq ad']--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_wacq. Qed.

Lemma onecr_inheritance_wrel : forall ad t1 t2 ad',
  one_cr ad t2 ->
  t1 --[e_wrel ad']--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_wrel. Qed.

Lemma onecr_inheritance_spawn : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  one_cr ad t2 ->
  t1 --[e_spawn t']--> t2 ->
  one_cr ad t1.
Proof. solve_onecr_inheritance nocr_inheritance_spawn. Qed.

Lemma onecr_inheritance_spawned : forall ad m t1 t2 t',
  valid_term m t1 ->
  (* --- *)
  one_cr ad t'            ->
  t1 --[e_spawn t']--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_vtm; auto. eauto using nocrs_onecr_contradiction. 
Qed.

