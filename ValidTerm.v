From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import NoRef.
From Elo Require Import NoInit.
From Elo Require Import NoCR.

(* ------------------------------------------------------------------------- *)
(* valid-term                                                                *)
(* ------------------------------------------------------------------------- *)

(*
  Enforces that:
  - addresses are within the bounds of the memory.
  - static blocks do not contain <init>s and <cr>s.
*)
Inductive valid_term (m : mem) : tm -> Prop :=
  | vtm_unit  :                  valid_term m <{unit                     }> 
  | vtm_nat   : forall n,        valid_term m <{nat n                    }>
  | vtm_plus  : forall t1 t2,    valid_term m t1 ->
                                 valid_term m t2 ->
                                 valid_term m <{t1 + t2                  }> 
  | vtm_monus : forall t1 t2,    valid_term m t1 ->
                                 valid_term m t2 ->
                                 valid_term m <{t1 - t2                  }> 
  | vtm_seq   : forall t1 t2,    valid_term m t1 ->
                                 valid_term m t2 ->
                                 valid_term m <{t1; t2                   }> 
  | vtm_if    : forall t1 t2 t3, no_inits t2     ->
                                 no_crs   t2     ->
                                 no_inits t3     ->
                                 no_crs   t3     ->
                                 valid_term m t1 ->
                                 valid_term m t2 ->
                                 valid_term m t3 ->
                                 valid_term m <{if t1 then t2 else t3 end}> 
  | vtm_while  : forall t1 t2,   no_inits t1     ->
                                 no_crs   t1     ->
                                 no_inits t2     ->
                                 no_crs   t2     ->
                                 valid_term m t1 ->
                                 valid_term m t2 ->
                                 valid_term m <{while t1 do t2 end       }> 
  | vtm_var   : forall x,        valid_term m <{var x                    }>
  | vtm_fun   : forall x Tx t,   no_inits t      ->
                                 no_crs   t      ->
                                 valid_term m t  ->
                                 valid_term m <{fn x Tx t                }>
  | vtm_call  : forall t1 t2,    valid_term m t1 ->
                                 valid_term m t2 ->
                                 valid_term m <{call t1 t2               }> 
  | vtm_ref   : forall ad T,     ad < #m         ->
                                 valid_term m <{&ad : T                  }>
  | vtm_init  : forall ad t T,   ad < #m         ->
                                 valid_term m t  ->
                                 valid_term m <{init ad t :             T}> 
  | vtm_new   : forall T t,      no_inits t      ->
                                 no_crs   t      ->
                                 valid_term m t  ->
                                 valid_term m <{new t : T                }>
  | vtm_load  : forall t,        valid_term m t  ->
                                 valid_term m <{*t                       }> 
  | vtm_asg   : forall t1 t2,    valid_term m t1 ->
                                 valid_term m t2 ->
                                 valid_term m <{t1 := t2                 }> 
  | vtm_acq   : forall t1 x t2,  no_inits t2     ->
                                 no_crs   t2     ->
                                 valid_term m t1 ->
                                 valid_term m t2 ->
                                 valid_term m <{acq t1 x t2              }>
  | vtm_cr    : forall ad t,     ad < #m         ->
                                 valid_term m t  ->
                                 valid_term m <{cr ad t                  }>
  | vtm_spawn : forall t,        no_inits t      ->
                                 no_crs   t      ->
                                 valid_term m t  ->
                                 valid_term m <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vtm tt :=
  match goal with
  | H : valid_term _ <{unit                  }> |- _ => clear H
  | H : valid_term _ <{nat _                 }> |- _ => clear H
  | H : valid_term _ <{_ + _                 }> |- _ => tt H
  | H : valid_term _ <{_ - _                 }> |- _ => tt H
  | H : valid_term _ <{_; _                  }> |- _ => tt H
  | H : valid_term _ <{if _ then _ else _ end}> |- _ => tt H
  | H : valid_term _ <{while _ do _ end      }> |- _ => tt H
  | H : valid_term _ <{var _                 }> |- _ => clear H
  | H : valid_term _ <{fn _ _ _              }> |- _ => tt H
  | H : valid_term _ <{call _ _              }> |- _ => tt H
  | H : valid_term _ <{& _ : _               }> |- _ => tt H
  | H : valid_term _ <{new _ : _             }> |- _ => tt H
  | H : valid_term _ <{init _ _ : _          }> |- _ => tt H
  | H : valid_term _ <{* _                   }> |- _ => tt H
  | H : valid_term _ <{_ := _                }> |- _ => tt H
  | H : valid_term _ <{acq _ _ _             }> |- _ => tt H
  | H : valid_term _ <{cr _ _                }> |- _ => tt H
  | H : valid_term _ <{spawn _               }> |- _ => tt H
  end.

Ltac inv_vtm  := _vtm inv.
Ltac invc_vtm := _vtm invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma vtm_from_base : forall m t,
  no_refs  t ->
  no_inits t ->
  no_crs   t ->
  valid_term m t.
Proof.
  intros. induction t; invc_norefs; invc_noinits; invc_nocrs;
  eauto using valid_term.
Qed.

Lemma vtm_insert_term : forall m t1 t2 ad t T,
  valid_term m t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  valid_term m t.
Proof.
  intros. ind_tstep; invc_vtm; auto.
Qed.

Lemma vtm_write_term : forall m t1 t2 ad t,
  valid_term m t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_term m t.
Proof.
  intros. ind_tstep; invc_vtm; auto.
Qed.

Lemma vtm_insert_address : forall m t1 t2 ad t T,
  valid_term m t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  ad < #m.
Proof.
  intros. ind_tstep; invc_vtm; auto.
Qed.

Lemma vtm_write_address : forall m t1 t2 ad t,
  valid_term m t1 ->
  t1 --[e_write ad t]--> t2 ->
  ad < #m.
Proof.
  intros. ind_tstep; repeat invc_vtm; auto.
Qed.

(* lemmas about no-init and no-cr ------------------------------------------ *)

(* spawn ------------------------ *)

Lemma noinit_spawn_term : forall ad m t1 t2 tid t,
  valid_term m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_init ad t.
Proof.
  intros. ind_tstep; invc_vtm; auto.
Qed.

Lemma nocr_spawn_term : forall ad m t1 t2 tid t,
  valid_term m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_cr ad t.
Proof.
  intros. ind_tstep; invc_vtm; auto.
Qed.

Corollary noinits_spawn_term : forall m t1 t2 tid t,
  valid_term m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_inits t.
Proof.
  unfold no_inits. eauto using noinit_spawn_term.
Qed.

Corollary nocrs_spawn_term : forall m t1 t2 tid t,
  valid_term m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_crs t.
Proof.
  unfold no_crs. eauto using nocr_spawn_term.
Qed.

(* bounds ----------------------- *)

Lemma noinit_from_vtm1 : forall m t,
  valid_term m t ->
  no_init (#m) t.
Proof.
  intros. induction t; invc_vtm; auto using no_init.
Qed.

Lemma noinit_from_vtm2 : forall ad m t,
  valid_term m t ->
  #m < ad ->
  no_init ad t.
Proof.
  intros. induction t; invc_vtm; auto using no_init.
  match goal with |- no_init ?ad1 <{init ?ad2 _ : _}> => nat_eq_dec ad1 ad2 end;
  auto using no_init. lia.
Qed.

Lemma nocr_from_vtm1 : forall m t,
  valid_term m t ->
  no_cr (#m) t.
Proof.
  intros. induction t; invc_vtm; auto using no_cr.
Qed.

Lemma nocr_from_vtm2 : forall ad m t,
  valid_term m t ->
  #m < ad ->
  no_cr ad t.
Proof.
  intros. induction t; invc_vtm; auto using no_cr.
  match goal with |- no_cr ?ad1 <{cr ?ad2 _}> => nat_eq_dec ad1 ad2 end;
  auto using no_cr. lia.
Qed.

(* values ----------------------- *)

Lemma noinit_from_value : forall m ad t,
  valid_term m t ->
  (* --- *)
  value t ->
  no_init ad t.
Proof.
  intros * ? Hval. invc Hval; invc_vtm; auto using no_init.
Qed.

Lemma nocr_from_value : forall m ad t,
  valid_term m t ->
  (* --- *)
  value t ->
  no_cr ad t.
Proof.
  intros * ? Hval. invc Hval; invc_vtm; auto using no_cr.
Qed.

Corollary noinits_from_value : forall m t,
  valid_term m t ->
  (* --- *)
  value t ->
  no_inits t.
Proof.
  unfold no_inits. eauto using noinit_from_value.
Qed.

Corollary nocrs_from_value : forall m t,
  valid_term m t ->
  (* --- *)
  value t ->
  no_crs t.
Proof.
  unfold no_crs. eauto using nocr_from_value.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma vtm_subst : forall m t tx x,
  no_inits t  ->
  no_crs   t  ->
  value    tx ->
  (* --- *)
  valid_term m t ->
  valid_term m tx ->
  valid_term m <{[x := tx] t}>.
Proof.
  intros. induction t; invc_noinits; invc_nocrs; invc_vtm;
  simpl; try destruct _str_eq_dec; auto using valid_term;
  constructor;
  eauto using noinits_from_value, noinits_subst;
  eauto using nocrs_from_value, nocrs_subst.
Qed.

Lemma vtm_mem_add : forall m t c,
  valid_term m t ->
  valid_term (m +++ c) t.
Proof.
  intros. induction t; invc_vtm; constructor; sigma; auto.
Qed.

Lemma vtm_mem_set : forall m t ad' t',
  valid_term m t ->
  valid_term m[ad'.t <- t'] t.
Proof.
  intros. induction t; invc_vtm; constructor; sigma; auto.
Qed.

Lemma vtm_mem_acq : forall m t ad,
  valid_term m t ->
  valid_term m[ad.X <- true] t.
Proof.
  intros. induction t; invc_vtm; constructor; sigma; auto.
Qed.

Lemma vtm_mem_rel : forall m t ad,
  valid_term m t ->
  valid_term m[ad.X <- false] t.
Proof.
  intros. induction t; invc_vtm; constructor; sigma; auto.
Qed.

Lemma vtm_mem_region : forall m t ad R,
  valid_term m t ->
  valid_term m[ad.R <- R] t.
Proof.
  intros. induction t; invc_vtm; constructor; sigma; auto.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_vtm_preservation :=
  intros; ind_tstep; repeat invc_vtm; repeat constructor; sigma;
  auto using vtm_subst, vtm_mem_add, vtm_mem_set, vtm_mem_acq, vtm_mem_rel.

Lemma vtm_preservation_none : forall m t1 t2,
  valid_term m t1 ->
  t1 --[e_none]--> t2 ->
  valid_term m t2.
Proof. solve_vtm_preservation. Qed.

Lemma vtm_preservation_alloc : forall m t1 t2 T,
  valid_term m t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  valid_term (m +++ (None, T, false, R_invalid)) t2.
Proof. solve_vtm_preservation. Qed.

Lemma vtm_preservation_insert : forall m t1 t2 ad t T,
  valid_term m t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  valid_term (m[ad.t <- t]) t2.
Proof. solve_vtm_preservation. Qed.

Lemma vtm_preservation_read : forall m t1 t2 ad t,
  valid_term m t ->
  (* --- *)
  valid_term m t1 ->
  t1 --[e_read ad t]--> t2 ->
  valid_term m t2.
Proof. solve_vtm_preservation. Qed.

Lemma vtm_preservation_write : forall m t1 t2 ad t,
  valid_term m t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_term (m[ad.t <- t]) t2.
Proof. solve_vtm_preservation. Qed.

Lemma vtm_preservation_acq : forall m t1 t2 ad t,
  value t ->
  valid_term m t ->
  (* --- *)
  valid_term m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  valid_term m[ad.X <- true] t2.
Proof. solve_vtm_preservation. Qed.

Lemma vtm_preservation_rel : forall m t1 t2 ad,
  valid_term m t1 ->
  t1 --[e_rel ad]--> t2 ->
  valid_term m[ad.X <- false] t2.
Proof. solve_vtm_preservation. Qed.

Lemma vtm_preservation_spawn : forall m t1 t2 tid t,
  valid_term m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_term m t2.
Proof. solve_vtm_preservation. Qed.

Lemma vtm_preservation_spawned : forall m t1 t2 tid t,
  valid_term m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_term m t.
Proof. solve_vtm_preservation. Qed.

(* ------------------------------------------------------------------------- *)

Corollary vtm_preservation_memory : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 (valid_term m1) ->
  forall_memory  m1   (valid_term m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_memory  m2   (valid_term m2).
Proof.
  intros. invc_cstep; try invc_mstep; trivial; intros ? ? ?.
  - upsilon. eauto using vtm_mem_add.
  - upsilon; eauto using vtm_insert_term, vtm_mem_set.
  - upsilon; eauto using vtm_write_term, vtm_mem_set.
  - upsilon. eauto using vtm_mem_acq.
  - upsilon. eauto using vtm_mem_rel.
Qed.

Corollary vtm_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value ->
  (* --- *)
  forall_memory  m1   (valid_term m1) ->
  forall_threads ths1 (valid_term m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (valid_term m2).
Proof.
  intros. invc_cstep; try invc_mstep.
  - upsilon. eauto using vtm_preservation_none.
  - upsilon; eauto using vtm_mem_add, vtm_preservation_alloc.
  - upsilon; eauto using vtm_mem_set, vtm_preservation_insert.
  - upsilon. eauto using vtm_preservation_read.
  - upsilon; eauto using vtm_mem_set, vtm_preservation_write.
  - upsilon; eauto using vtm_mem_acq, vtm_preservation_acq.
  - upsilon; eauto using vtm_mem_rel, vtm_preservation_rel.
  - upsilon; eauto using vtm_preservation_spawn, vtm_preservation_spawned.
Qed.

Theorem vtm_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value ->
  (* --- *)
  forall_program m1 ths1 (valid_term m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (valid_term m2).
Proof.
  intros * ? [? ?] ?. split;
  eauto using vtm_preservation_memory, vtm_preservation_threads.
Qed.

Theorem vtm_preservation_rstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value ->
  (* --- *)
  forall_program m1 ths1 (valid_term m1) ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (valid_term m2).
Proof.
  intros. invc_rstep; eauto using vtm_preservation_cstep.
  match goal with _ : _ / _ ~~[_, _]~~> ?m / ?ths |- _ =>
    assert (forall_program m ths (valid_term m)) as [? ?]
      by eauto using vtm_preservation_cstep
  end.
  split; repeat intro; repeat omicron; upsilon; eauto using vtm_mem_region.
Qed.

Theorem vtm_preservation_base : forall t,
  no_refs  t ->
  no_inits t ->
  no_crs   t ->
  (* --- *)
  forall_program nil (base t) (valid_term nil).
Proof.
  auto using forallprogram_base, vtm_from_base, valid_term.
Qed.

