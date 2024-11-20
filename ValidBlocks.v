From Elo Require Import Core.

From Elo Require Import NoInit.
From Elo Require Import NoCR.

(* ------------------------------------------------------------------------- *)
(* valid-blocks                                                              *)
(* ------------------------------------------------------------------------- *)

Inductive valid_blocks : tm -> Prop :=
  | vb_unit  :                valid_blocks <{unit         }>
  | vb_nat   : forall n,      valid_blocks <{nat n        }>
  | vb_var   : forall x,      valid_blocks <{var x        }>
  | vb_fun   : forall x Tx t, no_inits t      ->
                              no_crs   t      ->
                              valid_blocks <{fn x Tx t    }>
  | vb_call  : forall t1 t2,  valid_blocks t1 ->
                              valid_blocks t2 ->
                              valid_blocks <{call t1 t2   }>
  | vb_ref   : forall ad T,   valid_blocks <{&ad : T      }>
  | vb_new   : forall T t,    valid_blocks t  ->
                              valid_blocks <{new t : T    }>
  | vb_init  : forall ad T t, valid_blocks t  ->
                              valid_blocks <{init ad t : T}>
  | vb_load  : forall t,      valid_blocks t  ->
                              valid_blocks <{*t           }>
  | vb_asg   : forall t1 t2,  valid_blocks t1 ->
                              valid_blocks t2 ->
                              valid_blocks <{t1 := t2     }>
  | vb_acq   : forall t1 t2,  valid_blocks t1 ->
                              valid_blocks t2 ->
                              valid_blocks <{acq t1 t2    }>
  | vb_cr    : forall ad t,   valid_blocks t  ->
                              valid_blocks <{cr ad t      }>
  | vb_spawn : forall t,      no_inits t      ->
                              no_crs   t      ->
                              valid_blocks <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vb tt :=
  match goal with
  | H : valid_blocks <{unit          }> |- _ => clear H
  | H : valid_blocks <{nat _         }> |- _ => clear H
  | H : valid_blocks <{var _         }> |- _ => clear H
  | H : valid_blocks <{fn _ _ _      }> |- _ => tt H
  | H : valid_blocks <{call _ _      }> |- _ => tt H
  | H : valid_blocks <{&_ : _        }> |- _ => clear H
  | H : valid_blocks <{new _ : _     }> |- _ => tt H
  | H : valid_blocks <{init _ _ : _  }> |- _ => tt H
  | H : valid_blocks <{* _           }> |- _ => tt H
  | H : valid_blocks <{_ := _        }> |- _ => tt H
  | H : valid_blocks <{acq _ _       }> |- _ => tt H
  | H : valid_blocks <{cr _ _        }> |- _ => tt H
  | H : valid_blocks <{spawn _       }> |- _ => tt H
  end.

Ltac inv_vb  := _vb inv.
Ltac invc_vb := _vb invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma vb_from_noinits_nocrs : forall t,
  no_inits t ->
  no_crs   t ->
  valid_blocks t.
Proof.
  intros. induction t; invc_noinits; invc_nocrs; eauto using valid_blocks.
Qed.

Lemma vb_insert_term : forall t1 t2 ad t,
  valid_blocks t1 ->
  t1 --[e_insert ad t]--> t2 ->
  valid_blocks t.
Proof.
  intros. ind_tstep; invc_vb; eauto using valid_blocks.
Qed.

Lemma vb_write_term : forall t1 t2 ad t,
  valid_blocks t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_blocks t.
Proof.
  intros. ind_tstep; invc_vb; eauto using valid_blocks.
Qed.

Lemma noinit_spawn_term : forall ad t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_init ad t.
Proof.
  intros. ind_tstep; invc_vb; auto.
Qed.

Corollary noinits_spawn_term : forall t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_inits t.
Proof.
  unfold no_inits. eauto using noinit_spawn_term.
Qed.

Lemma nocr_spawn_term : forall ad t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_cr ad t.
Proof.
  intros. ind_tstep; invc_vb; auto.
Qed.

Corollary nocrs_spawn_term : forall t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_crs t.
Proof.
  unfold no_crs. eauto using nocr_spawn_term.
Qed.

Lemma noinit_from_value : forall ad t,
  valid_blocks t ->
  (* --- *)
  value t ->
  no_init ad t.
Proof.
  intros * ? Hval. invc Hval; invc_vb; eauto using no_init.
Qed.

Lemma nocr_from_value : forall ad t,
  valid_blocks t ->
  (* --- *)
  value t ->
  no_cr ad t.
Proof.
  intros * ? Hval. invc Hval; invc_vb; eauto using no_cr.
Qed.

Corollary noinits_from_value : forall t,
  valid_blocks t ->
  (* --- *)
  value t ->
  no_inits t.
Proof.
  unfold no_inits. auto using noinit_from_value.
Qed.

Corollary nocrs_from_value : forall t,
  valid_blocks t ->
  (* --- *)
  value t ->
  no_crs t.
Proof.
  unfold no_crs. auto using nocr_from_value.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma vb_subst : forall x tx t,
  no_inits t ->
  no_crs   t ->
  value tx ->
  valid_blocks tx ->
  valid_blocks <{[x := tx] t}>.
Proof.
  intros. induction t; invc_noinits; invc_nocrs;
  simpl; try destruct str_eq_dec; subst; eauto using valid_blocks;
  constructor;
  eauto using noinits_from_value, noinits_subst;
  eauto using nocrs_from_value, nocrs_subst.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_vb_preservation :=
  intros; ind_tstep; repeat invc_vb;
  eauto using vb_from_noinits_nocrs, vb_subst, valid_blocks.

Lemma vb_preservation_none : forall t1 t2,
  valid_blocks t1 ->
  t1 --[e_none]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_alloc : forall t1 t2 ad T,
  valid_blocks t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_insert : forall t1 t2 ad t,
  valid_blocks t1 ->
  t1 --[e_insert ad t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_read : forall t1 t2 ad t,
  valid_blocks t ->
  (* --- *)
  valid_blocks t1 ->
  t1 --[e_read ad t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_write : forall t1 t2 ad t,
  valid_blocks t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_acq : forall t1 t2 ad t,
  value t ->
  valid_blocks t ->
  (* --- *)
  valid_blocks t1 ->
  t1 --[e_acq ad t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_rel : forall t1 t2 ad,
  valid_blocks t1 ->
  t1 --[e_rel ad]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_spawn : forall t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_spawned : forall t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_blocks t.
Proof. solve_vb_preservation. Qed.

Theorem vb_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  (* --- *)
  forall_program m1 ths1 valid_blocks ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 valid_blocks.
Proof.
  intros * ? Hvb ?.
  assert (Hvb' := Hvb). destruct Hvb as [? ?].
  invc_cstep; try invc_mstep; upsilon.
  - eauto using vb_preservation_none.
  - eauto using vb_preservation_alloc.
  - eauto using vb_insert_term, vb_preservation_insert.
  - eauto using vb_preservation_read.
  - eauto using vb_write_term, vb_preservation_write.
  - eauto using vb_preservation_acq.
  - eauto using vb_preservation_rel.
  - eauto using vb_preservation_spawn, vb_preservation_spawned.
Qed.

