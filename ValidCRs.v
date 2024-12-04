From Elo Require Import Core.

From Elo Require Import WellTypedTerm.
From Elo Require Import NoWRef.

(* ------------------------------------------------------------------------- *)
(* valid-crs                                                                 *)
(* ------------------------------------------------------------------------- *)

Inductive valid_crs : tm -> Prop :=
  | vcr_unit  :                valid_crs <{unit         }>
  | vcr_nat   : forall n,      valid_crs <{nat n        }>
  | vcr_var   : forall x,      valid_crs <{var x        }>
  | vcr_fun   : forall x Tx t, valid_crs t  ->
                               valid_crs <{fn x Tx t    }>
  | vcr_call  : forall t1 t2,  valid_crs t1 ->
                               valid_crs t2 ->
                               valid_crs <{call t1 t2   }>
  | vcr_ref   : forall ad T,   valid_crs <{&ad : T      }>
  | vcr_new   : forall T t,    valid_crs t  ->
                               valid_crs <{new t : T    }>
  | vcr_init  : forall ad T t, valid_crs t  ->
                               valid_crs <{init ad t : T}>
  | vcr_load  : forall t,      valid_crs t  ->
                               valid_crs <{*t           }>
  | vcr_asg   : forall t1 t2,  valid_crs t1 ->
                               valid_crs t2 ->
                               valid_crs <{t1 := t2     }>
  | vcr_acq   : forall t1 t2,  valid_crs t1 ->
                               valid_crs t2 ->
                               valid_crs <{acq t1 t2    }>
  | vcr_cr1   : forall ad t,   value    t   ->
                               no_wrefs t   ->
                               valid_crs <{cr ad t      }>
  | vcr_cr2   : forall ad t,   ~ value t    ->
                               valid_crs t  ->
                               valid_crs <{cr ad t      }>
  | vcr_spawn : forall t,      valid_crs t  ->
                               valid_crs <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vcr tt :=
  match goal with
  | H : valid_crs <{unit          }> |- _ => clear H
  | H : valid_crs <{nat _         }> |- _ => clear H
  | H : valid_crs <{var _         }> |- _ => clear H
  | H : valid_crs <{fn _ _ _      }> |- _ => tt H
  | H : valid_crs <{call _ _      }> |- _ => tt H
  | H : valid_crs <{&_ : _        }> |- _ => clear H
  | H : valid_crs <{new _ : _     }> |- _ => tt H
  | H : valid_crs <{init _ _ : _  }> |- _ => tt H
  | H : valid_crs <{* _           }> |- _ => tt H
  | H : valid_crs <{_ := _        }> |- _ => tt H
  | H : valid_crs <{acq _ _       }> |- _ => tt H
  | H : valid_crs <{cr _ _        }> |- _ => tt H
  | H : valid_crs <{spawn _       }> |- _ => tt H
  end.

Ltac inv_vcr  := _vcr inv.
Ltac invc_vcr := _vcr invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma vcr_from_nowrefs : forall t,
  no_wrefs t ->
  valid_crs t.
Proof.
  intros. induction t; invc_nowrefs; auto using valid_crs.
  destruct (value_dec t); auto using valid_crs.
Qed.

Lemma vcr_insert_term : forall t1 t2 ad t,
  valid_crs t1 ->
  t1 --[e_insert ad t]--> t2 ->
  valid_crs t.
Proof.
  intros. ind_tstep; invc_vcr; auto using vcr_from_nowrefs, valid_crs.
Qed.

Lemma vcr_write_term : forall t1 t2 ad t,
  valid_crs t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_crs t.
Proof.
  intros. ind_tstep; invc_vcr; auto using vcr_from_nowrefs, valid_crs.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Local Lemma vcr_subst : forall x tx t,
  value tx ->
  valid_crs t ->
  valid_crs tx ->
  valid_crs <{[x := tx] t}>.
Proof.
  intros. induction t; simpl; try destruct str_eq_dec;
  invc_vcr; eauto using valid_crs.
  - assert (valid_crs t) by eauto using vcr_from_nowrefs.
    aspecialize.
    eapply vcr_cr1; eauto using value_subst.
    admit.
  - eapply vcr_cr2; eauto. intros ?. admit.
Abort.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_vcr_preservation :=
  intros; ind_tstep; repeat invc_vcr; eauto using vcr_from_nowrefs, valid_crs.

Lemma vcr_preservation_none : forall t1 t2,
  well_typed_term t2 ->
  (* --- *)
  valid_crs t1 ->
  t1 --[e_none]--> t2 ->
  valid_crs t2.
Proof.
  intros * [T ?] **. gendep T. ind_tstep; intros;
  repeat invc_typeof; repeat invc_vcr; eauto using valid_crs;
  try value_does_not_step.
  - admit.
  - destruct (value_dec t'); eauto using nowrefs_from_type, valid_crs.
Qed.

(*
Lemma vcr_preservation_alloc : forall t1 t2 ad T,
  valid_crs t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  valid_crs t2.
Proof. solve_vcr_preservation. Qed.

Lemma vcr_preservation_insert : forall t1 t2 ad t,
  valid_crs t1 ->
  t1 --[e_insert ad t]--> t2 ->
  valid_crs t2.
Proof. solve_vcr_preservation. Qed.

Lemma vcr_preservation_read : forall t1 t2 ad t,
  valid_crs t ->
  (* --- *)
  valid_crs t1 ->
  t1 --[e_read ad t]--> t2 ->
  valid_crs t2.
Proof. solve_vcr_preservation. Qed.

Lemma vcr_preservation_write : forall t1 t2 ad t,
  valid_crs t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_crs t2.
Proof. solve_vcr_preservation. Qed.

Lemma vcr_preservation_acq : forall m t1 t2 ad' t',
  forall_memory m value ->
  forall_memory m valid_crs ->
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  m[ad'].t = Some t' ->
  valid_crs t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  valid_crs t2.
Proof.
  intros * ? ? [T ?] **. gendep T; ind_tstep; intros;
  repeat invc_typeof; repeat invc_cr; repeat invc_vcr;
  eauto using vcr_subst, valid_crs.
  invc_eq. rewrite <- empty_eq_safe_empty in *. 
  eauto using vcr_subst, valid_crs.
Qed.

Lemma vcr_preservation_rel : forall t1 t2 ad,
  valid_crs t1 ->
  t1 --[e_rel ad]--> t2 ->
  valid_crs t2.
Proof. solve_vcr_preservation. Qed.

Lemma vcr_preservation_spawn : forall t1 t2 tid t,
  valid_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_crs t2.
Proof. solve_vcr_preservation. Qed.

Lemma vcr_preservation_spawned : forall t1 t2 tid t,
  valid_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_crs t.
Proof. solve_vcr_preservation. Qed.

Theorem vcr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistent_references m1) ->
  (* --- *)
  forall_program m1 ths1 valid_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 valid_crs.
Proof.
  intros until 3. intros Hvb ?.
  assert (Hvb' := Hvb). destruct Hvb as [? ?].
  invc_cstep; try invc_mstep; upsilon.
  - eauto using vcr_preservation_none.
  - eauto using vcr_preservation_alloc.
  - eauto using vcr_insert_term, vcr_preservation_insert.
  - eauto using vcr_preservation_read.
  - eauto using vcr_write_term, vcr_preservation_write.
  - eauto using vcr_preservation_acq.
  - eauto using vcr_preservation_rel.
  - eauto using vcr_preservation_spawn, vcr_preservation_spawned.
Qed.
*)

