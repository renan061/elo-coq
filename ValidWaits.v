From Elo Require Import Core.

From Elo Require Import NoWaits.
From Elo Require Import ReservedWaits.

(* ------------------------------------------------------------------------- *)
(* valid-waits                                                               *)
(* ------------------------------------------------------------------------- *)

(* Enforces:
    - x cannot be SELF in acquire statements.
    - x cannot be SELF in function abstractions.
    - the body of a function abstraction cannot have waits.
*)
Inductive valid_waits : tm -> Prop :=
  | vwaits_unit  :                  valid_waits <{unit                     }>
  | vwaits_nat   : forall n,        valid_waits <{nat n                    }>
  | vwaits_plus  : forall t1 t2,    valid_waits t1 ->
                                    valid_waits t2 ->
                                    valid_waits <{t1 + t2                  }>
  | vwaits_monus : forall t1 t2,    valid_waits t1 ->
                                    valid_waits t2 ->
                                    valid_waits <{t1 - t2                  }>
  | vwaits_seq   : forall t1 t2,    valid_waits t1 ->
                                    valid_waits t2 ->
                                    valid_waits <{t1; t2                   }>
  | vwaits_if    : forall t1 t2 t3, valid_waits t1 ->
                                    valid_waits t2 ->
                                    valid_waits t3 ->
                                    valid_waits <{if t1 then t2 else t3 end}>
  | vwaits_while : forall t1 t2,    valid_waits t1 ->
                                    valid_waits t2 ->
                                    valid_waits <{while t1 do t2 end       }>
  | vwaits_var   : forall x,        valid_waits <{var x                    }>
  | vwaits_fun   : forall x Tx t,   x <> SELF      ->
                                    no_waits    t  ->
                                    valid_waits t  ->
                                    valid_waits <{fn x Tx t                }>
  | vwaits_call  : forall t1 t2,    valid_waits t1 ->
                                    valid_waits t2 ->
                                    valid_waits <{call t1 t2               }>
  | vwaits_ref   : forall ad T,     valid_waits <{&ad : T                  }>
  | vwaits_new   : forall t T,      valid_waits t  ->
                                    valid_waits <{new t : T                }>
  | vwaits_init  : forall ad t T,   valid_waits t  ->
                                    valid_waits <{init ad t : T            }>
  | vwaits_load  : forall t,        valid_waits t  ->
                                    valid_waits <{*t                       }>
  | vwaits_asg   : forall t1 t2,    valid_waits t1 ->
                                    valid_waits t2 ->
                                    valid_waits <{t1 := t2                 }>
  | vwaits_acq   : forall t1 x t2,  x <> SELF        ->
                                    valid_waits t1 ->
                                    valid_waits t2 ->
                                    valid_waits <{acq t1 x t2              }>
  | vwaits_cr    : forall ad t,     valid_waits t  ->
                                    valid_waits <{cr ad t                  }>
  | vwaits_wait  : forall t,        valid_waits t  ->
                                    valid_waits <{wait t                   }>
  | vwaits_reacq : forall ad,       valid_waits <{reacq ad                 }>
  | vwaits_spawn : forall t,        reserved_waits t ->
                                    valid_waits t    ->
                                    valid_waits <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vwaits tt :=
  match goal with
  | H : valid_waits <{unit                  }> |- _ => clear H
  | H : valid_waits <{nat _                 }> |- _ => clear H
  | H : valid_waits <{_ + _                 }> |- _ => tt H
  | H : valid_waits <{_ - _                 }> |- _ => tt H
  | H : valid_waits <{_; _                  }> |- _ => tt H
  | H : valid_waits <{if _ then _ else _ end}> |- _ => tt H
  | H : valid_waits <{while _ do _ end      }> |- _ => tt H
  | H : valid_waits <{var _                 }> |- _ => clear H
  | H : valid_waits <{fn _ _ _              }> |- _ => tt H
  | H : valid_waits <{call _ _              }> |- _ => tt H
  | H : valid_waits <{&_ : _                }> |- _ => clear H
  | H : valid_waits <{new _ : _             }> |- _ => tt H
  | H : valid_waits <{init _ _ : _          }> |- _ => tt H
  | H : valid_waits <{* _                   }> |- _ => tt H
  | H : valid_waits <{_ := _                }> |- _ => tt H
  | H : valid_waits <{acq _ _ _             }> |- _ => tt H
  | H : valid_waits <{cr _ _                }> |- _ => tt H
  | H : valid_waits <{wait _                }> |- _ => tt H
  | H : valid_waits <{reacq _               }> |- _ => clear H
  | H : valid_waits <{spawn _               }> |- _ => tt H
  end.

Ltac inv_vwaits  := _vwaits inv.
Ltac invc_vwaits := _vwaits invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma vwaits_init_term : forall t1 t2 ad' t',
  valid_waits t1 ->
  t1 --[e_init ad' t']--> t2 ->
  valid_waits t'.
Proof.
  intros. ind_tstep; invc_vwaits; auto.
Qed.

Lemma vwaits_write_term : forall t1 t2 ad' t',
  valid_waits t1 ->
  t1 --[e_write ad' t']--> t2 ->
  valid_waits t'.
Proof.
  intros. ind_tstep; invc_vwaits; auto.
Qed.

Lemma rwaits_spawn_term : forall t1 t2 t',
  valid_waits t1 ->
  (* --- *)
  t1 --[e_spawn t']--> t2 ->
  reserved_waits t'.
Proof.
  intros. ind_tstep; invc_vwaits; auto.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma nowaits_from_value : forall t,
  valid_waits t ->
  (* --- *)
  value t       ->
  no_waits t.
Proof.
  intros * ? Hval. destruct Hval; invc_vwaits; auto using no_waits.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma vwaits_subst : forall x tx t,
  value tx       ->
  (* --- *)
  valid_waits t  ->
  valid_waits tx ->
  valid_waits <{[x := tx] t}>.
Proof. 
  intros. induction t; invc_vwaits;
  simpl; repeat destruct _str_eq_dec;
  auto using nowaits_from_value, nowaits_subst, rwaits_subst, valid_waits.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_vwaits_preservation :=
  intros; ind_tstep; repeat invc_vwaits;
  auto using vwaits_subst, valid_waits, value.

Lemma vwaits_preservation_none : forall t1 t2,
  valid_waits t1 ->
  t1 --[e_none]--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_alloc : forall t1 t2 ad' T',
  valid_waits t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_init : forall t1 t2 ad' t',
  valid_waits t1 ->
  t1 --[e_init ad' t']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_read : forall t1 t2 ad' t',
  valid_waits t' ->
  (* --- *)
  valid_waits t1 ->
  t1 --[e_read ad' t']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_write : forall t1 t2 ad' t',
  valid_waits t1 ->
  t1 --[e_write ad' t']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_acq : forall t1 t2 ad' t',
  value t'       ->
  valid_waits t' ->
  (* --- *)
  valid_waits t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_rel : forall t1 t2 ad',
  valid_waits t1 ->
  t1 --[e_rel ad']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_wacq : forall t1 t2 ad',
  valid_waits t1 ->
  t1 --[e_wacq ad']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_wrel : forall t1 t2 ad',
  valid_waits t1 ->
  t1 --[e_wrel ad']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_spawn : forall t1 t2 t',
  valid_waits t1 ->
  t1 --[e_spawn t']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation. Qed.

Lemma vwaits_preservation_spawned : forall t1 t2 t',
  valid_waits t1 ->
  t1 --[e_spawn t']--> t2 ->
  valid_waits t'.
Proof. solve_vwaits_preservation. Qed.

(* preservation ------------------------------------------------------------ *)

Corollary vwaits_preservation_memory : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 valid_waits ->
  forall_memory  m1   valid_waits ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  forall_memory  m2   valid_waits.
Proof.
  intros. invc_cstep; try invc_mstep; trivial; intros ? ? ?;
  upsilon; eauto using vwaits_init_term, vwaits_write_term.
  omicron; upsilon; auto; eauto.
Qed.

Corollary vwaits_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   value       ->
  (* --- *)
  forall_memory  m1   valid_waits ->
  forall_threads ths1 valid_waits ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  forall_threads ths2 valid_waits.
Proof.
  intros. invc_cstep; try invc_mstep; upsilon.
  - eauto using vwaits_preservation_none. 
  - eauto using vwaits_preservation_alloc. 
  - eauto using vwaits_preservation_init.
  - eauto using vwaits_preservation_read.
  - eauto using vwaits_preservation_write.
  - eauto using vwaits_preservation_acq.
  - eauto using vwaits_preservation_rel.
  - eauto using vwaits_preservation_wacq.
  - eauto using vwaits_preservation_wrel.
  - eauto using vwaits_preservation_spawn.
  - eauto using vwaits_preservation_spawned.
Qed.

Theorem vwaits_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   value          ->
  (* --- *)
  forall_program m1 ths1 valid_waits ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2  ->
  forall_program m2 ths2 valid_waits.
Proof.
  intros * ? [? ?] ?. split;
  eauto using vwaits_preservation_memory, vwaits_preservation_threads.
Qed.

