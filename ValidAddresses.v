From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* valid-addresses                                                           *)
(* ------------------------------------------------------------------------- *)

Inductive valid_addresses (m : mem) : tm -> Prop :=
  | vad_unit  :                 valid_addresses m <{unit         }> 
  | vad_nat   : forall n,       valid_addresses m <{nat n        }>
  | vad_var   : forall x,       valid_addresses m <{var x        }>
  | vad_fun   : forall x Tx t,  valid_addresses m t  ->
                                valid_addresses m <{fn x Tx t    }>
  | vad_call  : forall t1 t2,   valid_addresses m t1 ->
                                valid_addresses m t2 ->
                                valid_addresses m <{call t1 t2   }> 
  | vad_ref   : forall ad T,    ad < #m              ->
                                valid_addresses m <{&ad : T      }>
  | vad_init  : forall ad t T,  ad < #m              ->
                                valid_addresses m t  ->
                                valid_addresses m <{init ad t : T}> 
  | vad_new   : forall T t,     valid_addresses m t  ->
                                valid_addresses m <{new t : T    }>
  | vad_load  : forall t,       valid_addresses m t  ->
                                valid_addresses m <{*t           }> 
  | vad_asg   : forall t1 t2,   valid_addresses m t1 ->
                                valid_addresses m t2 ->
                                valid_addresses m <{t1 := t2     }> 
  | vad_acq   : forall t1 x t2, valid_addresses m t1 ->
                                valid_addresses m t2 ->
                                valid_addresses m <{acq t1 x t2  }>
  | vad_cr    : forall ad t,    ad < #m              ->
                                valid_addresses m t  ->
                                valid_addresses m <{cr ad t      }>
  | vad_spawn : forall t,       valid_addresses m t  ->
                                valid_addresses m <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vad tt :=
  match goal with
  | H : valid_addresses _ <{unit        }> |- _ => clear H
  | H : valid_addresses _ <{nat _       }> |- _ => clear H
  | H : valid_addresses _ <{var _       }> |- _ => clear H
  | H : valid_addresses _ <{fn _ _ _    }> |- _ => tt H
  | H : valid_addresses _ <{call _ _    }> |- _ => tt H
  | H : valid_addresses _ <{& _ : _     }> |- _ => tt H
  | H : valid_addresses _ <{new _ : _   }> |- _ => tt H
  | H : valid_addresses _ <{init _ _ : _}> |- _ => tt H
  | H : valid_addresses _ <{* _         }> |- _ => tt H
  | H : valid_addresses _ <{_ := _      }> |- _ => tt H
  | H : valid_addresses _ <{acq _ _ _   }> |- _ => tt H
  | H : valid_addresses _ <{cr _ _      }> |- _ => tt H
  | H : valid_addresses _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_vad  := _vad inv.
Ltac invc_vad := _vad invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma vad_insert_term : forall m t1 t2 ad t,
  valid_addresses m t1 ->
  t1 --[e_insert ad t]--> t2 ->
  valid_addresses m t.
Proof.
  intros. ind_tstep; invc_vad; auto.
Qed.

Lemma vad_write_term : forall m t1 t2 ad t,
  valid_addresses m t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_addresses m t.
Proof.
  intros. ind_tstep; invc_vad; auto.
Qed.

Lemma vad_insert_address : forall m t1 t2 ad t,
  valid_addresses m t1 ->
  t1 --[e_insert ad t]--> t2 ->
  ad < #m.
Proof.
  intros. ind_tstep; invc_vad; auto.
Qed.

Lemma vad_write_address : forall m t1 t2 ad t,
  valid_addresses m t1 ->
  t1 --[e_write ad t]--> t2 ->
  ad < #m.
Proof.
  intros. ind_tstep; repeat invc_vad; auto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma vad_subst : forall m t tx x,
  valid_addresses m t ->
  valid_addresses m tx ->
  valid_addresses m <{[x := tx] t}>.
Proof.
  intros. induction t; invc_vad;
  simpl; try destruct _str_eq_dec; auto using valid_addresses.
Qed.

Lemma vad_mem_add : forall m t c,
  valid_addresses m t ->
  valid_addresses (m +++ c) t.
Proof.
  intros. induction t; invc_vad; constructor; sigma; auto.
Qed.

Lemma vad_mem_set : forall m t ad' t',
  valid_addresses m t ->
  valid_addresses m[ad'.t <- t'] t.
Proof.
  intros. induction t; invc_vad; constructor; sigma; auto.
Qed.

Lemma vad_mem_acq : forall m t ad,
  valid_addresses m t ->
  valid_addresses m[ad.X <- true] t.
Proof.
  intros. induction t; invc_vad; constructor; sigma; auto.
Qed.

Lemma vad_mem_rel : forall m t ad,
  valid_addresses m t ->
  valid_addresses m[ad.X <- false] t.
Proof.
  intros. induction t; invc_vad; constructor; sigma; auto.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_vad_preservation :=
  intros; ind_tstep; repeat invc_vad;
  auto using valid_addresses, vad_subst,
             vad_mem_add, vad_mem_set,
             vad_mem_acq, vad_mem_rel;
  constructor; sigma; auto using vad_mem_add.

Lemma vad_preservation_none : forall m t1 t2,
  valid_addresses m t1 ->
  t1 --[e_none]--> t2 ->
  valid_addresses m t2.
Proof. solve_vad_preservation. Qed.

Lemma vad_preservation_alloc : forall m t1 t2 T,
  valid_addresses m t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  valid_addresses (m +++ (None, T, false)) t2.
Proof. solve_vad_preservation. Qed.

Lemma vad_preservation_insert : forall m t1 t2 ad t,
  valid_addresses m t1 ->
  t1 --[e_insert ad t]--> t2 ->
  valid_addresses (m[ad.t <- t]) t2.
Proof. solve_vad_preservation. Qed.

Lemma vad_preservation_read : forall m t1 t2 ad t,
  valid_addresses m t ->
  (* --- *)
  valid_addresses m t1 ->
  t1 --[e_read ad t]--> t2 ->
  valid_addresses m t2.
Proof. solve_vad_preservation. Qed.

Lemma vad_preservation_write : forall m t1 t2 ad t,
  valid_addresses m t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_addresses (m[ad.t <- t]) t2.
Proof. solve_vad_preservation. Qed.

Lemma vad_preservation_acq : forall m t1 t2 ad t,
  valid_addresses m t ->
  (* --- *)
  valid_addresses m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  valid_addresses m[ad.X <- true] t2.
Proof. solve_vad_preservation. Qed.

Lemma vad_preservation_rel : forall m t1 t2 ad,
  valid_addresses m t1 ->
  t1 --[e_rel ad]--> t2 ->
  valid_addresses m[ad.X <- false] t2.
Proof. solve_vad_preservation. Qed.

Lemma vad_preservation_spawn : forall m t1 t2 tid t,
  valid_addresses m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_addresses m t2.
Proof. solve_vad_preservation. Qed.

Lemma vad_preservation_spawned : forall m t1 t2 tid t,
  valid_addresses m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_addresses m t.
Proof. solve_vad_preservation. Qed.

(* ------------------------------------------------------------------------- *)

Corollary vad_preservation_memory : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 (valid_addresses m1) ->
  forall_memory  m1   (valid_addresses m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_memory  m2   (valid_addresses m2).
Proof.
  intros. invc_cstep; try invc_mstep; trivial; intros ? ? ?.
  - upsilon. eauto using vad_mem_add.
  - upsilon; eauto using vad_insert_term, vad_mem_set.
  - upsilon; eauto using vad_write_term, vad_mem_set.
  - upsilon. eauto using vad_mem_acq.
  - upsilon. eauto using vad_mem_rel.
Qed.

Corollary vad_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   (valid_addresses m1) ->
  forall_threads ths1 (valid_addresses m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (valid_addresses m2).
Proof.
  intros. invc_cstep; try invc_mstep.
  - upsilon. eauto using vad_preservation_none.
  - upsilon; eauto using vad_mem_add, vad_preservation_alloc.
  - upsilon; eauto using vad_mem_set, vad_preservation_insert.
  - upsilon. eauto using vad_preservation_read.
  - upsilon; eauto using vad_mem_set, vad_preservation_write.
  - upsilon; eauto using vad_mem_acq, vad_preservation_acq.
  - upsilon; eauto using vad_mem_rel, vad_preservation_rel.
  - upsilon; eauto using vad_preservation_spawn, vad_preservation_spawned.
Qed.

Theorem vad_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_addresses m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (valid_addresses m2).
Proof.
  intros * [? ?] ?. split;
  eauto using vad_preservation_memory, vad_preservation_threads.
Qed.

