From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.

(* ------------------------------------------------------------------------- *)
(* consistent-inits                                                          *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_inits (m : mem) : tm -> Prop :=
  | ci_unit  :                 consistent_inits m <{unit           }> 
  | ci_nat   : forall n,       consistent_inits m <{nat n          }>
  | ci_var   : forall x,       consistent_inits m <{var x          }>
  | ci_fun   : forall x Tx t,  consistent_inits m t  ->
                               consistent_inits m <{fn x Tx t      }>
  | ci_call  : forall t1 t2,   consistent_inits m t1 ->
                               consistent_inits m t2 ->
                               consistent_inits m <{call t1 t2     }> 
  | ci_ref   : forall ad T,    consistent_inits m <{&ad : T        }>

  | ci_initR : forall ad t T,  m[ad].t = None        ->
                               m[ad].T = `r&T`       ->
                               consistent_inits m t  ->
                               consistent_inits m <{init ad t : r&T}> 

  | ci_initX : forall ad t T,  m[ad].t = None        ->
                               m[ad].T = `x&T`       ->
                               consistent_inits m t  ->
                               consistent_inits m <{init ad t : x&T}> 

  | ci_initW : forall ad t T,  m[ad].t = None        ->
                               m[ad].T = `w&T`       ->
                               consistent_inits m t  ->
                               consistent_inits m <{init ad t : w&T}> 

  | ci_new   : forall T t,     consistent_inits m t  ->
                               consistent_inits m <{new t : T      }> 
  | ci_load  : forall t,       consistent_inits m t  ->
                               consistent_inits m <{*t             }> 
  | ci_asg   : forall t1 t2,   consistent_inits m t1 ->
                               consistent_inits m t2 ->
                               consistent_inits m <{t1 := t2       }> 
  | ci_acq   : forall t1 x t2, consistent_inits m t1 ->
                               consistent_inits m t2 ->
                               consistent_inits m <{acq t1 x t2    }>
  | ci_cr    : forall ad t,    consistent_inits m t  ->
                               consistent_inits m <{cr ad t        }>
  | ci_spawn : forall t,       consistent_inits m t  ->
                               consistent_inits m <{spawn t        }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _ci tt :=
  match goal with
  | H : consistent_inits _ <{unit        }> |- _ => clear H
  | H : consistent_inits _ <{nat _       }> |- _ => clear H
  | H : consistent_inits _ <{var _       }> |- _ => clear H
  | H : consistent_inits _ <{fn _ _ _    }> |- _ => tt H
  | H : consistent_inits _ <{call _ _    }> |- _ => tt H
  | H : consistent_inits _ <{& _ : _     }> |- _ => clear H
  | H : consistent_inits _ <{new _ : _   }> |- _ => tt H
  | H : consistent_inits _ <{init _ _ : _}> |- _ => tt H
  | H : consistent_inits _ <{* _         }> |- _ => tt H
  | H : consistent_inits _ <{_ := _      }> |- _ => tt H
  | H : consistent_inits _ <{acq _ _ _   }> |- _ => tt H
  | H : consistent_inits _ <{cr _ _      }> |- _ => tt H
  | H : consistent_inits _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_ci  := _ci inv.
Ltac invc_ci := _ci invc.

(* theorems ---------------------------------------------------------------- *)

Theorem insert_then_uninitialized : forall m t1 t2 ad t T,
  consistent_inits m t1 ->
  (* --- *)
  t1 --[e_insert ad t T]--> t2 ->
  m[ad].t = None.
Proof.
  intros. ind_tstep; invc_ci; auto.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma ci_from_noinits : forall m t,
  no_inits t ->
  consistent_inits m t.
Proof.
  intros. induction t; invc_noinits; auto using consistent_inits.
Qed.

Lemma ci_insert_term : forall m t1 t2 ad t T,
  consistent_inits m t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  consistent_inits m t.
Proof.
  intros. ind_tstep; invc_ci; auto.
Qed.

Lemma ci_write_term : forall m t1 t2 ad t,
  consistent_inits m t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_inits m t.
Proof.
  intros. ind_tstep; invc_ci; auto.
Qed.

Local Corollary oneinit_from_ui : forall m ths tid t ad' t' T',
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  unique_initializers m ths ->
  ths[tid] --[e_insert ad' t' T']--> t ->
  one_init ad' ths[tid].
Proof.
  intros * ? Hui ?.
  assert (Had' : ad' < #m) by eauto using vad_insert_address.
  specialize (Hui ad' Had') as [Hfall Hfone].
  opt_dec (m[ad'].t); spec.
  - specialize Hfone as [tid' [? ?]].
    nat_eq_dec tid' tid; trivial.
    exfalso. eauto using noinit_insert_contradiction.
  - exfalso. eauto using noinit_insert_contradiction.
Qed.

Local Corollary noinit_from_ui : forall m ths tid1 tid2 ad,
  forall_threads ths (valid_addresses m) ->
  unique_initializers m ths ->
  (* --- *)
  tid1 <> tid2 ->
  one_init ad ths[tid1] ->
  no_init ad ths[tid2].
Proof.
  intros * ? Hui ? **.
  assert (Had : ad < #m) by eauto using oneinit_ad_bound.
  specialize (Hui ad Had) as [Hfall Hfone].
  opt_dec (m[ad].t); spec.
  - specialize Hfone as [tid' [? ?]].
    nat_eq_dec tid1 tid'; eauto using noinit_oneinit_contradiction.
  - eauto using noinit_oneinit_contradiction.
Qed.

(* preservation ------------------------------------------------------------ *)

Lemma ci_subst : forall m x tx t,
  consistent_inits m t ->
  consistent_inits m tx ->
  consistent_inits m <{[x := tx] t}>.
Proof.
  intros. induction t; invc_ci; simpl;
  try destruct _str_eq_dec; auto using consistent_inits.
Qed.

Lemma ci_mem_add : forall m t c,
  valid_addresses m t ->
  (* --- *)
  consistent_inits m t ->
  consistent_inits (m +++ c) t.
Proof.
  intros. induction t; invc_vad; invc_ci; constructor; sigma; auto.
Qed.

Lemma ci_mem_set1 : forall m t t' ad,
  no_init ad t ->
  (* --- *)
  consistent_inits m t' ->
  consistent_inits m t  ->
  consistent_inits m[ad.t <- t'] t.
Proof.
  intros. induction t; invc_noinit; invc_ci; constructor; sigma; auto.
Qed.

Lemma ci_mem_set2 : forall m t t' ad,
  no_inits t ->
  no_inits t' ->
  consistent_inits m[ad.t <- t'] t.
Proof.
  intros. induction t; invc_noinits; auto using consistent_inits.
Qed.

Lemma ci_mem_acq : forall m t ad,
  consistent_inits m t ->
  consistent_inits m[ad.X <- true] t.
Proof.
  intros. induction t; invc_ci; constructor; upsilon; auto.
Qed.

Lemma ci_mem_rel : forall m t ad,
  consistent_inits m t ->
  consistent_inits m[ad.X <- false] t.
Proof.
  intros. induction t; invc_ci; constructor; upsilon; auto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ci_preservation_none : forall m t1 t2,
  consistent_inits m t1 ->
  t1 --[e_none]--> t2 ->
  consistent_inits m t2.
Proof.
  intros. ind_tstep; repeat invc_ci; auto using ci_subst, consistent_inits.
Qed.

Lemma ci_preservation_alloc : forall m t1 t2 T,
  valid_addresses m t1 ->
  well_typed_term t1 ->
  (* --- *)
  consistent_inits m t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  consistent_inits (m +++ (None, T, false)) t2.
Proof.
  intros * ? [T ?] **. gendep T.
  ind_tstep; intros; invc_vad; invc_typeof; invc_ci;
  constructor; sigma; eauto using ci_mem_add.
Qed.

Lemma ci_preservation_insert : forall m t1 t2 ad t T,
  one_init ad t1 ->
  (* --- *)
  consistent_inits m t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  consistent_inits m[ad.t <- t] t2.
Proof.
  intros. assert (consistent_inits m t) by eauto using ci_insert_term.
  ind_tstep; invc_oneinit; invc_ci;
  constructor; sigma; eauto using ci_mem_set1;
  exfalso; eauto using noinit_insert_contradiction.
Qed.

Lemma ci_preservation_read : forall m t1 t2 ad t,
  consistent_inits m t ->
  (* --- *)
  consistent_inits m t1 ->
  t1 --[e_read ad t]--> t2 ->
  consistent_inits m t2.
Proof.
  intros. ind_tstep; invc_ci; eauto using consistent_inits.
Qed.

Lemma ci_preservation_write : forall m t1 t2 ad t,
  no_init ad t1 ->
  (* --- *)
  consistent_inits m t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_inits m[ad.t <- t] t2.
Proof.
  intros. ind_tstep; invc_noinit; invc_ci;
  eauto using consistent_inits;
  constructor; sigma; eauto using ci_write_term, ci_mem_set1.
Qed.

Lemma ci_preservation_acq : forall m t1 t2 ad t,
  consistent_inits m t ->
  (* --- *)
  consistent_inits m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  consistent_inits m[ad.X <- true] t2.
Proof.
  intros. eapply ci_mem_acq. ind_tstep; repeat invc_ci;
  eauto using ci_subst, consistent_inits.
Qed.

Lemma ci_preservation_rel : forall m t1 t2 ad,
  consistent_inits m t1 ->
  t1 --[e_rel ad]--> t2 ->
  consistent_inits m[ad.X <- false] t2.
Proof.
  intros. eapply ci_mem_rel. ind_tstep; repeat invc_ci;
  eauto using consistent_inits.
Qed.

Lemma ci_preservation_spawn : forall m t1 t2 tid t,
  consistent_inits m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistent_inits m t2.
Proof.
  intros. ind_tstep; invc_ci; eauto using consistent_inits.
Qed.

Lemma ci_preservation_spawned : forall m t1 t2 tid t,
  consistent_inits m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistent_inits m t.
Proof.
  intros. ind_tstep; invc_ci; eauto using consistent_inits.
Qed.

(* ------------------------------------------------------------------------- *)

Corollary ci_preservation_memory : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value ->
  forall_program m1 ths1 valid_blocks ->
  (* --- *)
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_memory m2 (consistent_inits m2).
Proof.
  intros ** ? ? ?.
  assert (forall_memory m2 value)
    by eauto using value_preservation.
  assert (forall_program m2 ths2 valid_blocks) as [? _]
    by eauto using vb_preservation.
  eauto using noinits_from_value, ci_from_noinits.
Qed.

Corollary ci_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_addresses m1) ->
  forall_program m1 ths1 valid_blocks ->
  forall_program m1 ths1 well_typed_term ->
  no_uninitialized_references m1 ths1 ->
  unique_initializers m1 ths1 ->
  (* --- *)
  forall_memory  m1   (consistent_inits m1) ->
  forall_threads ths1 (consistent_inits m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (consistent_inits m2).
Proof.
  intros * [? ?] [? ?] [? ?] ? Hui ? ? ?.
  invc_cstep; try invc_mstep.
  - upsilon. eauto using ci_preservation_none.
  - upsilon; eauto using ci_mem_add, ci_preservation_alloc.
  - assert (one_init ad ths1[tid]) by eauto using oneinit_from_ui.
    upsilon; eauto using ci_preservation_insert. intros.
    assert (no_init  ad ths1[tid']) by eauto using noinit_from_ui.
    eapply ci_mem_set1; eauto using ci_from_noinits,
      vb_insert_term, value_insert_term, noinits_from_value.
  - upsilon. eauto using ci_preservation_read.
  - assert (m1[ad].t <> None) by eauto using write_then_initialized. 
    specialize (Hui ad) as [Hnoinit _]; trivial. spec.
    upsilon; eauto using ci_write_term, ci_mem_set1, ci_preservation_write.
  - upsilon; eauto using ci_mem_acq, ci_preservation_acq.
  - upsilon; eauto using ci_mem_rel, ci_preservation_rel.
  - upsilon; eauto using ci_preservation_spawn, ci_preservation_spawned.
Qed.

Theorem ci_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value ->
  forall_program m1 ths1 (valid_addresses m1) ->
  forall_program m1 ths1 valid_blocks ->
  forall_program m1 ths1 well_typed_term ->
  no_uninitialized_references m1 ths1 ->
  unique_initializers m1 ths1 ->
  (* --- *)
  forall_program m1 ths1 (consistent_inits m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (consistent_inits m2).
Proof.
  intros until 6. intros [? ?] **. split;
  eauto using ci_preservation_memory, ci_preservation_threads.
Qed.

