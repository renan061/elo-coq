From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.

(* ------------------------------------------------------------------------- *)
(* consistent-term                                                           *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_term (m : mem) : tm -> Prop :=
  | ctm_unit  :                 consistent_term m <{unit           }> 
  | ctm_nat   : forall n,       consistent_term m <{nat n          }>
  | ctm_seq   : forall t1 t2,   consistent_term m t1    ->
                                consistent_term m t2    ->
                                consistent_term m <{t1; t2         }> 
  | ctm_var   : forall x,       consistent_term m <{var x          }>
  | ctm_fun   : forall x Tx t,  consistent_term m t     ->
                                consistent_term m <{fn x Tx t      }>
  | ctm_call  : forall t1 t2,   consistent_term m t1    ->
                                consistent_term m t2    ->
                                consistent_term m <{call t1 t2     }> 

  | ctm_refR  : forall ad t T,  m[ad].t = Some t        ->
                                m[ad].T = `r&T`         ->
                                empty |-- t is `Safe T` ->
                                consistent_term m <{&ad : r&T      }>

  | ctm_refX  : forall ad t T,  m[ad].t = Some t        ->
                                m[ad].T = `x&T`         ->
                                empty |-- t is T        ->
                                consistent_term m <{&ad : x&T      }>

  | ctm_refW  : forall ad t T,  m[ad].t = Some t        ->
                                m[ad].T = `w&T`         ->
                                empty |-- t is T        ->
                                consistent_term m <{&ad : w&T      }>

  | ctm_initR : forall ad t T,  m[ad].t = None          ->
                                m[ad].T = `r&T`         ->
                                consistent_term m t     ->
                                consistent_term m <{init ad t : r&T}> 

  | ctm_initX : forall ad t T,  m[ad].t = None          ->
                                m[ad].T = `x&T`         ->
                                consistent_term m t     ->
                                consistent_term m <{init ad t : x&T}> 

  | ctm_initW : forall ad t T,  m[ad].t = None          ->
                                m[ad].T = `w&T`         ->
                                consistent_term m t     ->
                                consistent_term m <{init ad t : w&T}> 

  | ctm_new   : forall T t,     consistent_term m t     ->
                                consistent_term m <{new t : T      }> 
  | ctm_load  : forall t,       consistent_term m t     ->
                                consistent_term m <{*t             }> 
  | ctm_asg   : forall t1 t2,   consistent_term m t1    ->
                                consistent_term m t2    ->
                                consistent_term m <{t1 := t2       }> 
  | ctm_acq   : forall t1 x t2, consistent_term m t1    ->
                                consistent_term m t2    ->
                                consistent_term m <{acq t1 x t2    }>
  | ctm_cr    : forall ad t,    consistent_term m t     ->
                                consistent_term m <{cr ad t        }>
  | ctm_spawn : forall t,       consistent_term m t     ->
                                consistent_term m <{spawn t        }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _ctm tt :=
  match goal with
  | H : consistent_term _ <{unit        }> |- _ => clear H
  | H : consistent_term _ <{nat _       }> |- _ => clear H
  | H : consistent_term _ <{_; _        }> |- _ => tt H
  | H : consistent_term _ <{var _       }> |- _ => clear H
  | H : consistent_term _ <{fn _ _ _    }> |- _ => tt H
  | H : consistent_term _ <{call _ _    }> |- _ => tt H
  | H : consistent_term _ <{& _ : _     }> |- _ => tt H
  | H : consistent_term _ <{new _ : _   }> |- _ => tt H
  | H : consistent_term _ <{init _ _ : _}> |- _ => tt H
  | H : consistent_term _ <{* _         }> |- _ => tt H
  | H : consistent_term _ <{_ := _      }> |- _ => tt H
  | H : consistent_term _ <{acq _ _ _   }> |- _ => tt H
  | H : consistent_term _ <{cr _ _      }> |- _ => tt H
  | H : consistent_term _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_ctm  := _ctm inv.
Ltac invc_ctm := _ctm invc.

(* theorems ---------------------------------------------------------------- *)

Theorem insert_then_uninitialized : forall m t1 t2 ad t T,
  consistent_term m t1 ->
  (* --- *)
  t1 --[e_insert ad t T]--> t2 ->
  m[ad].t = None.
Proof.
  intros. ind_tstep; invc_ctm; auto.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma ctm_from_norefs_noinits : forall m t,
  no_refs  t ->
  no_inits t ->
  consistent_term m t.
Proof.
  intros. induction t; invc_norefs; invc_noinits; eauto using consistent_term.
Qed.

Lemma ctm_insert_term : forall m t1 t2 ad' t' T',
  consistent_term m t1 ->
  t1 --[e_insert ad' t' T']--> t2 ->
  consistent_term m t'.
Proof.
  intros. ind_tstep; invc_ctm; auto.
Qed.

Lemma ctm_write_term : forall m t1 t2 ad' t',
  consistent_term m t1 ->
  t1 --[e_write ad' t']--> t2 ->
  consistent_term m t'.
Proof.
  intros. ind_tstep; invc_ctm; auto.
Qed.

Lemma ctm_insert_type : forall m t1 t2 ad' t' T',
  well_typed_term   t1 ->
  consistent_term m t1 ->
  (* --- *)
  t1 --[e_insert ad' t' T']--> t2 ->
  (exists T, empty |-- t' is `Safe T` /\ m[ad'].T = `r&T`) \/
  (exists T, empty |-- t' is T        /\ m[ad'].T = `x&T`) \/
  (exists T, empty |-- t' is T        /\ m[ad'].T = `w&T`).
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; invc_typeof; invc_ctm; eauto.
Qed.

Lemma ctm_write_type : forall m t1 t2 ad' t',
  well_typed_term   t1 ->
  consistent_term m t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  (exists T, empty |-- t' is T /\ m[ad'].T = `w&T`).
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_ctm; eauto.
Qed.

(* preservation ------------------------------------------------------------ *)

Lemma ctm_subst : forall m x tx t,
  consistent_term m t ->
  consistent_term m tx ->
  consistent_term m <{[x := tx] t}>.
Proof.
  intros. induction t; invc_ctm; simpl;
  try destruct _str_eq_dec; eauto using consistent_term.
Qed.

Lemma ctm_mem_add : forall m t c,
  valid_term m t ->
  (* --- *)
  consistent_term m t ->
  consistent_term (m +++ c) t.
Proof.
  intros. induction t; invc_vtm; invc_ctm; econstructor; sigma; eauto.
Qed.

Lemma ctm_mem_set : forall m t t' ad,
  ((exists T, empty |-- t' is `Safe T` /\ m[ad].T = `r&T` ) \/
   (exists T, empty |-- t' is T        /\ m[ad].T = `x&T` ) \/
   (exists T, empty |-- t' is T        /\ m[ad].T = `w&T`)) ->
  no_init ad t ->
  (* --- *)
  consistent_term m t  ->
  consistent_term m t' ->
  consistent_term m[ad.t <- t'] t.
Proof.
  intros * [[? [? ?]] | [[? [? ?]] | [? [? ?]]]] **;
  assert (ad < #m) by (lt_eq_gt (#m) ad; sigma; trivial; discriminate);
  induction t; invc_noinit; invc_ctm; try constructor; sigma; eauto;
  match goal with H1 : _[?ad1].T = _, H2 : _[?ad2].T = _ |- _ =>
    nat_eq_dec ad1 ad2; try invc_eq
  end;
  econstructor; sigma; upsilon; eauto.
Qed.

Lemma ctm_mem_acq : forall m t ad,
  consistent_term m t ->
  consistent_term m[ad.X <- true] t.
Proof.
  intros. induction t; invc_ctm; econstructor; upsilon; eauto.
Qed.

Lemma ctm_mem_rel : forall m t ad,
  consistent_term m t ->
  consistent_term m[ad.X <- false] t.
Proof.
  intros. induction t; invc_ctm; econstructor; upsilon; eauto.
Qed.

Lemma ctm_mem_region : forall m t ad R,
  consistent_term m t ->
  consistent_term m[ad.R <- R] t.
Proof.
  intros. induction t; invc_ctm; econstructor; repeat omicron; eauto.
Qed.

Local Corollary oneinit_from_ui : forall m ths tid t ad' t' T',
  forall_threads ths (valid_term m) ->
  (* --- *)
  unique_initializers m ths ->
  ths[tid] --[e_insert ad' t' T']--> t ->
  one_init ad' ths[tid].
Proof.
  intros * ? Hui ?.
  assert (Had' : ad' < #m) by eauto using vtm_insert_address.
  specialize (Hui ad' Had') as [Hfall Hfone].
  opt_dec (m[ad'].t); spec.
  - specialize Hfone as [tid' [? ?]].
    nat_eq_dec tid' tid; trivial.
    exfalso. eauto using noinit_insert_contradiction.
  - exfalso. eauto using noinit_insert_contradiction.
Qed.

Local Corollary noinit_from_ui : forall m ths tid1 tid2 ad,
  forall_threads ths (valid_term m) ->
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

(* ------------------------------------------------------------------------- *)

Lemma ctm_preservation_none : forall m t1 t2,
  consistent_term m t1 ->
  t1 --[e_none]--> t2 ->
  consistent_term m t2.
Proof.
  intros. ind_tstep; repeat invc_ctm; eauto using ctm_subst, consistent_term.
Qed.

Lemma ctm_preservation_alloc : forall m t1 t2 T',
  valid_term m t1 ->
  well_typed_term t1 ->
  (* --- *)
  consistent_term m t1 ->
  t1 --[e_alloc (#m) T']--> t2 ->
  consistent_term (m +++ (None, T', false, R_invalid)) t2.
Proof.
  intros * ? [T ?] **. gendep T.
  ind_tstep; intros; invc_vtm; invc_typeof; invc_ctm;
  constructor; sigma; auto; eauto using ctm_mem_add.
Qed.

Lemma ctm_preservation_insert : forall m t1 t2 ad' t' T',
  well_typed_term t1 ->
  (* --- *)
  one_init ad' t1 ->
  consistent_term m t1 ->
  t1 --[e_insert ad' t' T']--> t2 ->
  consistent_term m[ad'.t <- t'] t2.
Proof.
  intros * Hwtt **.
  assert (Hwtt' := Hwtt). specialize Hwtt' as [T ?]. gendep T.
  assert (consistent_term m t') by eauto using ctm_insert_term.
  ind_tstep; intros; invc_wtt; invc_typeof; invc_oneinit; invc_ctm;
  try solve [exfalso; eauto using noinit_insert_contradiction];
  eauto using ctm_insert_type, ctm_mem_set, consistent_term;
  econstructor; sigma; eauto; try omicron; upsilon; auto; discriminate.
Qed.

Lemma ctm_preservation_read : forall m t1 t2 ad' t',
  consistent_term m t' ->
  (* --- *)
  consistent_term m t1 ->
  t1 --[e_read ad' t']--> t2 ->
  consistent_term m t2.
Proof.
  intros. ind_tstep; invc_ctm; eauto using consistent_term.
Qed.

Lemma ctm_preservation_write : forall m t1 t2 ad' t',
  well_typed_term t1 ->
  (* --- *)
  no_init ad' t1 ->
  consistent_term m t1 ->
  t1 --[e_write ad' t']--> t2 ->
  consistent_term m[ad'.t <- t'] t2.
Proof.
  intros. assert (consistent_term m t') by eauto using ctm_write_term.
  ind_tstep; invc_noinit; invc_wtt; invc_ctm; constructor; sigma;
  eauto 7 using ctm_write_type, ctm_mem_set.
Qed.

Lemma ctm_preservation_acq : forall m t1 t2 ad' t',
  consistent_term m t' ->
  (* --- *)
  consistent_term m t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  consistent_term m[ad'.X <- true] t2.
Proof.
  intros. eapply ctm_mem_acq. ind_tstep; invc_ctm;
  eauto using ctm_subst, consistent_term.
Qed.

Lemma ctm_preservation_rel : forall m t1 t2 ad',
  consistent_term m t1 ->
  t1 --[e_rel ad']--> t2 ->
  consistent_term m[ad'.X <- false] t2.
Proof.
  intros. eapply ctm_mem_rel. ind_tstep; invc_ctm;
  eauto using consistent_term.
Qed.

Lemma ctm_preservation_spawn : forall m t1 t2 tid' t',
  consistent_term m t1 ->
  t1 --[e_spawn tid' t']--> t2 ->
  consistent_term m t2.
Proof.
  intros. ind_tstep; invc_ctm; eauto using consistent_term.
Qed.

Lemma ctm_preservation_spawned : forall m t1 t2 tid' t',
  consistent_term m t1 ->
  t1 --[e_spawn tid' t']--> t2 ->
  consistent_term m t'.
Proof.
  intros. ind_tstep; invc_ctm; eauto using consistent_term.
Qed.

(* ------------------------------------------------------------------------- *)

Corollary ctm_preservation_memory : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value ->
  forall_program m1 ths1 (valid_term m1) ->
  forall_program m1 ths1 well_typed_term ->
  (* --- *)
  forall_memory  m1   (consistent_term m1) ->
  forall_threads ths1 (consistent_term m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_memory  m2   (consistent_term m2).
Proof.
  intros * ? [? ?] [? ?] **.
  invc_cstep; trivial. invc_mstep; trivial; repeat intro;
  try solve [upsilon; eauto using ctm_mem_add, ctm_mem_acq, ctm_mem_rel].
  - upsilon; eapply ctm_mem_set;
    eauto using value_insert_term, vtm_insert_term, noinit_from_value,
      ctm_insert_term, ctm_insert_type.
  - upsilon; eapply ctm_mem_set;
    eauto using value_write_term, vtm_write_term, noinit_from_value,
      ctm_write_term, ctm_write_type.
Qed.

Corollary ctm_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_term m1) ->
  forall_program m1 ths1 well_typed_term ->
  no_uninitialized_references m1 ths1 ->
  unique_initializers m1 ths1 ->
  (* --- *)
  forall_memory  m1   (consistent_term m1) ->
  forall_threads ths1 (consistent_term m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (consistent_term m2).
Proof.
  intros * [? ?] [? ?] ? Hui ? ? ?.
  invc_cstep; try invc_mstep.
  - upsilon. eauto using ctm_preservation_none.
  - upsilon; eauto using ctm_mem_add, ctm_preservation_alloc.
  - assert (one_init ad ths1[tid]) by eauto using oneinit_from_ui.
    upsilon; eauto using ctm_preservation_insert. intros.
    assert (no_init  ad ths1[tid']) by eauto using noinit_from_ui.
    eauto using ctm_insert_term, ctm_insert_type, ctm_mem_set.
  - upsilon. eauto using ctm_preservation_read.
  - assert (m1[ad].t <> None) by eauto using write_then_initialized. 
    specialize (Hui ad) as [Hnoinit _]; trivial. spec.
    upsilon; intros;
    eauto 6 using ctm_write_term, ctm_write_type, ctm_mem_set,
      ctm_preservation_write.
  - upsilon; eauto using ctm_mem_acq, ctm_preservation_acq.
  - upsilon; eauto using ctm_mem_rel, ctm_preservation_rel.
  - upsilon; eauto using ctm_preservation_spawn, ctm_preservation_spawned.
Qed.

Theorem ctm_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value ->
  forall_program m1 ths1 (valid_term m1) ->
  forall_program m1 ths1 well_typed_term ->
  no_uninitialized_references m1 ths1 ->
  unique_initializers m1 ths1 ->
  (* --- *)
  forall_program m1 ths1 (consistent_term m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (consistent_term m2).
Proof.
  intros until 5. intros [? ?] **.
  split; eauto using ctm_preservation_memory, ctm_preservation_threads.
Qed.

Theorem ctm_preservation_rstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1 value ->
  forall_program m1 ths1 (valid_term m1) ->
  forall_program m1 ths1 well_typed_term ->
  no_uninitialized_references m1 ths1 ->
  unique_initializers         m1 ths1 ->
  (* --- *)
  forall_program m1 ths1 (consistent_term m1) ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (consistent_term m2).
Proof.
  intros. invc_ostep; eauto using ctm_preservation_cstep.
  match goal with _ : _ / _ ~~[_, _]~~> ?m / ?ths |- _ =>
    assert (forall_program m ths (consistent_term m)) as [? ?]
      by eauto using ctm_preservation_cstep
  end.
  split; repeat intro; repeat omicron; upsilon; eauto using ctm_mem_region.
Qed.

Theorem ctm_preservation_base : forall t,
  no_refs  t ->
  no_inits t ->
  (* --- *)
  forall_program base_m (base_t t) (consistent_term base_m).
Proof.
  eauto using forallprogram_base, ctm_from_norefs_noinits, consistent_term.
Qed.

