From Elo Require Import Core.

From Elo Require Import WellTypedTerm.

(* ------------------------------------------------------------------------- *)
(* valid-references                                                          *)
(* ------------------------------------------------------------------------- *)

Inductive valid_references (m : mem) : tm -> Prop :=
  | vr_unit  :                valid_references m <{unit }> 
  | vr_nat   : forall n,      valid_references m <{nat n}>
  | vr_var   : forall x,      valid_references m <{var x}>

  | vr_fun   : forall x Tx t, valid_references m t ->
                              valid_references m <{fn x Tx t}>

  | vr_call  : forall t1 t2,  valid_references m t1 ->
                              valid_references m t2 ->
                              valid_references m <{call t1 t2}> 

  | vr_refR  : forall ad t T, ad < #m                 ->
                              m[ad].t = Some t        ->
                              m[ad].T = `r&T`         ->
                              empty |-- t is `Safe T` ->
                              valid_references m <{&ad : r&T}>

  | vr_refX  : forall ad t T, ad < #m          ->
                              m[ad].t = Some t ->
                              m[ad].T = `x&T`  ->
                              empty |-- t is T ->
                              valid_references m <{&ad : x&T}>

  | vr_refW  : forall ad t T, ad < #m          ->
                              m[ad].t = Some t ->
                              m[ad].T = `w&T`  ->
                              empty |-- t is T ->
                              valid_references m <{&ad : w&T}>

  | vr_initR : forall ad t T, ad < #m              ->
                              m[ad].T = `r&T`      ->
                              valid_references m t ->
                              valid_references m <{init ad t : r&T}> 

  | vr_initX : forall ad t T, ad < #m              ->
                              m[ad].T = `x&T`      ->
                              valid_references m t ->
                              valid_references m <{init ad t : x&T}> 

  | vr_initW : forall ad t T, ad < #m              ->
                              m[ad].T = `w&T`      ->
                              valid_references m t ->
                              valid_references m <{init ad t : w&T}> 

  | vr_new   : forall T t,    valid_references m t ->
                              valid_references m <{new t : T}> 

  | vr_load  : forall t,      valid_references m t ->
                              valid_references m <{*t}> 

  | vr_asg   : forall t1 t2,  valid_references m t1 ->
                              valid_references m t2 ->
                              valid_references m <{t1 := t2}> 

  | vr_acq   : forall t1 t2,  valid_references m t1 ->
                              valid_references m t2 ->
                              valid_references m <{acq t1 t2}>

  | vr_cr    : forall ad t,   ad < #m              ->
                              valid_references m t ->
                              valid_references m <{cr ad t}>

  | vr_spawn : forall t,      valid_references m t ->
                              valid_references m <{spawn t}>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vr tt :=
  match goal with
  | H : valid_references _ <{unit        }> |- _ => clear H
  | H : valid_references _ <{nat _       }> |- _ => clear H
  | H : valid_references _ <{var _       }> |- _ => clear H
  | H : valid_references _ <{fn _ _ _    }> |- _ => tt H
  | H : valid_references _ <{call _ _    }> |- _ => tt H
  | H : valid_references _ <{& _ : _     }> |- _ => tt H
  | H : valid_references _ <{new _ : _   }> |- _ => tt H
  | H : valid_references _ <{init _ _ : _}> |- _ => tt H
  | H : valid_references _ <{* _         }> |- _ => tt H
  | H : valid_references _ <{_ := _      }> |- _ => tt H
  | H : valid_references _ <{acq _ _     }> |- _ => tt H
  | H : valid_references _ <{cr _ _      }> |- _ => tt H
  | H : valid_references _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_vr  := _vr inv.
Ltac invc_vr := _vr invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma vr_tstep_init_term : forall m t1 t2 ad t,
  valid_references m t1 ->
  t1 --[e_init ad t]--> t2 ->
  valid_references m t.
Proof.
  intros. ind_tstep; invc_vr; eauto.
Qed.

Lemma vr_tstep_write_term : forall m t1 t2 ad t,
  valid_references m t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_references m t.
Proof.
  intros. ind_tstep; invc_vr; eauto.
Qed.

Lemma vr_tstep_write_addr : forall m t1 t2 ad t,
  valid_references m t1 ->
  t1 --[e_write ad t]--> t2 ->
  ad < #m.
Proof.
  intros. ind_tstep; repeat invc_vr; eauto.
Qed.

Lemma valid_init_effect : forall m t1 t2 ad t,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  t1 --[e_init ad t]--> t2 ->
  (exists T, empty |-- t is `Safe T` /\ m[ad].T = `r&T`) \/
  (exists T, empty |-- t is T        /\ m[ad].T = `x&T`) \/
  (exists T, empty |-- t is T        /\ m[ad].T = `w&T`).
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_vr; eauto.
Qed.

Lemma valid_write_effect : forall m t1 t2 ad t,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  t1 --[e_write ad t]--> t2 ->
  (exists T, empty |-- t is T /\ m[ad].T = `w&T`).
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_vr; eauto.
Qed.

Corollary valid_write_type : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  t1 --[e_write ad t]--> t2 ->
  empty |-- t is T <-> m[ad].T = `w&T`.
Proof.
  intros.
  assert (exists T, empty |-- t is T /\ m[ad].T = `w&T`) as [Te [? ?]]
      by eauto using valid_write_effect.
  split; intros.
  - apply_deterministic_typing. assumption.
  - invc_eq. assumption.
Qed.

(* preservation ------------------------------------------------------------ *)

Lemma vr_subst : forall m t tx x,
  valid_references m tx ->
  valid_references m t ->
  valid_references m <{[x := tx] t}>.
Proof.
  intros.
  induction t; repeat invc_vr; eauto using valid_references;
  simpl; destruct str_eq_dec; eauto using valid_references.
Qed.

Lemma vr_mem_add : forall m t c,
  valid_references m t ->
  valid_references (m +++ c) t.
Proof.
  intros. induction t; try invc_vr; eauto using valid_references;
  try (constructor; sigma; eauto);
  (eapply vr_refR || eapply vr_refX || eapply vr_refW); sigma; eauto.
Qed.

Local Ltac solve_mem_set :=
  intros ? t **; induction t; invc_vr; eauto using valid_references;
  try match goal with H1 : _[?ad1].T = _, H2 : _[?ad2].T = _ |- _ =>
    destruct (nat_eq_dec ad1 ad2); subst; try invc_eq
  end;
  (constructor || eapply vr_refR || eapply vr_refX || eapply vr_refW);
  sigma; eauto.

Lemma vr_mem_setR : forall m t te ad T,
  m[ad].T = `r&T` ->
  empty |-- te is `Safe T` ->
  (* --- *)
  valid_references m t ->
  valid_references m[ad.t <- te] t.
Proof. solve_mem_set. Qed.

Lemma vr_mem_setX : forall m t te ad T,
  m[ad].T = `x&T` ->
  empty |-- te is T ->
  (* --- *)
  valid_references m t ->
  valid_references m[ad.t <- te] t.
Proof. solve_mem_set. Qed.

Lemma vr_mem_setW : forall m t te ad T,
  m[ad].T = `w&T` ->
  empty |-- te is T ->
  (* --- *)
  valid_references m t ->
  valid_references m[ad.t <- te] t.
Proof. solve_mem_set. Qed.

Local Ltac solve_mem_acq_rel :=
  intros ? t **; induction t; try invc_vr; eauto using valid_references;
  (constructor || eapply vr_refR || eapply vr_refX || eapply vr_refW);
  sigma; eauto; omicron; eauto.

Lemma vr_mem_acq : forall m t ad,
  valid_references m t ->
  valid_references m[ad.X <- true] t.
Proof. solve_mem_acq_rel. Qed.

Lemma vr_mem_rel : forall m t ad,
  valid_references m t ->
  valid_references m[ad.X <- false] t.
Proof. solve_mem_acq_rel. Qed.

(* none -------------------------------------------------------------------- *)

Lemma vr_preservation_none : forall m t1 t2,
  valid_references m t1 ->
  t1 --[e_none]--> t2 ->
  valid_references m t2.
Proof.
  intros.
  ind_tstep; inv_vr; eauto using valid_references.
  inv_vr. eauto using vr_subst.
Qed.

(* alloc ------------------------------------------------------------------- *)

Lemma vr_preservation_mem_alloc : forall m t1 t2 T X,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  forall_memory m (valid_references m) ->
  t1 --[e_alloc (#m) T]--> t2 ->
  forall_memory (m +++ (None, T, X)) (valid_references (m +++ (None, T, X))).
Proof.
  intros ** ? ? ?. omicron; eauto using vr_mem_add; discriminate.
Qed.

Lemma vr_preservation_alloc : forall m t1 t2 T X,
  well_typed_term t1 ->
  (* --- *)
  valid_references m t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  valid_references (m +++ (None, T, X)) t2.
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; invc_typeof; invc_vr;
  constructor; sigma; eauto using vr_mem_add.
Qed.

Lemma vr_preservation_unt_alloc : forall m t1 t2 tu ad T X,
  valid_references m tu ->
  t1 --[e_alloc ad T]--> t2 ->
  valid_references (m +++ (None, T, X)) tu.
Proof.
  intros. ind_tstep; eauto using vr_mem_add.
Qed.

(* init -------------------------------------------------------------------- *)

Lemma vr_preservation_mem_init : forall m t1 t2 ad t,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  forall_memory m (valid_references m) ->
  t1 --[e_init ad t]--> t2 ->
  forall_memory m[ad.t <- t] (valid_references m[ad.t <- t]).
Proof.
  intros ** ? ? Had.
  assert (
    (exists T, empty |-- t is `Safe T` /\ m[ad].T = `r&T`) \/
    (exists T, empty |-- t is T        /\ m[ad].T = `x&T`) \/
    (exists T, empty |-- t is T        /\ m[ad].T = `w&T`)
  ) as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]]
    by eauto using valid_init_effect;
  repeat omicron; try discriminate; invc Had;
  eauto using vr_mem_setR, vr_mem_setX, vr_mem_setW, vr_tstep_init_term.
Qed.

Lemma vr_preservation_init : forall m t1 t2 ad t,
  well_typed_term t1 ->
  (* --- *)
  ad < #m ->
  valid_references m t1 ->
  t1 --[e_init ad t]--> t2 ->
  valid_references (m[ad.t <- t]) t2.
Proof.
  intros.
  assert (
    (exists T, empty |-- t is `Safe T` /\ m[ad].T = `r&T`) \/
    (exists T, empty |-- t is T        /\ m[ad].T = `x&T`) \/
    (exists T, empty |-- t is T        /\ m[ad].T = `w&T`)
  ) as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]]
    by eauto using valid_init_effect;
  ind_tstep; invc_wtt; invc_vr;
  eauto using vr_mem_setR, vr_mem_setX, vr_mem_setW, valid_references;
  try solve [constructor; sigma; eauto; omicron; eauto];
  invc_eq; (eapply vr_refR || eapply vr_refX || eapply vr_refW); sigma; eauto.
Qed.

Lemma vr_preservation_unt_init : forall m t1 t2 tu ad t,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  valid_references m tu ->
  t1 --[e_init ad t]--> t2 ->
  valid_references m[ad.t <- t] tu.
Proof.
  intros.
  assert (
    (exists T, empty |-- t is `Safe T` /\ m[ad].T = `r&T`) \/
    (exists T, empty |-- t is T        /\ m[ad].T = `x&T`) \/
    (exists T, empty |-- t is T        /\ m[ad].T = `w&T`)
  ) as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]]
    by eauto using valid_init_effect;
  eauto using vr_mem_setR, vr_mem_setX, vr_mem_setW.
Qed.

(* read -------------------------------------------------------------------- *)

Lemma vr_preservation_read : forall m t1 t2 ad t,
  m[ad].t = Some t ->
  valid_references m t ->
  (* --- *)
  valid_references m t1 ->
  t1 --[e_read ad t]--> t2 ->
  valid_references m t2.
Proof.
  intros. ind_tstep; invc_vr; eauto using valid_references.
Qed.

(* write ------------------------------------------------------------------- *)

Lemma vr_preservation_mem_write : forall m t1 t2 ad t,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (valid_references m) ->
  t1 --[e_write ad t]--> t2 ->
  forall_memory m[ad.t <- t] (valid_references m[ad.t <- t]).
Proof.
  intros ** ? ? Had.
  assert (exists T, empty |-- t is T /\ m[ad].T = `w&T`) as [Te [? ?]]
    by eauto using valid_write_effect.
  omicron; invc Had; eauto using vr_mem_setW, vr_tstep_write_term.
Qed.

Lemma vr_preservation_write : forall m t1 t2 ad t,
  well_typed_term t1 ->
  (* --- *)
  ad < #m ->
  valid_references m t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_references (m[ad.t <- t]) t2.
Proof.
  intros.
  assert (exists T, empty |-- t is T /\ m[ad].T = `w&T`) as [Te [? ?]]
    by eauto using valid_write_effect.
  ind_tstep; invc_wtt; invc_vr;
  eauto using vr_mem_setW, valid_references;
  constructor; sigma; eauto; omicron; eauto.
Qed.

Lemma vr_preservation_unt_write : forall m t1 t2 tu ad t,
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  valid_references m tu ->
  t1 --[e_write ad t]--> t2 ->
  valid_references m[ad.t <- t] tu.
Proof.
  intros.
  assert (exists T, empty |-- t is T /\ m[ad].T = `w&T`) as [Te [? ?]]
    by eauto using valid_write_effect.
  eauto using vr_mem_setW.
Qed.

(* acq --------------------------------------------------------------------- *)

Lemma vr_preservation_mem_acq : forall m t1 t2 ad t,
  forall_memory m well_typed_term ->
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (valid_references m) ->
  t1 --[e_acq ad t]--> t2 ->
  forall_memory m[ad.X <- true] (valid_references m[ad.X <- true]).
Proof.
  intros ** ? ? ?. omicron; eauto using vr_mem_acq.
Qed.

Lemma vr_preservation_acq : forall m t1 t2 ad t,
  m[ad].t = Some t ->
  valid_references m t ->
  (* --- *)
  ad < #m ->
  valid_references m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  valid_references m[ad.X <- true] t2.
Proof.
  intros. ind_tstep; repeat invc_vr;
  eauto using vr_mem_acq, vr_subst, valid_references;
  constructor; sigma; eauto; omicron; eauto.
Qed.

Lemma vr_preservation_unt_acq : forall m t1 t2 tu ad t,
  ad < #m ->
  valid_references m tu ->
  t1 --[e_acq ad t]--> t2 ->
  valid_references m[ad.X <- true] tu.
Proof.
  eauto using vr_mem_acq.
Qed.

(* rel --------------------------------------------------------------------- *)

Lemma vr_preservation_mem_rel : forall m t1 t2 ad,
  forall_memory m well_typed_term ->
  well_typed_term t1 ->
  valid_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (valid_references m) ->
  t1 --[e_rel ad]--> t2 ->
  forall_memory m[ad.X <- false] (valid_references m[ad.X <- false]).
Proof.
  intros ** ? ? ?. omicron; eauto using vr_mem_rel.
Qed.

Lemma vr_preservation_rel : forall m t1 t2 ad,
  ad < #m ->
  valid_references m t1 ->
  t1 --[e_rel ad]--> t2 ->
  valid_references m[ad.X <- false] t2.
Proof.
  intros. ind_tstep; invc_vr; eauto using vr_mem_rel, valid_references;
  constructor; sigma; eauto; omicron; eauto.
Qed.

Lemma vr_preservation_unt_rel : forall m t1 t2 tu ad,
  ad < #m ->
  valid_references m tu ->
  t1 --[e_rel ad]--> t2 ->
  valid_references m[ad.X <- false] tu.
Proof.
  eauto using vr_mem_rel.
Qed.

(* spawn ------------------------------------------------------------------- *)

Lemma vr_preservation_spawn : forall m t1 t2 tid t,
  valid_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_references m t2.
Proof.
  intros. ind_tstep; inv_vr; eauto using valid_references.
Qed.

Lemma vr_preservation_spawned : forall m t1 t2 tid t,
  valid_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_references m t.
Proof.
  intros. ind_tstep; inv_vr; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Ltac destruct_forall := 
  match goal with
  | |- forall_threads _[_ <- _] _          => intros tid'; omicron
  | |- forall_threads (_[_ <- _] +++ _) _  => intros tid'; omicron
  end.

Theorem vr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  (* --- *)
  forall_program m1 ths1 (valid_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (valid_references m2).
Proof.
  intros * [? ?] [? ?] ?.
  invc_cstep; try invc_mstep; split; try destruct_forall; trivial.
  - eauto using vr_preservation_none.
  - eauto using vr_preservation_mem_alloc.
  - eauto using vr_preservation_alloc.
  - eauto using vr_preservation_unt_alloc.
  - eauto using vr_preservation_mem_init.
  - eauto using vr_preservation_init.
  - eauto using vr_preservation_unt_init.
  - eauto using vr_preservation_read.
  - eauto using vr_preservation_mem_write.
  - eauto using vr_preservation_write.
  - eauto using vr_preservation_unt_write.
  - eauto using vr_preservation_mem_acq.
  - eauto using vr_preservation_acq.
  - eauto using vr_preservation_unt_acq.
  - eauto using vr_preservation_mem_rel.
  - eauto using vr_preservation_rel.
  - eauto using vr_preservation_unt_rel.
  - eauto using vr_preservation_spawn.
  - eauto using vr_preservation_spawned.
  - eauto using valid_references.
Qed.

