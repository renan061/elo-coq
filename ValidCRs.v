From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-cr & valid-crs                                                         *)
(* ------------------------------------------------------------------------- *)

Inductive no_cr : tm -> Prop :=
  | nocr_unit  :                                        no_cr <{unit      }>
  | nocr_nat   : forall n,                              no_cr <{nat n     }>
  | nocr_var   : forall x,                              no_cr <{var x     }>
  | nocr_fun   : forall x Tx t, no_cr t  ->             no_cr <{fn x Tx t }>
  | nocr_call  : forall t1 t2,  no_cr t1 -> no_cr t2 -> no_cr <{call t1 t2}>
  | nocr_ref   : forall ad T,                           no_cr <{&ad : T   }>
  | nocr_new   : forall T t,    no_cr t  ->             no_cr <{new t : T }>
  | nocr_load  : forall t,      no_cr t  ->             no_cr <{*t        }>
  | nocr_asg   : forall t1 t2,  no_cr t1 -> no_cr t2 -> no_cr <{t1 := t2  }>
  | nocr_acq   : forall t1 t2,  no_cr t1 -> no_cr t2 -> no_cr <{acq t1 t2 }>
  | nocr_spawn : forall t,      no_cr t  ->             no_cr <{spawn t   }>
  .

Reserved Notation "'vcrs' t" (at level 60).

Inductive valid_crs : tm -> Prop :=
  | vcrs_unit  :                                      vcrs <{unit      }>
  | vcrs_nat   : forall n,                            vcrs <{nat n     }>
  | vcrs_var   : forall x,                            vcrs <{var x     }>
  | vcrs_fun   : forall x Tx t, no_cr t ->            vcrs <{fn x Tx t }>
  | vcrs_call  : forall t1 t2,  vcrs t1 -> vcrs t2 -> vcrs <{call t1 t2}>
  | vcrs_ref   : forall ad T,                         vcrs <{&ad : T   }>
  | vcrs_new   : forall T t,    vcrs t  ->            vcrs <{new t : T }>
  | vcrs_load  : forall t,      vcrs t  ->            vcrs <{*t        }>
  | vcrs_asg   : forall t1 t2,  vcrs t1 -> vcrs t2 -> vcrs <{t1 := t2  }>
  | vcrs_acq   : forall t1 t2,  vcrs t1 -> vcrs t2 -> vcrs <{acq t1 t2 }>
  | vcrs_cr    : forall ad t,   vcrs t  ->            vcrs <{cr ad t   }>
  | vcrs_spawn : forall t,      no_cr t ->            vcrs <{spawn t   }>

  where "'vcrs' t" := (valid_crs t).

(* ------------------------------------------------------------------------- *)
(* inversions                                                                *)
(* ------------------------------------------------------------------------- *)

Local Ltac _nocr tt :=
  match goal with
  | H : no_cr <{unit     }> |- _ => clear H
  | H : no_cr <{nat _    }> |- _ => clear H
  | H : no_cr <{var _    }> |- _ => clear H
  | H : no_cr <{fn _ _ _ }> |- _ => tt H
  | H : no_cr <{call _ _ }> |- _ => tt H
  | H : no_cr <{&_ : _   }> |- _ => clear H
  | H : no_cr <{new _ : _}> |- _ => tt H
  | H : no_cr <{* _      }> |- _ => tt H
  | H : no_cr <{_ := _   }> |- _ => tt H
  | H : no_cr <{acq _ _  }> |- _ => tt H
  | H : no_cr <{cr _ _   }> |- _ => tt H
  | H : no_cr <{spawn _  }> |- _ => tt H
  end.

Local Ltac _vcrs tt :=
  match goal with
  | H : vcrs <{unit     }> |- _ => clear H
  | H : vcrs <{nat _    }> |- _ => clear H
  | H : vcrs <{var _    }> |- _ => clear H
  | H : vcrs <{fn _ _ _ }> |- _ => tt H
  | H : vcrs <{call _ _ }> |- _ => tt H
  | H : vcrs <{&_ : _   }> |- _ => clear H
  | H : vcrs <{new _ : _}> |- _ => tt H
  | H : vcrs <{* _      }> |- _ => tt H
  | H : vcrs <{_ := _   }> |- _ => tt H
  | H : vcrs <{acq _ _  }> |- _ => tt H
  | H : vcrs <{cr _ _   }> |- _ => tt H
  | H : vcrs <{spawn _  }> |- _ => tt H
  end.

Ltac inv_nocr  := _nocr inv.
Ltac invc_nocr := _nocr invc.

Ltac inv_vcrs  := _vcrs inv.
Ltac invc_vcrs := _vcrs invc.

(* ------------------------------------------------------------------------- *)
(* simple lemmas                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma nocr_then_vcrs : forall t,
  no_cr t ->
  valid_crs t.
Proof.
  intros. induction t; try invc_nocr; eauto using valid_crs.
Qed.

Lemma vcrs_then_nocr : forall t,
  value t ->
  valid_crs t ->
  no_cr t.
Proof.
  intros * Hval **. invc Hval; try invc_vcrs; eauto using no_cr.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation -- valid-crs                                                 *)
(* ------------------------------------------------------------------------- *)

Local Lemma nocr_subst : forall x tx t,
  no_cr t ->
  no_cr tx ->
  no_cr <{[x := tx] t}>.
Proof.
  intros. induction t; simpl in *; trivial;
  try (destruct str_eq_dec; subst); trivial;
  invc_nocr; eauto using no_cr.
Qed.

Local Lemma vcrs_subst : forall x tx t,
  value tx ->
  no_cr t ->
  valid_crs tx ->
  valid_crs <{[x := tx] t}>.
Proof.
  intros. induction t; simpl in *; invc_nocr;
  try (destruct str_eq_dec);
  eauto using vcrs_then_nocr, nocr_subst, valid_crs.
Qed.

Local Lemma vcrs_preservation_none : forall t1 t2,
  valid_crs t1 ->
  t1 --[e_none]--> t2 ->
  valid_crs t2.
Proof.
  intros. ind_tstep; repeat invc_vcrs; eauto using vcrs_subst, valid_crs.
Qed.

Local Lemma vcrs_preservation_alloc : forall t1 t2 ad t T,
  valid_crs t1 ->
  t1 --[e_alloc ad t T]--> t2 ->
  valid_crs t2.
Proof.
  intros. ind_tstep; invc_vcrs; eauto using valid_crs.
Qed.

Local Lemma vcrs_preservation_read : forall t1 t2 ad t,
  valid_crs t ->
  (* --- *)
  valid_crs t1 ->
  t1 --[e_read ad t]--> t2 ->
  valid_crs t2.
Proof.
  intros. ind_tstep; invc_vcrs; eauto using valid_crs.
Qed.

Local Lemma vcrs_preservation_write : forall t1 t2 ad t T,
  valid_crs t1 ->
  t1 --[e_write ad t T]--> t2 ->
  valid_crs t2.
Proof.
  intros. ind_tstep; invc_vcrs; eauto using valid_crs.
Qed.

Local Lemma vcrs_preservation_acq : forall t1 t2 ad t,
  value t ->
  valid_crs t ->
  (* --- *)
  valid_crs t1 ->
  t1 --[e_acq ad t]--> t2 ->
  valid_crs t2.
Proof.
  intros. ind_tstep; repeat invc_vcrs; eauto using vcrs_subst, valid_crs.
Qed.

Local Lemma vcrs_preservation_rel : forall t1 t2 ad,
  valid_crs t1 ->
  t1 --[e_rel ad]--> t2 ->
  valid_crs t2.
Proof.
  intros. ind_tstep; invc_vcrs; eauto using valid_crs.
Qed.

Local Lemma vcrs_preservation_spawn : forall t1 t2 tid t,
  valid_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_crs t2.
Proof.
  intros. ind_tstep; invc_vcrs; eauto using valid_crs.
Qed.

Local Lemma vcrs_preservation_spawned : forall t1 t2 tid t,
  valid_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_crs t.
Proof.
  intros. ind_tstep; invc_vcrs; eauto using nocr_then_vcrs, valid_crs.
Qed.

Local Lemma vcrs_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_memory m1 valid_crs ->
  (* --- *)
  forall_threads ths1 valid_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 valid_crs.
Proof.
  intros. invc_cstep; try invc_mstep; intros tid'; omicron; trivial.
  - eauto using vcrs_preservation_none. 
  - eauto using vcrs_preservation_alloc. 
  - eauto using vcrs_preservation_read. 
  - eauto using vcrs_preservation_write. 
  - eauto using vcrs_preservation_acq. 
  - eauto using vcrs_preservation_rel. 
  - eauto using vcrs_preservation_spawn. 
  - eauto using vcrs_preservation_spawned. 
  - eauto using valid_crs.
Qed.
