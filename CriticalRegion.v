From Coq Require Import Lia.

From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-cr & ok-crs                                                            *)
(* ------------------------------------------------------------------------- *)

Inductive no_cr : tm -> Prop :=
  | nocr_unit  :                                        no_cr <{unit      }>
  | nocr_nat   : forall n,                              no_cr <{nat n     }>
  | nocr_var   : forall x,                              no_cr <{var x     }>
  | nocr_fun   : forall x Tx t, no_cr t              -> no_cr <{fn x Tx t }>
  | nocr_call  : forall t1 t2,  no_cr t1 -> no_cr t2 -> no_cr <{call t1 t2}>
  | nocr_ref   : forall ad T,                           no_cr <{&ad : T   }>
  | nocr_new   : forall T t,    no_cr t              -> no_cr <{new t : T }>
  | nocr_load  : forall t,      no_cr t              -> no_cr <{*t        }>
  | nocr_asg   : forall t1 t2,  no_cr t1 -> no_cr t2 -> no_cr <{t1 := t2  }>
  | nocr_acq   : forall t1 t2,  no_cr t1 -> no_cr t2 -> no_cr <{acq t1 t2 }>
  | nocr_spawn : forall t,      no_cr t              -> no_cr <{spawn t   }>
  .

Inductive ok_crs : tm -> Prop :=
  | okcrs_unit  :                                          ok_crs <{unit      }>
  | okcrs_nat   : forall n,                                ok_crs <{nat n     }>
  | okcrs_var   : forall x,                                ok_crs <{var x     }>
  | okcrs_fun   : forall x Tx t, no_cr t                -> ok_crs <{fn x Tx t }>
  | okcrs_call  : forall t1 t2,  ok_crs t1 -> ok_crs t2 -> ok_crs <{call t1 t2}>
  | okcrs_ref   : forall ad T,                             ok_crs <{&ad : T   }>
  | okcrs_new   : forall T t,    ok_crs t               -> ok_crs <{new t : T }>
  | okcrs_load  : forall t,      ok_crs t               -> ok_crs <{*t        }>
  | okcrs_asg   : forall t1 t2,  ok_crs t1 -> ok_crs t2 -> ok_crs <{t1 := t2  }>
  | okcrs_acq   : forall t1 t2,  ok_crs t1 -> ok_crs t2 -> ok_crs <{acq t1 t2 }>
  | okcrs_cr    : forall ad t,   ok_crs t               -> ok_crs <{cr ad t   }>
  | okcrs_spawn : forall t,      no_cr t                -> ok_crs <{spawn t   }>
  .

(* inversions -------------------------------------------------------------- *)

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

Local Ltac _okcrs tt :=
  match goal with
  | H : ok_crs <{unit     }> |- _ => clear H
  | H : ok_crs <{nat _    }> |- _ => clear H
  | H : ok_crs <{var _    }> |- _ => clear H
  | H : ok_crs <{fn _ _ _ }> |- _ => tt H
  | H : ok_crs <{call _ _ }> |- _ => tt H
  | H : ok_crs <{&_ : _   }> |- _ => clear H
  | H : ok_crs <{new _ : _}> |- _ => tt H
  | H : ok_crs <{* _      }> |- _ => tt H
  | H : ok_crs <{_ := _   }> |- _ => tt H
  | H : ok_crs <{acq _ _  }> |- _ => tt H
  | H : ok_crs <{cr _ _   }> |- _ => tt H
  | H : ok_crs <{spawn _  }> |- _ => tt H
  end.

Ltac inv_nocr  := _nocr inv.
Ltac invc_nocr := _nocr invc.

Ltac inv_okcrs  := _okcrs inv.
Ltac invc_okcrs := _okcrs invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma nocr_then_okcrs : forall t,
  no_cr t ->
  ok_crs t.
Proof.
  intros. induction t; try invc_nocr; eauto using ok_crs.
Qed.

Lemma value_then_nocr : forall t,
  value t ->
  ok_crs t ->
  no_cr t.
Proof.
  intros * Hval **. invc Hval; try invc_okcrs; eauto using no_cr.
Qed.

(* preservation (valid-crs) ------------------------------------------------ *)

Local Lemma nocr_subst : forall x tx t,
  no_cr t ->
  no_cr tx ->
  no_cr <{[x := tx] t}>.
Proof.
  intros. induction t; simpl in *; trivial;
  try (destruct str_eq_dec; subst); trivial;
  invc_nocr; eauto using no_cr.
Qed.

Local Lemma okcrs_subst : forall x tx t,
  value tx ->
  no_cr t ->
  ok_crs tx ->
  ok_crs <{[x := tx] t}>.
Proof.
  intros. induction t; simpl in *; invc_nocr;
  try (destruct str_eq_dec); eauto using value_then_nocr, nocr_subst, ok_crs.
Qed.

Local Lemma okcrs_preservation_tm_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_memory m1 ok_crs ->
  (* --- *)
  forall_threads ths1 ok_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 ok_crs.
Proof.
  intros * ? ? H ? tid' **.
  invc_cstep; try invc_mstep; omicron; trivial;
  match goal with | _ : _[?tid] --[_]--> _ |- _ => specialize (H tid) end;
  ind_tstep; repeat invc_okcrs;
  eauto using okcrs_subst, nocr_then_okcrs, ok_crs.
Qed.

Local Lemma okcrs_preservation_mem_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 ok_crs ->
  (* --- *)
  forall_memory m1 ok_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_memory m2 ok_crs.
Proof.
  intros * H ** ?. invc_cstep; try invc_mstep; trivial;
  omicron; eauto using ok_crs;
  specialize (H tid); ind_tstep; invc_okcrs; eauto.
Qed.

Theorem okcrs_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  (* --- *)
  forall_program m1 ths1 ok_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 ok_crs.
Proof.
  intros * ? [? ?] **. split;
  eauto using okcrs_preservation_tm_cstep, okcrs_preservation_mem_cstep.
Qed.

(* ------------------------------------------------------------------------- *)
(* in-cr                                                                     *)
(* ------------------------------------------------------------------------- *)

(* Ignores spawn blocks. *)
Inductive in_cr (ad : addr) : tm -> Prop :=
  | incr_fun   : forall x Tx t, in_cr ad t   -> in_cr ad <{fn x Tx t }>
  | incr_call1 : forall t1 t2,  in_cr ad t1  -> in_cr ad <{call t1 t2}>
  | incr_call2 : forall t1 t2,  in_cr ad t2  -> in_cr ad <{call t1 t2}>
  | incr_new   : forall T t,    in_cr ad t   -> in_cr ad <{new t : T }>
  | incr_load  : forall t,      in_cr ad t   -> in_cr ad <{*t        }>
  | incr_asg1  : forall t1 t2,  in_cr ad t1  -> in_cr ad <{t1 := t2  }>
  | incr_asg2  : forall t1 t2,  in_cr ad t2  -> in_cr ad <{t1 := t2  }>
  | incr_acq1  : forall t1 t2,  in_cr ad t1  -> in_cr ad <{acq t1 t2 }>
  | incr_acq2  : forall t1 t2,  in_cr ad t2  -> in_cr ad <{acq t1 t2 }>
  | incr_eq  : forall t, in_cr ad <{cr ad t}>
  | incr_neq : forall ad' t, ad <> ad' -> in_cr ad t -> in_cr ad <{cr ad' t}>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _incr tt :=
  match goal with
  | H : in_cr _ <{unit     }> |- _ => tt H
  | H : in_cr _ <{nat _    }> |- _ => tt H
  | H : in_cr _ <{var _    }> |- _ => tt H
  | H : in_cr _ <{fn _ _ _ }> |- _ => tt H
  | H : in_cr _ <{call _ _ }> |- _ => tt H
  | H : in_cr _ <{& _ : _  }> |- _ => tt H
  | H : in_cr _ <{new _ : _}> |- _ => tt H
  | H : in_cr _ <{* _      }> |- _ => tt H
  | H : in_cr _ <{_ := _   }> |- _ => tt H
  | H : in_cr _ <{acq _ _  }> |- _ => tt H
  | H : in_cr _ <{cr _ _   }> |- _ => tt H
  | H : in_cr _ <{spawn _  }> |- _ => tt H
  end.

Ltac inv_incr  := _incr inv.
Ltac invc_incr := _incr invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma nocr_then_nincr : forall ad t,
  no_cr t ->
  ~ in_cr ad t.
Proof.
  intros ** ?. induction t; invc_nocr; invc_incr; eauto.
Qed.

Lemma nincr_spawned : forall ad t t1 t2 tid,
  ok_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  ~ in_cr ad t.
Proof.
  intros. ind_tstep; invc_okcrs; eauto using nocr_then_nincr.
Qed.

(* inheritance ------------------------------------------------------------- *)

Local Lemma incr_inheritance_subst : forall ad x Tx t tx,
  in_cr ad <{[x := tx] t}> ->
  in_cr ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. induction t; eauto; simpl in *;
  try (destruct str_eq_dec; subst; eauto using in_cr);
  invc_incr; repeat auto_specialize; repeat invc_incr; eauto using in_cr.
Qed.

Local Lemma incr_inheritance_subst2 : forall ad ad' T x Tx t tx,
  no_cr t ->
  (* --- *)
  ad <> ad' ->
  in_cr ad <{[x := tx] t}> ->
  in_cr ad <{acq (&ad' : T) (fn x Tx t)}>.
Proof.
  intros.
Abort.

Local Lemma incr_inheritance_none : forall t1 t2 ad,
  in_cr ad t2 ->
  t1 --[e_none]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using incr_inheritance_subst, in_cr.
Qed.

Local Lemma incr_inheritance_alloc : forall t1 t2 ad ad' t T,
  in_cr ad t2 ->
  t1 --[e_alloc ad' t T]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using in_cr.
Qed.

Local Lemma incr_inheritance_read : forall t1 t2 ad ad' t,
  value t ->
  ok_crs t ->
  (* --- *)
  in_cr ad t2 ->
  t1 --[e_read ad' t]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using in_cr.
  exfalso. eapply nocr_then_nincr; eauto using value_then_nocr.
Qed.

Local Lemma incr_inheritance_write : forall t1 t2 ad ad' t T,
  in_cr ad t2 ->
  t1 --[e_write ad' t T]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using in_cr.
Qed.

Local Lemma incr_inheritance_acq : forall t1 t2 ad ad' t,
  value t ->
  ok_crs t ->
  ok_crs t1 ->
  (* --- *)
  ad <> ad' ->
  in_cr ad t2 ->
  t1 --[e_acq ad' t]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; repeat invc_okcrs; try invc_incr; eauto using in_cr.
  exfalso. eapply nocr_then_nincr.
  2: eauto. eauto using value_then_nocr, nocr_subst.
Qed.

Local Lemma incr_inheritance_rel : forall t1 t2 ad ad',
  ok_crs t1 ->
  (* --- *)
  in_cr ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; invc_okcrs; try invc_incr; eauto using in_cr.
  exfalso. eapply nocr_then_nincr; eauto using value_then_nocr.
Qed.

Local Lemma incr_inheritance_spawn : forall t1 t2 ad tid t,
  in_cr ad t2 ->
  t1 --[e_spawn tid t]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using in_cr.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma incr_subst : forall t tx ad x,
  in_cr ad t ->
  in_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; eauto; simpl in *;
  try (destruct str_eq_dec; subst); invc_incr; eauto using in_cr.
Qed.

Local Lemma incr_preservation_none : forall t1 t2 ad,
  ok_crs t1 ->
  (* --- *)
  in_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  in_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_okcrs; repeat invc_incr;
  eauto using incr_subst, in_cr.
  match goal with H : in_cr _ _ |- _ => contradict H end.
  eauto using value_then_nocr, nocr_then_nincr.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-in-cr                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_inv_nincr := intros; try split; eauto using in_cr.

Local Lemma inv_nincr_fun : forall ad x Tx t,
  ~ in_cr ad <{fn x Tx t}> -> ~ in_cr ad t.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_call : forall ad t1 t2,
  ~ in_cr ad <{call t1 t2}> -> ~ in_cr ad t1 /\ ~ in_cr ad t2.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_new : forall ad t T,
  ~ in_cr ad <{new t : T}> -> ~ in_cr ad t.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_load : forall ad t,
  ~ in_cr ad <{*t}> -> ~ in_cr ad t.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_asg : forall ad t1 t2,
  ~ in_cr ad <{t1 := t2}> -> ~ in_cr ad t1 /\ ~ in_cr ad t2.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_acq : forall ad t1 t2,
  ~ in_cr ad <{acq t1 t2}> -> ~ in_cr ad t1 /\ ~ in_cr ad t2.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_neq : forall ad ad' t,
  ~ in_cr ad <{cr ad' t}> -> ad <> ad' /\ ~ in_cr ad t.
Proof.
  intros * H. split. intros ?.
  - subst. eauto using in_cr.
  - intros ?. destruct (nat_eq_dec ad ad'); subst; eauto using in_cr.
Qed.

Ltac invc_nincr :=
  match goal with
  | H : ~ in_cr _   <{unit     }> |- _ => clear H
  | H : ~ in_cr _   <{nat _    }> |- _ => clear H
  | H : ~ in_cr _   <{var _    }> |- _ => clear H
  | H : ~ in_cr _   <{fn _ _ _ }> |- _ => eapply inv_nincr_fun    in H
  | H : ~ in_cr _   <{call _ _ }> |- _ => eapply inv_nincr_call   in H as [? ?]
  | H : ~ in_cr _   <{& _ : _  }> |- _ => clear H
  | H : ~ in_cr _   <{new _ : _}> |- _ => eapply inv_nincr_new    in H
  | H : ~ in_cr _   <{* _      }> |- _ => eapply inv_nincr_load   in H
  | H : ~ in_cr _   <{_ := _   }> |- _ => eapply inv_nincr_asg    in H as [? ?]
  | H : ~ in_cr _   <{acq _ _  }> |- _ => eapply inv_nincr_acq    in H as [? ?]
  | H : ~ in_cr ?ad <{cr ?ad _ }> |- _ => contradict H; eauto using in_cr
  | H : ~ in_cr _   <{cr _ _   }> |- _ => eapply inv_nincr_neq    in H as [? ?]
  | H : ~ in_cr _   <{spawn _  }> |- _ => clear H
  end.

(* preservation ------------------------------------------------------------ *)

Local Lemma nincr_subst : forall ad x tx t,
  no_cr t ->
  (* --- *)
  ~ in_cr ad t ->
  ~ in_cr ad tx ->
  ~ in_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_nocr; trivial; simpl in *;
  try (destruct str_eq_dec; subst); eauto using in_cr;
  invc_nincr; repeat auto_specialize; intros ?; invc_incr; eauto.
Qed.

Local Ltac solve_nincr_preservation IH :=
  intros; ind_tstep; repeat invc_okcrs; repeat invc_nincr;
  eauto using nincr_subst, value_then_nocr, nocr_then_nincr;
  intros ?; invc_incr; eauto; repeat auto_specialize; contradict IH; assumption.

Local Lemma nincr_preservation_none : forall t1 t2 ad,
  ok_crs t1 ->
  (* --- *)
  ~ in_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation IHtstep. Qed.

Local Lemma nincr_preservation_alloc : forall t1 t2 ad ad' t T,
  ~ in_cr ad t1 ->
  t1 --[e_alloc ad' t T]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation IHtstep. Qed.

Local Lemma nincr_preservation_read : forall t1 t2 ad ad' t,
  value t ->
  ok_crs t ->
  (* --- *)
  ~ in_cr ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation IHtstep. Qed.

Local Lemma nincr_preservation_write : forall t1 t2 ad ad' t T,
  ~ in_cr ad t1 ->
  t1 --[e_write ad' t T]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation IHtstep. Qed.

Local Lemma nincr_preservation_acq : forall t1 t2 ad ad' t,
  value t ->
  ok_crs t ->
  ok_crs t1 ->
  (* --- *)
  ad <> ad' ->
  ~ in_cr ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  ~ in_cr ad t2.
Proof.
  intros; ind_tstep; repeat invc_okcrs; repeat invc_nincr;
  intros ?; invc_incr; eauto; repeat auto_specialize; eauto.
  (* TODO *)
  contradict H8. eauto using nincr_subst, value_then_nocr, nocr_then_nincr.
Qed.

Local Lemma nincr_preservation_rel : forall t1 t2 ad ad',
  ~ in_cr ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation IHtstep. Qed.

Local Lemma nincr_preservation_spawn : forall t1 t2 ad tid t,
  ~ in_cr ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation IHtstep. Qed.

(* ------------------------------------------------------------------------- *)
(* lock-exclusivity                                                          *)
(* ------------------------------------------------------------------------- *)

Definition locked_cr (m : mem) (t : tm) := forall ad,
  in_cr ad t ->
  m[ad].X = true.

Theorem lcr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_memory m1 ok_crs ->
  forall_threads ths1 ok_crs ->
  (* --- *)
  forall_threads ths1 (locked_cr m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (locked_cr m2).
Proof.
  unfold locked_cr.
  intros ** tid' **. invc_cstep; try invc_mstep.
  - omicron; eauto using incr_inheritance_none.
  - repeat omicron; eauto using incr_inheritance_alloc.
    + specialize (H2 tid' (#m1)). sigma. eauto using incr_inheritance_alloc. 
    + specialize (H2 tid' ad).    sigma. eauto using incr_inheritance_alloc. 
    + specialize (H2 tid' (#m1)). sigma. eauto.
    + specialize (H2 tid' ad).    sigma. eauto.
  - omicron; eauto using incr_inheritance_read.
  - repeat omicron; eauto using incr_inheritance_write.
  - repeat omicron; eauto using incr_inheritance_acq. 
  - repeat omicron; eauto.
    + specialize (H2 tid' ad). clear H2. repeat clean. admit.
    + eauto using incr_inheritance_rel. 
    + admit.
  - omicron; eauto using incr_inheritance_spawn.
    + contradict H4. eauto using nincr_spawned.
    + invc_incr.
Abort.

(* ------------------------------------------------------------------------- *)
(* critical-region-exclusivity                                               *)
(* ------------------------------------------------------------------------- *)

Definition critical_region_exclusivity (ths : threads) := forall ad tid1 tid2,
  tid1 <> tid2 ->
  in_cr ad ths[tid1] ->
  ~ in_cr ad ths[tid2].

(* preservation ------------------------------------------------------------ *)

Local Lemma tstep_length_tid : forall ths tid e t,
  ths[tid] --[e]--> t ->
  tid < #ths.
Proof.
  intros.
  decompose sum (lt_eq_lt_dec tid (#ths)); subst; sigma; eauto; invc_tstep.
Qed.

Local Ltac destruct_cre ths tid tid1 tid2 :=
  assert (Hlt : tid < #ths) by eauto using tstep_length_tid;
  destruct (nat_eq_dec tid tid1), (nat_eq_dec tid tid2); subst;
  try contradiction.

Local Lemma cre_preservation_none : forall t ths tid,
  ok_crs ths[tid] ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_none]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_none, nincr_preservation_none.
Qed.

Local Lemma cre_preservation_alloc : forall t ths tid ad te T,
  critical_region_exclusivity ths ->
  ths[tid] --[e_alloc ad te T]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_alloc, nincr_preservation_alloc.
Qed.

Local Lemma cre_preservation_read : forall t ths tid ad te,
  value te ->
  ok_crs te ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_read ad te]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_read, nincr_preservation_read.
Qed.

Local Lemma cre_preservation_write : forall t ths tid ad te T,
  critical_region_exclusivity ths ->
  ths[tid] --[e_write ad te T]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_write, nincr_preservation_write.
Qed.

Local Lemma cre_preservation_rel : forall t ths tid ad,
  forall_threads ths ok_crs ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_rel ad]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_rel, nincr_preservation_rel.
Qed.

Local Lemma cre_preservation_acq : forall m t ths tid ad te,
  m[ad].X = false ->
  value te ->
  ok_crs te ->
  forall_threads ths ok_crs ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_acq ad te]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros * ? ? ? ? ? ? ad' **.
  destruct_cre ths tid tid1 tid2; sigma; eauto;
  destruct (nat_eq_dec ad' ad); subst;
  eauto using nincr_preservation_acq, incr_inheritance_acq.
  - (*
      - tid1 steps
      - t has CR(ad) after the acq
      - we want to show tid2 does not have it
    *)
    admit.
  - (*
      - tid2 steps
      - tid1 has CR(ad)
      - we want to show t does not have it (after the step)
    *)
    admit.
Abort.

Local Lemma cre_preservation_spawn : forall t ths tid tid' te,
  forall_threads ths ok_crs ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_spawn tid' te]--> t ->
  critical_region_exclusivity (ths[tid <- t] +++ te).
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; repeat omicron;
  eauto; try solve [lia | intros ?; invc_incr];
  eauto using incr_inheritance_spawn, nincr_preservation_spawn, nincr_spawned;
  match goal with
  | H : in_cr _ _ |- _ => contradict H; eauto using nincr_spawned
  end.
Qed.

Theorem cre_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_program m1 ths1 ok_crs ->
  (* --- *)
  critical_region_exclusivity ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  critical_region_exclusivity ths2.
Proof.
  intros * ? [? ?] **. invc_cstep; try invc_mstep;
  eauto using cre_preservation_none,
              cre_preservation_alloc,
              cre_preservation_read,
              cre_preservation_write,
              cre_preservation_rel,
              cre_preservation_spawn.

  intros ad' tid1 tid2 Hneq Hincr.
  omicron; eauto.
  -

  specialize (H2 tid ad). auto_specialize.
Qed.
