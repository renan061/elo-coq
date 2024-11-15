From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import Addresses.
From Elo Require Import Blocks.
From Elo Require Import WellTypedTerm.
From Elo Require Import NoRef.

(* ------------------------------------------------------------------------- *)
(* consistent-uninitialized-addresses                                        *)
(* ------------------------------------------------------------------------- *)

Definition no_uninitialized_references (m : mem) (ths : threads) :=
  forall ad, m[ad].t = None -> forall_program m ths (no_ref ad).

(* lemmas ------------------------------------------------------------------ *)

Lemma write_then_initialized : forall m ths tid t ad te,
  no_uninitialized_references m ths ->
  ths[tid] --[e_write ad te]--> t ->
  m[ad].t <> None.
Proof.
  intros * Hnur ?. specialize (Hnur ad).
  destruct (alt_opt_dec m[ad].t) as [Had | ?]; trivial.
  specialize (Hnur Had) as [? ?].
  exfalso. eauto using noref_write_contradiction.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac simpl_nur :=
  intros ** ? ?;
  try match goal with _ : forall_threads _ (valid_addresses ?m) |- _ =>
    match goal with
    | _ : _ --[e_init  ?ad _]--> _ |- _ => assert (ad < #m)
    | _ : _ --[e_write ?ad _]--> _ |- _ => assert (ad < #m)
    end;
    eauto using vad_init_addr, vad_write_addr
  end;
  upsilon;
  match goal with
  | Hnur : no_uninitialized_references ?m _, Had  : ?m[?ad].t = None |- _ =>
    specialize (Hnur ad Had) as Hnoref; clear Hnur
  end;
  match goal with
  | Hnoref : forall_program _ _ (no_ref _) |- _ =>
    assert (Htemp := Hnoref); specialize Htemp as [Hnoref1 Hnoref2]
  end;
  upsilon.

Lemma nur_preservation_none : forall m ths tid t,
  no_uninitialized_references m ths ->
  ths[tid] --[e_none]--> t ->
  no_uninitialized_references m ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_none.
Qed.

Lemma nur_preservation_alloc : forall m ths tid t T,
  no_uninitialized_references m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  no_uninitialized_references (m +++ (None, T, false)) ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_alloc.
Qed.

Lemma nur_preservation_init : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  no_uninitialized_references m ths ->
  ths[tid] --[e_init ad te]--> t ->
  no_uninitialized_references m[ad.t <- te] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_init_term, noref_preservation_init.
Qed.

Lemma nur_preservation_read : forall m ths tid t ad te,
  m[ad].t = Some te ->
  no_uninitialized_references m ths ->
  ths[tid] --[e_read ad te]--> t ->
  no_uninitialized_references m ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_read.
Qed.

Lemma nur_preservation_write : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  no_uninitialized_references m ths ->
  ths[tid] --[e_write ad te]--> t ->
  no_uninitialized_references m[ad.t <- te] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_write_term, noref_preservation_write.
Qed.

Lemma nur_preservation_acq : forall m ths tid t ad te,
  m[ad].t = Some te ->
  no_uninitialized_references m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  no_uninitialized_references m[ad.X <- true] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_acq.
Qed.

Lemma nur_preservation_rel : forall m ths tid t ad,
  no_uninitialized_references m ths ->
  ths[tid] --[e_rel ad]--> t ->
  no_uninitialized_references m[ad.X <- false] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_preservation_rel.
Qed.

Lemma nur_preservation_spawn : forall m ths tid t te,
  no_uninitialized_references m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  no_uninitialized_references m (ths[tid <- t] +++ te).
Proof.
  simpl_nur. eauto using noref_preservation_spawn, noref_preservation_spawned.
Qed.

Theorem nur_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_addresses m1) ->
  (* --- *)
  no_uninitialized_references m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  no_uninitialized_references m2 ths2.
Proof.
  intros * [_ ?] **. invc_cstep; try invc_mstep.
  - eauto using nur_preservation_none.
  - eauto using nur_preservation_alloc.
  - eauto using nur_preservation_init.
  - eauto using nur_preservation_read.
  - eauto using nur_preservation_write.
  - eauto using nur_preservation_acq.
  - eauto using nur_preservation_rel.
  - eauto using nur_preservation_spawn.
Qed.

(* ------------------------------------------------------------------------- *)
(* one-init                                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive one_init (ad : addr) : tm -> Prop :=
  | oneinit_call1    : forall t1 t2,   one_init ad t1 ->
                                       no_init  ad t2 ->
                                       one_init ad <{call t1 t2    }>
  | oneinit_call2    : forall t1 t2,   no_init  ad t1 ->
                                       one_init ad t2 ->
                                       one_init ad <{call t1 t2    }>
  | oneinit_new      : forall T t,     one_init ad t  ->
                                       one_init ad <{new t : T     }>
  | oneinit_init_eq  : forall t T,     no_init  ad t  ->
                                       one_init ad <{init ad  t : T}>
  | oneinit_init_neq : forall ad' t T, ad <> ad'      ->
                                       one_init ad t  ->
                                       one_init ad <{init ad' t : T}>
  | oneinit_load     : forall t,       one_init ad t  ->
                                       one_init ad <{*t            }>
  | oneinit_asg1     : forall t1 t2,   one_init ad t1 ->
                                       no_init  ad t2 ->
                                       one_init ad <{t1 := t2      }>
  | oneinit_asg2     : forall t1 t2,   no_init  ad t1 ->
                                       one_init ad t2 ->
                                       one_init ad <{t1 := t2      }>
  | oneinit_acq1     : forall t1 t2,   one_init ad t1 ->
                                       no_init  ad t2 ->
                                       one_init ad <{acq t1 t2     }>
  | oneinit_acq2     : forall t1 t2,   no_init  ad t1 ->
                                       one_init ad t2 ->
                                       one_init ad <{acq t1 t2     }>
  | oneinit_cr       : forall ad' t,   one_init ad t  ->
                                       one_init ad <{cr ad' t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _oneinit tt :=
  match goal with
  | H : one_init _ <{unit        }> |- _ => inv H
  | H : one_init _ <{nat _       }> |- _ => inv H
  | H : one_init _ <{var _       }> |- _ => inv H
  | H : one_init _ <{fn _ _ _    }> |- _ => inv H
  | H : one_init _ <{call _ _    }> |- _ => tt H
  | H : one_init _ <{&_ : _      }> |- _ => inv H
  | H : one_init _ <{new _ : _   }> |- _ => tt H
  | H : one_init _ <{init _ _ : _}> |- _ => tt H
  | H : one_init _ <{* _         }> |- _ => tt H
  | H : one_init _ <{_ := _      }> |- _ => tt H
  | H : one_init _ <{acq _ _     }> |- _ => tt H
  | H : one_init _ <{cr _ _      }> |- _ => tt H
  | H : one_init _ <{spawn _     }> |- _ => inv H
  end.

Ltac inv_oneinit  := _oneinit inv.
Ltac invc_oneinit := _oneinit invc.

(* lemmas ------------------------------------------------------------------ *)

Local Lemma noinit_oneinit_contradiction : forall ad t,
  no_init ad t ->
  one_init ad t ->
  False.
Proof.
  intros * H ?. induction t; invc_noinit; invc_oneinit; eauto.
Qed.

Local Corollary noinits_oneinit_contradiction : forall ad t,
  no_inits t ->
  one_init ad t ->
  False.
Proof.
  eauto using noinit_oneinit_contradiction.
Qed.

Lemma noinit_to_oneinit : forall t1 t2 ad T,
  no_init ad t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  one_init ad t2.
Proof.
  intros. ind_tstep; invc_noinit; eauto using one_init.
Qed.

Lemma oneinit_to_noinit : forall t1 t2 ad t,
  one_init ad t1 ->
  t1 --[e_init ad t]--> t2 ->
  no_init ad t2.
Proof.
  intros. ind_tstep; invc_oneinit; eauto using no_init;
  exfalso; eauto using noinit_init_contradiction.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Local Lemma oneinit_subst : forall ad x tx t,
  no_init  ad tx -> 
  one_init ad t  ->
  one_init ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_oneinit; eauto using noinit_subst, one_init.
Qed.

(* inheritance ------------------------------------------------------------- *)

Lemma oneinit_inheritance_none : forall ad t1 t2,
  valid_blocks t1 ->
  (* --- *)
  one_init ad t2 ->
  t1 --[e_none]--> t2 ->
  one_init ad t1.
Proof.
  intros. ind_tstep; repeat invc_vb; try invc_oneinit;
  eauto using noinit_inheritance_none, one_init.
  exfalso. apply (noinit_oneinit_contradiction ad <{[x := tx] t}>);
  auto using noinit_from_value, noinit_subst.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_oneinit_preservation L :=
  intros; ind_tstep; try invc_vb; repeat invc_oneinit;
  eauto using L, one_init;
  exfalso; eauto using noinits_from_value, noinits_oneinit_contradiction.

Local Lemma oneinit_preservation_none : forall ad t1 t2,
  valid_blocks t1 ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_none]--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_none. Qed.

Local Lemma oneinit_preservation_alloc : forall ad t1 t2 ad' T,
  ad <> ad' ->
  one_init ad t1 ->
  t1 --[e_alloc ad' T]--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_alloc. Qed.

Local Lemma oneinit_preservation_init : forall ad t1 t2 ad' t,
  valid_blocks t1 ->
  (* --- *)
  ad <> ad' ->
  one_init ad t1 ->
  t1 --[e_init ad' t]--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_init. Qed.

Local Lemma oneinit_preservation_read : forall ad t1 t2 ad' t,
  no_inits t ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_read. Qed.

Local Lemma oneinit_preservation_write : forall ad t1 t2 ad' t,
  valid_blocks t1 ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_write ad' t]--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_write. Qed.

Local Lemma oneinit_preservation_acq : forall ad t1 t2 ad' t,
  no_inits t ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_acq. Qed.

Local Lemma oneinit_preservation_rel : forall ad t1 t2 ad',
  one_init ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_rel. Qed.

Local Lemma oneinit_preservation_spawn : forall ad t1 t2 tid t,
  valid_blocks t1 ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_spawn. Qed.

(* ------------------------------------------------------------------------- *)
(* unique-initializers                                                       *)
(* ------------------------------------------------------------------------- *)

Definition unique_initializers (m : mem) (ths : threads) := forall ad,
  ad < #m ->
  (m[ad].t <> None -> forall_threads ths (no_init ad)) /\
  (m[ad].t =  None -> forone_thread  ths (one_init ad) (no_init ad)).

(* preservation lemmas ----------------------------------------------------- *)

Lemma vad_noinit_ad : forall m t,
  valid_addresses m t ->
  no_init (#m) t.
Proof.
  intros. induction t; invc_vad; eauto using no_init.
Qed.

Lemma vad_oneinit_ad : forall ad m t,
  valid_addresses m t ->
  one_init ad t ->
  ad < #m.
Proof.
  intros. induction t; invc_vad; invc_oneinit; eauto.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma ui_preservation_none : forall m ths tid t,
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_none]--> t ->
  unique_initializers m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hui ? ad Had. specialize (Hui ad Had) as [Hfall Hfone].
  split; intros; aspecialize.
  - intros ?. omicron; eauto using noinit_preservation_none.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split; intros; omicron;
    eauto using noinit_preservation_none, oneinit_preservation_none.
Qed.

Local Lemma ui_preservation_alloc : forall m ths tid t T,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  unique_initializers (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hui ? ad Had. omicron.
  - specialize (Hui ad) as [Hfall Hfone]; trivial.
    split; intros; upsilon; aspecialize.
    + intros ?. omicron; eauto using noinit_preservation_alloc.
    + specialize Hfone as [tid' [? ?]]. exists tid'.
      assert (ad < #m) by eauto using vad_oneinit_ad.
      split; intros; omicron;
      eauto using noinit_preservation_alloc, oneinit_preservation_alloc.
  - split; intros; upsilon; auto. exists tid. split; intros; sigma;
    eauto using vad_noinit_ad, noinit_to_oneinit.
  - lia.
Qed.

Local Lemma ui_preservation_init : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_init ad te]--> t ->
  unique_initializers m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 2.
  intros ? Hui ? ad' Had'. sigma. specialize (Hui ad' Had') as [Hfall Hfone].
  assert (ad < #m) by eauto using vad_init_addr.
  destruct (alt_opt_dec m[ad'].t); aspecialize; split; intros.
  - specialize Hfone as [tid'' [? ?]].
    intros tid'. repeat omicron;
    destruct (nat_eq_dec tid'' tid'); subst;
    eauto using oneinit_to_noinit;
    exfalso; eauto using noinit_init_contradiction.
  - specialize Hfone as [tid'' [? ?]].
    repeat omicron; try discriminate.
    exists tid''. split; intros; omicron;
    eauto using noinit_preservation_init, oneinit_preservation_init.
  - intros tid'. repeat omicron; eauto using noinit_preservation_init.
    exfalso. eauto using noinit_init_contradiction.
  - omicron; eauto. discriminate.
Qed.

Local Lemma ui_preservation_read : forall m ths tid t ad te,
  no_inits te ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_read ad te]--> t ->
  unique_initializers m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hui ? ad' Had'. specialize (Hui ad' Had') as [Hfall Hfone].
  split; intros; upsilon; aspecialize.
  - intros ?. omicron; eauto using noinit_preservation_read.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using noinit_preservation_read, oneinit_preservation_read.
Qed.

Local Lemma ui_preservation_write : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  no_uninitialized_references m ths ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_write ad te]--> t ->
  unique_initializers m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 2. intros Hnur.
  intros ? Hui ? ad' Had'. sigma. specialize (Hui ad' Had') as [Hfall Hfone].
  assert (ad < #m) by eauto using vad_write_addr.
  split; intros; repeat omicron; try discriminate; try aspecialize.
  - destruct (alt_opt_dec m[ad'].t) as [Hmad' | Hmad']; aspecialize.
    + destruct (Hnur ad' Hmad').
      exfalso. eauto using noref_write_contradiction.
    + intros ?. omicron; eauto using noinit_preservation_write.
  - intros ?. omicron; eauto using noinit_preservation_write.
  - specialize Hfone as [tid' [? ?]]. exists tid'; split; intros;
    omicron; eauto using noinit_preservation_write, oneinit_preservation_write.
Qed.

Local Lemma ui_preservation_acq : forall m ths tid ad t te,
  no_inits te ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  unique_initializers m[ad.X <- true] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hui ? ad' Had'. sigma. specialize (Hui ad' Had') as [Hfall Hfone].
  split; intros; upsilon; aspecialize.
  - intros ?. omicron; eauto using noinit_preservation_acq.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using noinit_preservation_acq, oneinit_preservation_acq.
Qed.

Local Lemma ui_preservation_rel : forall m ths tid ad t,
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_rel ad]--> t ->
  unique_initializers m[ad.X <- false] ths[tid <- t].
Proof.
  intros *.
  intros ? Hui ? ad' Had'. sigma. specialize (Hui ad' Had') as [Hfall Hfone].
  split; intros; upsilon; aspecialize.
  - intros ?. omicron; eauto using noinit_preservation_rel.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using noinit_preservation_rel, oneinit_preservation_rel.
Qed.

Local Lemma ui_preservation_spawn : forall m ths tid t te,
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  unique_initializers m (ths[tid <- t] +++ te).
Proof.
  intros until 1.
  intros ? Hui ? ad' Had'. specialize (Hui ad' Had') as [Hfall Hfone].
  split; intros; upsilon; aspecialize.
  - intros ?. omicron; try constructor;
    eauto using noinit_preservation_spawn, noinit_preservation_spawned.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron; try constructor;
    eauto using noinit_preservation_spawn, oneinit_preservation_spawn.
    + invc_oneinit.
    + eauto using noinit_spawn_term.
Qed.

Theorem ui_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_inits ->
  forall_program m1 ths1 (valid_addresses m1) ->
  forall_program m1 ths1 valid_blocks ->
  no_uninitialized_references m1 ths1 ->
  (* --- *)
  unique_initializers m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  unique_initializers m2 ths2.
Proof.
  intros * ? [? ?] [? ?] ? **. invc_cstep; try invc_mstep.
  - eauto using ui_preservation_none.
  - eauto using ui_preservation_alloc.
  - eauto using ui_preservation_init.
  - eauto using ui_preservation_read.
  - eauto using ui_preservation_write.
  - eauto using ui_preservation_acq.
  - eauto using ui_preservation_rel.
  - eauto using ui_preservation_spawn.
Qed.

(* ------------------------------------------------------------------------- *)
(* consistent-inits                                                          *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_inits (m : mem) : tm -> Prop :=
  | ci_unit  :                consistent_inits m <{unit         }> 
  | ci_nat   : forall n,      consistent_inits m <{nat n        }>
  | ci_var   : forall x,      consistent_inits m <{var x        }>
  | ci_fun   : forall x Tx t, consistent_inits m t  ->
                              consistent_inits m <{fn x Tx t    }>
  | ci_call  : forall t1 t2,  consistent_inits m t1 ->
                              consistent_inits m t2 ->
                              consistent_inits m <{call t1 t2   }> 
  | ci_ref   : forall ad T,   consistent_inits m <{&ad : T      }>

  | ci_initR : forall ad t T, m[ad].t = None        ->
                              m[ad].T = `r&T`       ->
                              consistent_inits m t  ->
                              consistent_inits m <{init ad t : r&T}> 

  | ci_initX : forall ad t T, m[ad].t = None        ->
                              m[ad].T = `x&T`       ->
                              consistent_inits m t  ->
                              consistent_inits m <{init ad t : x&T}> 

  | ci_initW : forall ad t T, m[ad].t = None        ->
                              m[ad].T = `w&T`       ->
                              consistent_inits m t  ->
                              consistent_inits m <{init ad t : w&T}> 

  | ci_new   : forall T t,    consistent_inits m t  ->
                              consistent_inits m <{new t : T    }> 
  | ci_load  : forall t,      consistent_inits m t  ->
                              consistent_inits m <{*t           }> 
  | ci_asg   : forall t1 t2,  consistent_inits m t1 ->
                              consistent_inits m t2 ->
                              consistent_inits m <{t1 := t2     }> 
  | ci_acq   : forall t1 t2,  consistent_inits m t1 ->
                              consistent_inits m t2 ->
                              consistent_inits m <{acq t1 t2    }>
  | ci_cr    : forall ad t,   consistent_inits m t  ->
                              consistent_inits m <{cr ad t      }>
  | ci_spawn : forall t,      consistent_inits m t  ->
                              consistent_inits m <{spawn t      }>
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
  | H : consistent_inits _ <{acq _ _     }> |- _ => tt H
  | H : consistent_inits _ <{cr _ _      }> |- _ => tt H
  | H : consistent_inits _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_ci  := _ci inv.
Ltac invc_ci := _ci invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma ci_from_noinits : forall m t,
  no_inits t ->
  consistent_inits m t.
Proof.
  intros. induction t; invc_noinits; eauto using consistent_inits.
Qed.

Lemma ci_init_address : forall m t1 t2 ad t,
  consistent_inits m t1 ->
  t1 --[e_init ad t]--> t2 ->
  m[ad].t = None.
Proof.
  intros. ind_tstep; invc_ci; eauto.
Qed.

Lemma ci_init_term : forall m t1 t2 ad t,
  consistent_inits m t1 ->
  t1 --[e_init ad t]--> t2 ->
  consistent_inits m t.
Proof.
  intros. ind_tstep; invc_ci; eauto.
Qed.

Lemma ci_write_term : forall m t1 t2 ad t,
  consistent_inits m t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_inits m t.
Proof.
  intros. ind_tstep; invc_ci; eauto.
Qed.

Local Corollary oneinit_from_ui : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  unique_initializers m ths ->
  ths[tid] --[e_init ad te]--> t ->
  one_init ad ths[tid].
Proof.
  intros * ? Hui ?.
  assert (Had : ad < #m) by eauto using vad_init_addr.
  specialize (Hui ad Had) as [Hfall Hfone].
  destruct (alt_opt_dec m[ad].t); aspecialize.
  - specialize Hfone as [tid' [? ?]].
    destruct (nat_eq_dec tid' tid); subst; trivial.
    exfalso. eauto using noinit_init_contradiction.
  - exfalso. eauto using noinit_init_contradiction.
Qed.

Local Corollary noinit_from_ui : forall m ths tid1 tid2 ad,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  tid1 <> tid2 ->
  unique_initializers m ths ->
  one_init ad ths[tid1] ->
  no_init ad ths[tid2].
Proof.
  intros * ? ? Hui **.
  assert (Had : ad < #m) by eauto using vad_oneinit_ad.
  specialize (Hui ad Had) as [Hfall Hfone].
  destruct (alt_opt_dec m[ad].t); aspecialize.
  - specialize Hfone as [tid' [? ?]].
    destruct (nat_eq_dec tid1 tid'); subst;
    eauto using noinit_oneinit_contradiction.
  - eauto using noinit_oneinit_contradiction.
Qed.

(* preservation ------------------------------------------------------------ *)

Lemma ci_subst : forall m x tx t,
  consistent_inits m t ->
  consistent_inits m tx ->
  consistent_inits m <{[x := tx] t}>.
Proof.
  intros. induction t; invc_ci; simpl;
  try destruct str_eq_dec; eauto using consistent_inits.
Qed.

Lemma ci_mem_add : forall m t c,
  valid_addresses m t ->
  (* --- *)
  consistent_inits m t ->
  consistent_inits (m +++ c) t.
Proof.
  intros. induction t; invc_vad; invc_ci;
  constructor; sigma; eauto using consistent_inits.
Qed.

Lemma ci_mem_set1 : forall m t t' ad,
  no_init ad t ->
  (* --- *)
  consistent_inits m t' ->
  consistent_inits m t  ->
  consistent_inits m[ad.t <- t'] t.
Proof.
  intros. induction t; invc_noinit; invc_ci;
  constructor; sigma; eauto.
Qed.

Lemma ci_mem_set2 : forall m t t' ad,
  no_inits t ->
  no_inits t' ->
  consistent_inits m[ad.t <- t'] t.
Proof.
  intros. induction t; invc_noinits; eauto using consistent_inits.
Qed.

Lemma ci_mem_acq : forall m t ad,
  consistent_inits m t ->
  consistent_inits m[ad.X <- true] t.
Proof.
  intros. induction t; invc_ci; constructor; upsilon; eauto.
Qed.

Lemma ci_mem_rel : forall m t ad,
  consistent_inits m t ->
  consistent_inits m[ad.X <- false] t.
Proof.
  intros. induction t; invc_ci; constructor; upsilon; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ci_preservation_none : forall m t1 t2,
  consistent_inits m t1 ->
  t1 --[e_none]--> t2 ->
  consistent_inits m t2.
Proof.
  intros. ind_tstep; repeat invc_ci; eauto using ci_subst, consistent_inits.
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

Lemma ci_preservation_init : forall m t1 t2 ad t,
  one_init ad t1 ->
  (* --- *)
  consistent_inits m t1 ->
  t1 --[e_init ad t]--> t2 ->
  consistent_inits m[ad.t <- t] t2.
Proof.
  intros. assert (consistent_inits m t) by eauto using ci_init_term.
  ind_tstep; invc_oneinit; invc_ci;
  constructor; sigma; eauto using ci_mem_set1;
  exfalso; eauto using noinit_init_contradiction.
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

Theorem ci_preservation_ths : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_addresses m1) ->
  forall_program m1 ths1 valid_blocks ->
  forall_program m1 ths1 well_typed_term ->
  no_uninitialized_references m1 ths1 ->
  unique_initializers m1 ths1 ->
  (* --- *)
  forall_program m1 ths1 (consistent_inits m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (consistent_inits m2).
Proof.
  intros * [? ?] [? ?] [? ?] ? Hui [? ?] ?.
  invc_cstep; try invc_mstep; upsilon; intros.
  - eauto using ci_preservation_none.
  - eauto using ci_preservation_alloc.
  - eauto using ci_mem_add.
  - assert (one_init ad ths1[tid]) by eauto using oneinit_from_ui.
    eauto using ci_preservation_init.
  - assert (one_init ad ths1[tid] ) by eauto using oneinit_from_ui.
    assert (no_init  ad ths1[tid']) by eauto using noinit_from_ui.
    eapply ci_mem_set1; eauto using ci_from_noinits,
      vb_init_term, value_init_term, noinits_from_value.
  - eauto using ci_preservation_read.
  - assert (m1[ad].t <> None) by eauto using write_then_initialized. 
    specialize (Hui ad) as [Hnoinit _]; trivial. aspecialize.
    eauto using ci_preservation_write.
  - assert (m1[ad].t <> None) by eauto using write_then_initialized. 
    specialize (Hui ad) as [Hnoinit _]; trivial. aspecialize.
    eauto using ci_write_term, ci_mem_set1.
  - eauto using ci_preservation_acq.
  - eauto using ci_mem_acq.
  - eauto using ci_preservation_rel.
  - eauto using ci_mem_rel.
  - eauto using ci_preservation_spawn.
  - eauto using ci_preservation_spawned.
Qed.

Corollary ci_preservation_mem : forall m1 m2 ths1 ths2 tid e,
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
  intros until 6. intros Hci **. split;
  eauto using ci_preservation_mem, ci_preservation_ths.
Qed.

