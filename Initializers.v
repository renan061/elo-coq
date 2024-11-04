From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import Addresses.
From Elo Require Import Blocks.

(* ------------------------------------------------------------------------- *)
(* no-ref                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive no_ref (ad : addr) : tm -> Prop :=
  | noref_unit  :                 no_ref ad <{unit          }>
  | noref_nat   : forall n,       no_ref ad <{nat n         }>
  | noref_var   : forall x,       no_ref ad <{var x         }>
  | noref_fun   : forall x Tx t,  no_ref ad t  ->
                                  no_ref ad <{fn x Tx t     }>
  | noref_call  : forall t1 t2,   no_ref ad t1 ->
                                  no_ref ad t2 ->
                                  no_ref ad <{call t1 t2    }>
  | noref_ref   : forall ad' T,   ad <> ad'    ->
                                  no_ref ad <{&ad' : T      }>
  | noref_new   : forall t T,     no_ref ad t  ->
                                  no_ref ad <{new t : T     }>
  | noref_init  : forall ad' t T, no_ref ad t  ->
                                  no_ref ad <{init ad' t : T}>
  | noref_load  : forall t,       no_ref ad t  ->
                                  no_ref ad <{*t            }>
  | noref_asg   : forall t1 t2,   no_ref ad t1 ->
                                  no_ref ad t2 ->
                                  no_ref ad <{t1 := t2      }>
  | noref_acq   : forall t1 t2,   no_ref ad t1 ->
                                  no_ref ad t2 ->
                                  no_ref ad <{acq t1 t2     }>
  | noref_cr    : forall ad' t,   no_ref ad t  ->
                                  no_ref ad <{cr ad' t      }>
  | noref_spawn : forall t,       no_ref ad t ->
                                  no_ref ad <{spawn t       }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _noref tt :=
  match goal with
  | H : no_ref _   <{unit        }> |- _ => clear H
  | H : no_ref _   <{nat _       }> |- _ => clear H
  | H : no_ref _   <{var _       }> |- _ => clear H
  | H : no_ref _   <{fn _ _ _    }> |- _ => tt H
  | H : no_ref _   <{call _ _    }> |- _ => tt H
  | H : no_ref ?ad <{& ?ad : _   }> |- _ => invc H; eauto
  | H : no_ref _   <{&_ : _      }> |- _ => tt H
  | H : no_ref _   <{new _ : _   }> |- _ => tt H
  | H : no_ref _   <{init _ _ : _}> |- _ => tt H
  | H : no_ref _   <{* _         }> |- _ => tt H
  | H : no_ref _   <{_ := _      }> |- _ => tt H
  | H : no_ref _   <{acq _ _     }> |- _ => tt H
  | H : no_ref _   <{cr _ _      }> |- _ => tt H
  | H : no_ref _   <{spawn _     }> |- _ => tt H
  end.

Ltac inv_noref  := _noref inv.
Ltac invc_noref := _noref invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma noref_from_vad1 : forall m t,
  valid_addresses m t ->
  no_ref (#m) t.
Proof.
  intros. induction t; invc_vad; constructor; eauto. lia.
Qed.

Lemma noref_from_vad2 : forall ad m t,
  #m < ad ->
  valid_addresses m t ->
  no_ref ad t.
Proof.
  intros. induction t; invc_vad; constructor; eauto. lia.
Qed.

Lemma noref_init_term : forall m t1 t2 ad t,
  no_ref m t1 ->
  t1 --[e_init ad t]--> t2 ->
  no_ref m t.
Proof.
  intros. ind_tstep; invc_noref; eauto.
Qed.

Lemma noref_write_term : forall m t1 t2 ad t,
  no_ref m t1 ->
  t1 --[e_write ad t]--> t2 ->
  no_ref m t.
Proof.
  intros. ind_tstep; invc_noref; eauto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma noref_subst : forall ad x tx t,
  no_ref ad t ->
  no_ref ad tx ->
  no_ref ad <{[x := tx] t}>.
Proof. 
  intros. induction t; invc_noref;
  simpl in *; try destruct str_eq_dec; eauto using no_ref.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_noref_preservation :=
  intros; ind_tstep; repeat invc_noref; eauto using noref_subst, no_ref.

Lemma noref_preservation_none : forall ad t1 t2,
  no_ref ad t1 ->
  t1 --[e_none]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_alloc : forall ad t1 t2 ad' T,
  no_ref ad t1 ->
  t1 --[e_alloc ad' T]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_init : forall ad t1 t2 ad' t,
  ad <> ad' ->
  no_ref ad t1 ->
  t1 --[e_init ad' t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_read : forall ad t1 t2 ad' t,
  no_ref ad t ->
  (* --- *)
  no_ref ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_write : forall ad t1 t2 ad' t,
  no_ref ad t1 ->
  t1 --[e_write ad' t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_acq : forall ad t1 t2 ad' t,
  no_ref ad t ->
  (* --- *)
  no_ref ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_rel : forall ad t1 t2 ad',
  no_ref ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_spawn : forall ad t1 t2 tid t,
  no_ref ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_spawned : forall ad t1 t2 tid t,
  no_ref ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_ref ad t.
Proof. solve_noref_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* consistent-uninitialized-addresses                                        *)
(* ------------------------------------------------------------------------- *)

Definition consistent_uninitialized_addresses (m : mem) (ths : threads) :=
  forall ad, m[ad].t = None -> forall_program m ths (no_ref ad).

(* preservation ------------------------------------------------------------ *)

Local Lemma cua_preservation_none : forall m ths tid t,
  tid < #ths ->
  consistent_uninitialized_addresses m ths ->
  ths[tid] --[e_none]--> t ->
  consistent_uninitialized_addresses m ths[tid <- t].
Proof.
  intros * ? Hcua ? ad Had. specialize (Hcua ad Had) as [? ?].
  split; trivial. intros ?. omicron; eauto using noref_preservation_none.
Qed.

Local Lemma cua_preservation_alloc : forall m ths tid t T,
  forall_program m ths (valid_addresses m) ->
  (* --- *)
  tid < #ths ->
  consistent_uninitialized_addresses m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  consistent_uninitialized_addresses (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros * [? ?] ? Hcua ? ad Had. omicron; split; intros ? **; omicron;
  try specialize (Hcua ad Had) as [? ?];
  eauto using noref_from_vad1, noref_from_vad2, noref_preservation_alloc;
  discriminate.
Qed.

Local Lemma cua_preservation_init : forall m ths tid t ad te,
  forall_program m ths (valid_addresses m) ->
  (* --- *)
  tid < #ths ->
  consistent_uninitialized_addresses m ths ->
  ths[tid] --[e_init ad te]--> t ->
  consistent_uninitialized_addresses m[ad.t <- te] ths[tid <- t].
Proof.
  intros * [? ?] ? Hcua ? ad' Had'.
  assert (ad < #m) by eauto using vad_init_addr.
  repeat omicron; try discriminate.
  destruct (Hcua ad' Had'). split; intros ? **; omicron;
  try invc_eq; eauto using noref_init_term, noref_preservation_init.
Qed.

Local Lemma cua_preservation_read : forall m ths tid t ad te,
  tid < #ths ->
  m[ad].t = Some te ->
  consistent_uninitialized_addresses m ths ->
  ths[tid] --[e_read ad te]--> t ->
  consistent_uninitialized_addresses m ths[tid <- t].
Proof.
  intros * ? ? Hcua ? ad' Had'. destruct (Hcua ad' Had').
  split; trivial. intros ?. omicron; eauto using noref_preservation_read.
Qed.

Local Lemma cua_preservation_write : forall m ths tid t ad te,
  forall_program m ths (valid_addresses m) ->
  (* --- *)
  tid < #ths ->
  consistent_uninitialized_addresses m ths ->
  ths[tid] --[e_write ad te]--> t ->
  consistent_uninitialized_addresses m[ad.t <- te] ths[tid <- t].
Proof.
  intros * [? ?] ? Hcua ? ad' Had'.
  assert (ad < #m) by eauto using vad_write_addr.
  repeat omicron; try discriminate.
  destruct (Hcua ad' Had'). split; intros ? **; omicron;
  try invc_eq; eauto using noref_write_term, noref_preservation_write.
Qed.

Local Lemma cua_preservation_acq : forall m ths tid t ad te,
  tid < #ths ->
  m[ad].t = Some te ->
  consistent_uninitialized_addresses m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  consistent_uninitialized_addresses m[ad.X <- true] ths[tid <- t].
Proof.
  intros * ? ? Hcua ? ad' H.
  assert (Had' : m[ad'].t = None) by (repeat omicron; eauto). clear H.
  destruct (Hcua ad' Had'). split; trivial;
  intros ? **; repeat omicron; eauto using noref_preservation_acq.
Qed.

Local Lemma cua_preservation_rel : forall m ths tid t ad,
  tid < #ths ->
  consistent_uninitialized_addresses m ths ->
  ths[tid] --[e_rel ad]--> t ->
  consistent_uninitialized_addresses m[ad.X <- false] ths[tid <- t].
Proof.
  intros * ? Hcua ? ad' H.
  assert (Had' : m[ad'].t = None) by (repeat omicron; eauto). clear H.
  destruct (Hcua ad' Had'). split; trivial;
  intros ? **; repeat omicron; eauto using noref_preservation_rel;
  discriminate.
Qed.

Local Lemma cua_preservation_spawn : forall m ths tid t te,
  tid < #ths ->
  consistent_uninitialized_addresses m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  consistent_uninitialized_addresses m (ths[tid <- t] +++ te).
Proof.
  intros * ? Hcua ? ad Had. specialize (Hcua ad Had) as [? ?].
  split; trivial. intros ?. omicron; eauto using no_ref;
  eauto using noref_preservation_spawn, noref_preservation_spawned.
Qed.

Theorem cua_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_addresses m1) ->
  (* --- *)
  consistent_uninitialized_addresses m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  consistent_uninitialized_addresses m2 ths2.
Proof.
  intros.
  invc_cstep; try invc_mstep.
  - eauto using cua_preservation_none.
  - eauto using cua_preservation_alloc.
  - eauto using cua_preservation_init.
  - eauto using cua_preservation_read.
  - eauto using cua_preservation_write.
  - eauto using cua_preservation_acq.
  - eauto using cua_preservation_rel.
  - eauto using cua_preservation_spawn.
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

(* preservation ------------------------------------------------------------ *)

Local Lemma oneinit_subst : forall ad x tx t,
  no_init  ad tx -> 
  one_init ad t  ->
  one_init ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_oneinit; eauto using noinit_subst, one_init.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

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

(* P1 holds for one thread. P2 holds for the other threads. *)
Definition forone_thread
  (ths : threads) (P1: tm -> Prop) (P2 : tm -> Prop) : Prop :=
  exists tid, P1 ths[tid] /\ forall tid', tid <> tid' -> P2 ths[tid'].

Definition unique_initializers (m : mem) (ths : threads) := forall ad,
  (m[ad].t <> None -> forall_threads ths (no_init ad)) /\
  (m[ad].t =  None -> forone_thread  ths (one_init ad) (no_init ad)).

(* preservation lemmas ----------------------------------------------------- *)

Local Lemma vad_oneinit_contradiction1 : forall m t,
  valid_addresses m t ->
  one_init (# m) t ->
  False.
Proof.
  intros. induction t; invc_vad; invc_oneinit; eauto.
Qed.

Local Lemma vad_oneinit_contradiction2 : forall ad m t,
  valid_addresses m t ->
  one_init ad t ->
  #m < ad ->
  False.
Proof.
  intros. induction t; invc_vad; invc_oneinit; eauto. lia.
Qed.

Local Lemma noinit_init_contradiction : forall t1 t2 ad t,
  no_init ad t1 ->
  t1 --[e_init ad t]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_noinit; eauto.
Qed.

Local Lemma noinit_to_oneinit : forall t1 t2 ad T,
  no_init ad t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  one_init ad t2.
Proof.
  intros. ind_tstep; invc_noinit; eauto using one_init.
Qed.

Local Lemma oneinit_to_noinit : forall t1 t2 ad t,
  one_init ad t1 ->
  t1 --[e_init ad t]--> t2 ->
  no_init ad t2.
Proof.
  intros. ind_tstep; invc_oneinit; eauto using no_init;
  exfalso; eauto using noinit_init_contradiction.
Qed.

Local Lemma noref_write_contradiction : forall t1 t2 ad t,
  no_ref ad t1 ->
  t1 --[e_write ad t]--> t2 ->
  False.
Proof.
  intros. ind_tstep; repeat invc_noref; eauto.
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
  intros * ? ? Hui ** ad. specialize (Hui ad) as [Hnone Hone].
  split; intros Had **; aspecialize. 
  - intros ?. omicron; eauto using noinit_preservation_none.
  - specialize Hone as [tid' [? ?]]. exists tid'.
    omicron; split; eauto using oneinit_preservation_none; intros. 
    + sigma. eauto.
    + omicron; eauto using noinit_preservation_none.
Qed.

Local Lemma ui_preservation_alloc : forall m ths tid t T,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  unique_initializers (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros * ? ? ? Hui ** ad. specialize (Hui ad) as [Hnone Hone].
  split; intros Had **.
  - intros ?. repeat omicron; eauto; aspecialize. 
    + eapply (noinit_preservation_alloc _ _ _ (#m)); eauto. lia.
    + eauto using noinit_preservation_alloc.  
  - omicron; aspecialize; destruct Hone as [tid' [Hone ?]].
    + exists tid'. split; intros; omicron; eauto.
      * eapply (oneinit_preservation_alloc _ _ _ (#m)); eauto. lia.
      * eapply (noinit_preservation_alloc _ _ _ (#m)); eauto. lia.
    + exfalso. eauto using vad_oneinit_contradiction1.
    + exfalso. eauto using vad_oneinit_contradiction2.
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
  intros * ? ? ? Hui ** ad'. destruct (Hui ad) as [Hnone Hone];
  split; intros Had **.
  - intros tid'. repeat omicron; eauto.
    + destruct (alt_opt_dec m[ad'].t); aspecialize.
      * destruct Hone as [tid [? ?]].
        destruct (nat_eq_dec tid' tid); subst.
        ** eauto using oneinit_to_noinit.
        ** exfalso. eauto using noinit_init_contradiction.
      * exfalso. eauto using noinit_init_contradiction.
    + destruct (alt_opt_dec m[ad'].t); aspecialize.
      * destruct Hone as [tid'' [? ?]].
        destruct (nat_eq_dec tid'' tid); subst.
        ** eauto using oneinit_to_noinit.
        ** exfalso. eauto using noinit_init_contradiction.
      * exfalso. eauto using noinit_init_contradiction.
    + specialize (Hui ad') as [Hnone' Hone']. aspecialize.
      eauto using noinit_preservation_init.
    + specialize (Hui ad') as [Hnone' Hone']. aspecialize.
      eauto using noinit_preservation_init.
  - repeat omicron; try aspecialize.
    + exfalso. eapply Lt.le_lt_or_eq in a as [? | ?]; subst;
      destruct Hone as [tid' [Hone ?]];
      destruct (nat_eq_dec tid' tid);
      eauto using vad_oneinit_contradiction1, vad_oneinit_contradiction2.
    + discriminate.
    + specialize (Hui ad') as [_ Hone']. aspecialize.
      destruct Hone' as [tid' [Hone' Hnone']].
      destruct (nat_eq_dec tid' tid); subst.
      * exists tid. sigma. split.
        ** eauto using oneinit_preservation_init. 
        ** intros. sigma. eauto.
      * exists tid'. sigma. split.
        ** eauto. 
        ** intros tid'' ?. omicron; eauto using noinit_preservation_init.
Qed.

Local Lemma ui_preservation_read : forall m ths tid t ad te,
  no_inits te ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_read ad te]--> t ->
  unique_initializers m ths[tid <- t].
Proof.
  intros * ? ? Hui ** ad'. destruct (Hui ad') as [Hnone Hone];
  split; intros Had **; aspecialize.
  - intros ?. omicron; eauto using noinit_preservation_read.
  - destruct Hone as [tid' [Hone ?]]. exists tid'. split.
    + omicron; eauto using oneinit_preservation_read.
    + intros. omicron; eauto using noinit_preservation_read.
Qed.

Local Lemma ui_preservation_write : forall m ths tid t ad te,
  forall_program m ths (valid_addresses m) ->
  forall_program m ths valid_blocks ->
  consistent_uninitialized_addresses m ths ->
  (* --- *)
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_write ad te]--> t ->
  unique_initializers m[ad.t <- te] ths[tid <- t].
Proof.
  intros * [? ?] [? ?] Hcua ? Hui ** ad'.
  assert (ad < #m) by eauto using vad_write_addr.
  destruct (Hui ad') as [Hnone Hone];
  split; intros Had **; repeat omicron; eauto.
  - destruct (alt_opt_dec m[ad'].t); aspecialize.
    + specialize (Hcua ad'). aspecialize. destruct Hcua.
      exfalso. eauto using noref_write_contradiction.
    + intros ?. omicron; eauto using noinit_preservation_write.
  - aspecialize. intros ?. omicron; eauto using noinit_preservation_write.
  - discriminate.
  - aspecialize. destruct Hone as [tid' [? ?]]. exists tid'. split; intros;
    omicron; eauto using noinit_preservation_write, oneinit_preservation_write.
Qed.

Local Lemma ui_preservation_acq : forall m ths tid ad t te,
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  unique_initializers m[ad.X <- true] ths[tid <- t].
Proof.
Abort.

Local Lemma ucr_preservation_rel : forall m ths tid ad t,
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_rel ad]--> t ->
  unique_initializers m[ad.X <- false] ths[tid <- t].
Proof.
Abort.

Local Lemma ucr_preservation_spawn : forall m ths tid t te,
  tid < #ths ->
  unique_initializers m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  unique_initializers m (ths[tid <- t] +++ te).
Proof.
Abort.

Theorem ui_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 valid_blocks ->
  forall_memory m1 no_inits ->
  (* --- *)
  unique_initializers m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  unique_initializers m2 ths2.
Proof.
  intros. invc_cstep; try invc_mstep;
  eauto using ui_preservation_none; 
  eauto using ui_preservation_alloc; 
  eauto using ui_preservation_init; 
  eauto using ui_preservation_read.
  eauto using ui_preservation_write; 
  eauto using ui_preservation_acq; 
  eauto using ui_preservation_rel;
  eauto using ui_preservation_spawn.
Qed.













Inductive one_init (ad : addr) : tm -> Prop :=
  | oneinit_call1  : forall t1 t2,  one_init ad t1 ->
                                  no_init  ad t2 ->
                                  one_init ad <{call t1 t2}>
  | oneinit_call2  : forall t1 t2,  no_init  ad t1 ->
                                  one_init ad t2 ->
                                  one_init ad <{call t1 t2}>
  | oneinit_new    : forall T t,    one_init ad t  ->
                                  one_init ad <{new t : T }>
  | oneinit_load   : forall t,      one_init ad t  ->
                                  one_init ad <{*t        }>
  | oneinit_asg1   : forall t1 t2,  one_init ad t1 ->
                                  no_init  ad t2 ->
                                  one_init ad <{t1 := t2  }>
  | oneinit_asg2   : forall t1 t2,  no_init  ad t1 ->
                                  one_init ad t2 ->
                                  one_init ad <{t1 := t2  }>
  | oneinit_acq1   : forall t1 t2,  one_init ad t1 ->
                                  no_init  ad t2 ->
                                  one_init ad <{acq t1 t2 }>
  | oneinit_acq2   : forall t1 t2,  no_init  ad t1 ->
                                  one_init ad t2 ->
                                  one_init ad <{acq t1 t2 }>
  | oneinit_cr_eq  : forall t,      no_init  ad t  ->
                                  one_init ad <{cr ad t   }>
  | oneinit_cr_neq : forall ad' t,  ad <> ad'    ->
                                  one_init ad t  ->
                                  one_init ad <{cr ad' t  }>
  .


Inductive valid_init (ad : addr) (m : mem) : tm -> Prop :=
  | vi_unit  :                valid_init m <{unit }> 

  | vi_nat   : forall n,      valid_init m <{nat n}>

  | vi_var   : forall x,      valid_init m <{var x}>

  | vi_fun   : forall x Tx t, valid_inits m t ->
                              valid_inits m <{fn x Tx t}>

  | vi_call  : forall t1 t2,  valid_inits m t1 ->
                              valid_inits m t2 ->
                              valid_inits m <{call t1 t2}> 

  | vi_ref   : forall ad T,   valid_inits m <{&ad : T}>

  | vi_init  : forall ad t T, ad < #m         ->
                              m[ad].t = None  ->
                              valid_inits m t ->
                              valid_inits m <{init ad t : T}> 

  | vi_new   : forall T t,    valid_inits m t ->
                              valid_inits m <{new t : T}> 

  | vi_load  : forall t,      valid_inits m t ->
                              valid_inits m <{*t}> 

  | vi_asg   : forall t1 t2,  valid_inits m t1 ->
                              valid_inits m t2 ->
                              valid_inits m <{t1 := t2}> 

  | vi_acq   : forall t1 t2,  valid_inits m t1 ->
                              valid_inits m t2 ->
                              valid_inits m <{acq t1 t2}>

  | vi_cr    : forall ad t,   valid_inits m t ->
                              valid_inits m <{cr ad t}>

  | vi_spawn : forall t,      valid_inits m t ->
                              valid_inits m <{spawn t}>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vi tt :=
  match goal with
  | H : valid_inits _ <{unit        }> |- _ => clear H
  | H : valid_inits _ <{nat _       }> |- _ => clear H
  | H : valid_inits _ <{var _       }> |- _ => clear H
  | H : valid_inits _ <{fn _ _ _    }> |- _ => tt H
  | H : valid_inits _ <{call _ _    }> |- _ => tt H
  | H : valid_inits _ <{& _ : _     }> |- _ => clear H
  | H : valid_inits _ <{new _ : _   }> |- _ => tt H
  | H : valid_inits _ <{init _ _ : _}> |- _ => tt H
  | H : valid_inits _ <{* _         }> |- _ => tt H
  | H : valid_inits _ <{_ := _      }> |- _ => tt H
  | H : valid_inits _ <{acq _ _     }> |- _ => tt H
  | H : valid_inits _ <{cr _ _      }> |- _ => tt H
  | H : valid_inits _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_vi  := _vi inv.
Ltac invc_vi := _vi invc.

(* preservation ------------------------------------------------------------ *)

Lemma vi_subst : forall m x tx t,
  valid_inits m t ->
  valid_inits m tx ->
  valid_inits m <{[x := tx] t}>.
Proof.
  intros. induction t; invc_vi; simpl;
  try destruct str_eq_dec; eauto using valid_inits.
Qed.

Lemma vi_mem_add : forall m t c,
  valid_inits m t ->
  valid_inits (m +++ c) t.
Proof.
  intros. induction t; invc_vi; constructor; sigma; eauto using valid_inits.
Qed.

Lemma vi_mem_set : forall m t t' ad,
  valid_inits m t' ->
  valid_inits m t  ->
  valid_inits m[ad.t <- t'] t.
Proof.
  intros. induction t; inv_vi; eauto using valid_inits.
  aspecialize.
  constructor; sigma; eauto. omicron; eauto.
Abort.

(* ------------------------------------------------------------------------- *)

Lemma vi_preservation_none : forall m t1 t2,
  valid_inits m t1 ->
  t1 --[e_none]--> t2 ->
  valid_inits m t2.
Proof.
  intros. ind_tstep; repeat invc_vi; eauto using vi_subst, valid_inits.
Qed.

Lemma vi_preservation_alloc : forall m t1 t2 T,
  valid_inits m t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  valid_inits (m +++ (None, T, false)) t2.
Proof.
  intros. ind_tstep; invc_vi;
  constructor; sigma; eauto using vi_mem_add.
Qed.

Lemma vi_preservation_inits : forall m t1 t2 ad t,
  valid_inits m t1 ->
  t1 --[e_init ad t]--> t2 ->
  valid_inits m[ad.t <- t] t2.
Proof.
  intros. ind_tstep; inv_vi;
  constructor; sigma; eauto using vi_mem_add.
  - repeat aspecialize.
    constructor.
Qed.
H4 : ths1 [tid'] --[ e_init ad t0 ]--> t

========================= (1 / 1)

valid_inits 

Theorem vi_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_inits m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (valid_inits m2).
Proof.
  intros * [? ?] ?.
  invc_cstep; try invc_mstep; split; try destruct_forall; trivial.
  - eauto using vi_preservation_none.
  - admit.
  - eauto using vi_preservation_alloc.
  - admit.
  - admit.
  - eauto using vi_preservation_init.
  - eauto using vi_preservation_unt_init.
  - eauto using vi_preservation_read.
  - eauto using vi_preservation_mem_write.
  - eauto using vi_preservation_write.
  - eauto using vi_preservation_unt_write.
  - eauto using vi_preservation_mem_acq.
  - eauto using vi_preservation_acq.
  - eauto using vi_preservation_unt_acq.
  - eauto using vi_preservation_mem_rel.
  - eauto using vi_preservation_rel.
  - eauto using vi_preservation_unt_rel.
  - eauto using vi_preservation_spawn.
  - eauto using vi_preservation_spawned.
  - eauto using valid_inits.
Qed.

