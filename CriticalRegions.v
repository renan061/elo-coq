From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import Addresses.
From Elo Require Import Blocks.

(* ------------------------------------------------------------------------- *)
(* one-cr                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive one_cr (ad : addr) : tm -> Prop :=
  | onecr_call1  : forall t1 t2,   one_cr ad t1 ->
                                   no_cr  ad t2 ->
                                   one_cr ad <{call t1 t2    }>
  | onecr_call2  : forall t1 t2,   no_cr  ad t1 ->
                                   one_cr ad t2 ->
                                   one_cr ad <{call t1 t2    }>
  | onecr_new    : forall t T,     one_cr ad t  ->
                                   one_cr ad <{new t : T     }>
  | onecr_init   : forall ad' t T, one_cr ad t  ->
                                   one_cr ad <{init ad' t : T}>
  | onecr_load   : forall t,       one_cr ad t  ->
                                   one_cr ad <{*t            }>
  | onecr_asg1   : forall t1 t2,   one_cr ad t1 ->
                                   no_cr  ad t2 ->
                                   one_cr ad <{t1 := t2      }>
  | onecr_asg2   : forall t1 t2,   no_cr  ad t1 ->
                                   one_cr ad t2 ->
                                   one_cr ad <{t1 := t2      }>
  | onecr_acq1   : forall t1 t2,   one_cr ad t1 ->
                                   no_cr  ad t2 ->
                                   one_cr ad <{acq t1 t2     }>
  | onecr_acq2   : forall t1 t2,   no_cr  ad t1 ->
                                   one_cr ad t2 ->
                                   one_cr ad <{acq t1 t2     }>
  | onecr_cr_eq  : forall t,       no_cr  ad t  ->
                                   one_cr ad <{cr ad t       }>
  | onecr_cr_neq : forall ad' t,   ad <> ad'    ->
                                   one_cr ad t  ->
                                   one_cr ad <{cr ad' t      }>
  .

(* inversion -- one-cr ----------------------------------------------------- *)

Local Ltac _onecr tt :=
  match goal with
  | H : one_cr _ <{unit        }> |- _ => inv H
  | H : one_cr _ <{nat _       }> |- _ => inv H
  | H : one_cr _ <{var _       }> |- _ => inv H
  | H : one_cr _ <{fn _ _ _    }> |- _ => inv H
  | H : one_cr _ <{call _ _    }> |- _ => tt H
  | H : one_cr _ <{&_ : _      }> |- _ => inv H
  | H : one_cr _ <{new _ : _   }> |- _ => tt H
  | H : one_cr _ <{init _ _ : _}> |- _ => tt H
  | H : one_cr _ <{* _         }> |- _ => tt H
  | H : one_cr _ <{_ := _      }> |- _ => tt H
  | H : one_cr _ <{acq _ _     }> |- _ => tt H
  | H : one_cr _ <{cr _ _      }> |- _ => tt H
  | H : one_cr _ <{spawn _     }> |- _ => inv H
  end.

Ltac inv_onecr  := _onecr inv.
Ltac invc_onecr := _onecr invc.

(* lemmas -- one-cr -------------------------------------------------------- *)

Local Lemma nocrs_onecr_contradiction : forall ad t,
  no_crs t ->
  one_cr ad t ->
  False.
Proof.
  intros * H ?. specialize (H ad).
  induction t; invc_nocr; invc_onecr; auto.
Qed.

Local Lemma nocr_to_onecr : forall t1 t2 ad t,
  no_crs t ->
  (* --- *)
  no_cr ad t1 ->
  t1 --[e_acq ad t]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_nocr; eauto using one_cr, nocr_subst.
Qed.

Local Lemma onecr_to_nocr : forall t1 t2 ad,
  one_cr ad t1 ->
  t1 --[e_rel ad]--> t2 ->
  no_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_onecr; eauto using no_cr;
  exfalso; eauto using nocr_rel_contradiction.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Local Lemma onecr_subst : forall ad x tx t,
  no_cr  ad tx -> 
  one_cr ad t  ->
  one_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_onecr; eauto using nocr_subst, one_cr; simpl in *;
  destruct str_eq_dec; subst; eauto using one_cr.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_onecr_preservation L :=
  intros; ind_tstep; try invc_vb; repeat invc_onecr;
  eauto using L, one_cr;
  exfalso; eauto using nocrs_from_value, nocrs_onecr_contradiction.

Local Lemma onecr_preservation_none : forall t1 t2 ad,
  valid_blocks t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_none. Qed.

Local Lemma onecr_preservation_alloc : forall t1 t2 ad ad' T,
  one_cr ad t1 ->
  t1 --[e_alloc ad' T]--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_alloc. Qed.

Local Lemma onecr_preservation_init : forall t1 t2 ad ad' t,
  valid_blocks t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_init ad' t]--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_init. Qed.

Local Lemma onecr_preservation_read : forall t1 t2 ad ad' t,
  no_crs t ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_read. Qed.

Local Lemma onecr_preservation_write : forall t1 t2 ad ad' t,
  valid_blocks t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_write ad' t]--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_write. Qed.

Local Lemma onecr_preservation_acq : forall t1 t2 ad ad' t,
  no_cr ad t ->
  (* --- *)
  ad <> ad' ->
  one_cr ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_acq. Qed.

Local Lemma onecr_preservation_rel : forall t1 t2 ad ad',
  ad <> ad' ->
  one_cr ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_rel. Qed.

Local Lemma onecr_preservation_spawn : forall ad t1 t2 tid t,
  valid_blocks t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  one_cr ad t2.
Proof. solve_onecr_preservation nocr_preservation_spawn. Qed.

(* ------------------------------------------------------------------------- *)
(* unique-critical-regions                                                   *)
(* ------------------------------------------------------------------------- *)

Definition unique_critical_regions (m : mem) (ths : threads) := forall ad,
  (m[ad].X = false -> forall_threads ths (no_cr ad)) /\
  (m[ad].X = true  -> forone_thread  ths (one_cr ad) (no_cr ad)).

(* preservation -- --------------------------------------------------------- *)

Local Lemma ucr_preservation_none : forall m ths tid t,
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_none]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad. specialize (Hucr ad) as [Hfall Hfone].
  split; intros; aspecialize.
  - intros ?. omicron; eauto using nocr_preservation_none.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split; intros; omicron;
    eauto using nocr_preservation_none, onecr_preservation_none.
Qed.

Local Lemma ucr_preservation_alloc : forall m ths tid t T,
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  unique_critical_regions (m +++ (None, T, false)) ths[tid <- t].
Proof.
  intros *.
  intros ? Hucr ? ad. specialize (Hucr ad) as [Hfall Hfone].
  split; intros; upsilon; aspecialize.
  - intros ?. omicron; eauto using nocr_preservation_alloc.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nocr_preservation_alloc, onecr_preservation_alloc.
Qed.

Local Lemma ucr_preservation_init : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_init ad te]--> t ->
  unique_critical_regions m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 2.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  assert (ad < #m) by eauto using vad_init_addr.
  split; intros; repeat omicron; aspecialize; upsilon;
  eauto using nocr_preservation_init;
  specialize Hfone as [tid' [? ?]]; exists tid'; split; intros;
  omicron; eauto using nocr_preservation_init, onecr_preservation_init.
Qed.

Local Lemma ucr_preservation_read : forall m ths tid t ad te,
  no_crs te ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_read ad te]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  split; intros; upsilon; aspecialize.
  - intros ?. omicron; eauto using nocr_preservation_read.
  - specialize Hfone as [tid' [? ?]]. exists tid'.
    split; intros; omicron;
    eauto using nocr_preservation_read, onecr_preservation_read.
Qed.

Local Lemma ucr_preservation_write : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_write ad te]--> t ->
  unique_critical_regions m[ad.t <- te] ths[tid <- t].
Proof.
  intros until 2.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  assert (ad < #m) by eauto using vad_write_addr.
  split; intros; repeat omicron; aspecialize; upsilon;
  eauto using nocr_preservation_write;
  specialize Hfone as [tid' [? ?]]; exists tid'; split; intros;
  omicron; eauto using nocr_preservation_write, onecr_preservation_write.
Qed.

Local Lemma ucr_preservation_acq : forall m ths tid ad t te,
  no_crs te ->
  (* --- *)
  ad < #m ->
  m[ad].X = false ->
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  unique_critical_regions m[ad.X <- true] ths[tid <- t].
Proof.
  intros until 3.
  intros ? Hucr ? ad'. specialize (Hucr ad') as [Hfall Hfone].
  split; intros; repeat omicron; aspecialize; upsilon;
  eauto using nocr_preservation_acq.
  - exists tid. sigma. split.
    + eauto using nocr_to_onecr.
    + intros. sigma. eauto.
  - specialize Hfone as [tid' [? ?]]. exists tid'. split.
    + omicron; eauto using onecr_preservation_acq.
    + intros. omicron; eauto using nocr_preservation_acq.
Qed.

Local Lemma ucr_preservation_rel : forall m ths tid ad t,
  ad < #m ->
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_rel ad]--> t ->
  unique_critical_regions m[ad.X <- false] ths[tid <- t].
Proof.
  intros until 1.
  intros ? Hucr ? ad'. destruct (Hucr ad') as [Hfall Hfone].
  assert (Had : m[ad].X = true). { (* This is cool *)
    destruct (m[ad].X) eqn:Heq; trivial.
    specialize (Hucr ad) as [? _]. aspecialize.
    exfalso. eauto using nocr_rel_contradiction.
  } 
  split; intros; try intros tid'; repeat omicron; aspecialize; upsilon;
  eauto using nocr_preservation_rel;
  specialize Hfone as [tid'' [? ?]].
  - destruct (nat_eq_dec tid'' tid'); subst; eauto using onecr_to_nocr.
    exfalso. eauto using nocr_rel_contradiction.
  - destruct (nat_eq_dec tid'' tid'); subst;
    eauto using nocr_rel_contradiction.
  - exists tid''.
    destruct (nat_eq_dec tid'' tid); subst; sigma;
    split; eauto using onecr_preservation_rel; intros.
    + sigma. eauto.
    + omicron; eauto using nocr_preservation_rel.
Qed.

Local Ltac eapply_in_tstep tt :=
  match goal with Htstep : _ --[_]--> _ |- _ => eapply tt in Htstep as ? end.

Local Lemma ucr_preservation_spawn : forall m ths tid t te,
  forall_threads ths valid_blocks ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  unique_critical_regions m (ths[tid <- t] +++ te).
Proof.
  intros until 1.
  intros ? Hucr ? ad'. destruct (Hucr ad') as [Hfall Hfone].
  split; intros; repeat omicron; aspecialize; upsilon.
  - eapply_in_tstep nocr_preservation_spawn; eauto using no_cr.
  - eauto using nocr_preservation_spawned.
  - specialize Hfone as [tid' [? ?]]. exists tid'. omicron;
    try invc_onecr; split; eauto using onecr_preservation_spawn; intros;
    omicron; eauto using no_cr.
    + eapply_in_tstep nocrs_spawn_term; eauto.
    + eauto using nocr_preservation_spawn.
    + eapply_in_tstep nocrs_spawn_term; eauto.
Qed.

Theorem ucr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_crs ->
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 valid_blocks ->
  (* --- *)
  unique_critical_regions m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  unique_critical_regions m2 ths2.
Proof.
  intros. invc_cstep; try invc_mstep.
  - eauto using ucr_preservation_none.
  - eauto using ucr_preservation_alloc.
  - eauto using ucr_preservation_init.
  - eauto using ucr_preservation_read.
  - eauto using ucr_preservation_write.
  - eauto using ucr_preservation_acq.
  - eauto using ucr_preservation_rel.
  - eauto using ucr_preservation_spawn.
Qed.

