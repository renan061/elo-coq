From Elo Require Import Core.
From Elo Require Import Properties1.

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

Lemma noref_insert_term : forall m t1 t2 ad t,
  no_ref m t1 ->
  t1 --[e_insert ad t]--> t2 ->
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

Lemma noref_write_contradiction : forall t1 t2 ad t,
  no_ref ad t1 ->
  t1 --[e_write ad t]--> t2 ->
  False.
Proof.
  intros. ind_tstep; repeat invc_noref; eauto.
Qed.

Lemma noref_acq_contradiction : forall t1 t2 ad t,
  no_ref ad t1 ->
  t1 --[e_acq ad t]--> t2 ->
  False.
Proof.
  intros. ind_tstep; repeat invc_noref; eauto.
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

Lemma noref_preservation_insert : forall ad t1 t2 ad' t,
  ad <> ad' ->
  no_ref ad t1 ->
  t1 --[e_insert ad' t]--> t2 ->
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
(* no-uninitialized-references                                               *)
(* ------------------------------------------------------------------------- *)

Definition no_uninitialized_references (m : mem) (ths : threads) :=
  forall ad, m[ad].t = None -> forall_program m ths (no_ref ad).

(* theorems ---------------------------------------------------------------- *)

Theorem write_then_initialized : forall m ths tid t ad te,
  no_uninitialized_references m ths ->
  (* --- *)
  ths[tid] --[e_write ad te]--> t ->
  m[ad].t <> None.
Proof.
  intros * Hnur ? Had. specialize (Hnur ad Had) as [? ?].
  eauto using noref_write_contradiction.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac simpl_nur :=
  intros ** ? ?;
  try match goal with _ : forall_threads _ (valid_addresses ?m) |- _ =>
    match goal with
    | _ : _ --[e_insert ?ad _]--> _ |- _ => assert (ad < #m)
    | _ : _ --[e_write  ?ad _]--> _ |- _ => assert (ad < #m)
    end;
    eauto using vad_insert_addr, vad_write_addr
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

Lemma nur_preservation_insert : forall m ths tid t ad te,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  no_uninitialized_references m ths ->
  ths[tid] --[e_insert ad te]--> t ->
  no_uninitialized_references m[ad.t <- te] ths[tid <- t].
Proof.
  simpl_nur. eauto using noref_insert_term, noref_preservation_insert.
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
  - eauto using nur_preservation_insert.
  - eauto using nur_preservation_read.
  - eauto using nur_preservation_write.
  - eauto using nur_preservation_acq.
  - eauto using nur_preservation_rel.
  - eauto using nur_preservation_spawn.
Qed.

