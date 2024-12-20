From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.
(* From Elo Require Import ConsistentInits. *)

(* ------------------------------------------------------------------------- *)
(* consistent-references                                                     *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_references (m : mem) : tm -> Prop :=
  | cr_unit  :                 consistent_references m <{unit         }> 
  | cr_nat   : forall n,       consistent_references m <{nat n        }>
  | cr_var   : forall x,       consistent_references m <{var x        }>
  | cr_fun   : forall x Tx t,  consistent_references m t  ->
                               consistent_references m <{fn x Tx t    }>
  | cr_call  : forall t1 t2,   consistent_references m t1 ->
                               consistent_references m t2 ->
                               consistent_references m <{call t1 t2   }> 

  | cr_refR  : forall ad t T,  m[ad].t = Some t        ->
                               m[ad].T = `r&T`         ->
                               empty |-- t is `Safe T` ->
                               consistent_references m <{&ad : r&T    }>

  | cr_refX  : forall ad t T,  m[ad].t = Some t ->
                               m[ad].T = `x&T`  ->
                               empty |-- t is T ->
                               consistent_references m <{&ad : x&T    }>

  | cr_refW  : forall ad t T,  m[ad].t = Some t ->
                               m[ad].T = `w&T`  ->
                               empty |-- t is T ->
                               consistent_references m <{&ad : w&T    }>

  | cr_init  : forall ad t T,  consistent_references m t  ->
                               consistent_references m <{init ad t : T}>
  | cr_new   : forall T t,     consistent_references m t  ->
                               consistent_references m <{new t : T    }>
  | cr_load  : forall t,       consistent_references m t  ->
                               consistent_references m <{*t           }>
  | cr_asg   : forall t1 t2,   consistent_references m t1 ->
                               consistent_references m t2 ->
                               consistent_references m <{t1 := t2     }>
  | cr_acq   : forall t1 x t2, consistent_references m t1 ->
                               consistent_references m t2 ->
                               consistent_references m <{acq t1 x t2  }>
  | cr_cr    : forall ad t,    consistent_references m t  ->
                               consistent_references m <{cr ad t      }>
  | cr_spawn : forall t,       consistent_references m t  ->
                               consistent_references m <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _cr tt :=
  match goal with
  | H : consistent_references _ <{unit        }> |- _ => clear H
  | H : consistent_references _ <{nat _       }> |- _ => clear H
  | H : consistent_references _ <{var _       }> |- _ => clear H
  | H : consistent_references _ <{fn _ _ _    }> |- _ => tt H
  | H : consistent_references _ <{call _ _    }> |- _ => tt H
  | H : consistent_references _ <{& _ : _     }> |- _ => tt H
  | H : consistent_references _ <{new _ : _   }> |- _ => tt H
  | H : consistent_references _ <{init _ _ : _}> |- _ => tt H
  | H : consistent_references _ <{* _         }> |- _ => tt H
  | H : consistent_references _ <{_ := _      }> |- _ => tt H
  | H : consistent_references _ <{acq _ _ _   }> |- _ => tt H
  | H : consistent_references _ <{cr _ _      }> |- _ => tt H
  | H : consistent_references _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_cr  := _cr inv.
Ltac invc_cr := _cr invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma cr_insert_term : forall m t1 t2 ad t T,
  consistent_references m t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  consistent_references m t.
Proof.
  intros. ind_tstep; invc_cr; auto.
Qed.

Lemma cr_write_term : forall m t1 t2 ad t,
  consistent_references m t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_references m t.
Proof.
  intros. ind_tstep; invc_cr; auto.
Qed.

Lemma cr_spawn_term : forall m t1 t2 tid t,
  consistent_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistent_references m t.
Proof.
  intros. ind_tstep; invc_cr; auto.
Qed.

Lemma cr_write_address : forall m t1 t2 ad t,
  consistent_references m t1 ->
  t1 --[e_write ad t]--> t2 ->
  ad < #m.
Proof.
  intros. ind_tstep; repeat invc_cr; auto;
  lt_eq_gt (#m) ad; trivial; sigma; discriminate.
Qed.

Lemma cr_acq_address : forall m t1 t2 ad t,
  consistent_references m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  ad < #m.
Proof.
  intros. ind_tstep; repeat invc_cr; auto;
  lt_eq_gt (#m) ad; trivial; sigma; discriminate.
Qed.

Lemma consistent_insert : forall m t1 t2 ad' t' T',
  well_typed_term t1 ->
  consistent_inits m t1 ->
  (* --- *)
  t1 --[e_insert ad' t' T']--> t2 ->
  (exists T, empty |-- t' is `Safe T` /\ m[ad'].T = `r&T`) \/
  (exists T, empty |-- t' is T        /\ m[ad'].T = `x&T`) \/
  (exists T, empty |-- t' is T        /\ m[ad'].T = `w&T`).
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; invc_typeof; invc_ci; eauto.
Qed.

Lemma consistent_write : forall m t1 t2 ad t,
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  t1 --[e_write ad t]--> t2 ->
  (exists T, empty |-- t is T /\ m[ad].T = `w&T`).
Proof.
  intros * [T ?] **. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_cr; eauto.
Qed.

Corollary consistent_write_type : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  t1 --[e_write ad t]--> t2 ->
  empty |-- t is T <-> m[ad].T = `w&T`.
Proof.
  intros.
  assert (exists T, empty |-- t is T /\ m[ad].T = `w&T`) as [Te [? ?]]
      by eauto using consistent_write.
  split; intros.
  - apply_deterministic_typing. assumption.
  - invc_eq. assumption.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma cr_subst : forall m t tx x,
  consistent_references m t ->
  consistent_references m tx ->
  consistent_references m <{[x := tx] t}>.
Proof.
  intros. induction t; repeat invc_cr; simpl; try destruct _str_eq_dec;
  eauto using consistent_references.
Qed.

Lemma cr_mem_add : forall m t T,
  consistent_references m t ->
  consistent_references (m +++ (None, T, false, R_invalid)) t.
Proof.
  intros. induction t; invc_cr; eauto using consistent_references;
  (eapply cr_refR || eapply cr_refX || eapply cr_refW);
  eauto; omicron; trivial; discriminate.
Qed.

Local Ltac solve_mem_set m ad :=
  intros ? t **;
  assert (ad < #m) by (lt_eq_gt (#m) ad; sigma; trivial; discriminate);
  induction t; invc_cr; eauto using consistent_references;
  try match goal with H1 : _[?ad1].T = _, H2 : _[?ad2].T = _ |- _ =>
    nat_eq_dec ad1 ad2; try invc_eq
  end;
  (eapply cr_refR || eapply cr_refX || eapply cr_refW); sigma; upsilon; eauto.

Lemma cr_mem_setR : forall m t te ad T,
  m[ad].T = `r&T` ->
  empty |-- te is `Safe T` ->
  (* --- *)
  consistent_references m t ->
  consistent_references m[ad.t <- te] t.
Proof. solve_mem_set m ad. Qed.

Lemma cr_mem_setX : forall m t te ad T,
  m[ad].T = `x&T` ->
  empty |-- te is T ->
  (* --- *)
  consistent_references m t ->
  consistent_references m[ad.t <- te] t.
Proof. solve_mem_set m ad. Qed.

Lemma cr_mem_setW : forall m t te ad T,
  m[ad].T = `w&T` ->
  empty |-- te is T ->
  (* --- *)
  consistent_references m t ->
  consistent_references m[ad.t <- te] t.
Proof. solve_mem_set m ad. Qed.

Local Ltac solve_mem_acq_rel :=
  intros ? t **; induction t; invc_cr; eauto using consistent_references;
  (eapply cr_refR || eapply cr_refX || eapply cr_refW);
  sigma; eauto; repeat omicron; auto.

Lemma cr_mem_acq : forall m t ad,
  consistent_references m t ->
  consistent_references m[ad.X <- true] t.
Proof. solve_mem_acq_rel. Qed.

Lemma cr_mem_rel : forall m t ad,
  consistent_references m t ->
  consistent_references m[ad.X <- false] t.
Proof. solve_mem_acq_rel. Qed.

(* preservation ------------------------------------------------------------ *)

Lemma cr_preservation_none : forall m t1 t2,
  consistent_references m t1 ->
  t1 --[e_none]--> t2 ->
  consistent_references m t2.
Proof.
  intros. ind_tstep; repeat invc_cr;
  eauto using cr_subst, consistent_references.
Qed.

Lemma cr_preservation_alloc : forall m t1 t2 T,
  consistent_references m t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  consistent_references (m +++ (None, T, false, R_invalid)) t2.
Proof.
  intros. ind_tstep; intros; invc_cr;
  eauto using cr_mem_add, consistent_references.
Qed.

Lemma cr_preservation_mem_insert : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  consistent_inits m t1 ->
  consistent_references m t1 ->
  (* --- *)
  forall_memory m (consistent_references m) ->
  t1 --[e_insert ad t T]--> t2 ->
  forall_memory m[ad.t <- t] (consistent_references m[ad.t <- t]).
Proof.
  intros ** ? ? Had.
  assert ((exists T, empty |-- t is `Safe T` /\ m[ad].T = `r&T`) \/
          (exists T, empty |-- t is T        /\ m[ad].T = `x&T`) \/
          (exists T, empty |-- t is T        /\ m[ad].T = `w&T`)
  ) as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]] by eauto using consistent_insert;
  upsilon; eauto using cr_mem_setR, cr_mem_setX, cr_mem_setW, cr_insert_term. 
Qed.

Lemma cr_preservation_insert : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  consistent_inits m t1 ->
  (* --- *)
  ad < #m ->
  consistent_references m t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  consistent_references (m[ad.t <- t]) t2.
Proof.
  intros * Hwtt **.
  assert (
    (exists T', empty |-- t is `Safe T'` /\ m[ad].T = `r&T'`) \/
    (exists T', empty |-- t is T'        /\ m[ad].T = `x&T'`) \/
    (exists T', empty |-- t is T'        /\ m[ad].T = `w&T'`)
  ) as [[T' [? ?]] | [[T' [? ?]] | [T' [? ?]]]]
    by eauto using consistent_insert;
  clear Hwtt;
  ind_tstep; invc_ci; invc_cr;
  try solve [constructor; eauto using cr_mem_setR, cr_mem_setX, cr_mem_setW];
  invc_eq; (eapply cr_refR || eapply cr_refX || eapply cr_refW);
  sigma; upsilon; trivial.
Qed.

Lemma cr_preservation_unt_insert : forall m t1 t2 tu ad t T,
  well_typed_term t1 ->
  consistent_inits m t1 ->
  consistent_references m t1 ->
  (* --- *)
  ad < #m ->
  consistent_references m tu ->
  t1 --[e_insert ad t T]--> t2 ->
  consistent_references m[ad.t <- t] tu.
Proof.
  intros.
  assert (
    (exists T, empty |-- t is `Safe T` /\ m[ad].T = `r&T`) \/
    (exists T, empty |-- t is T        /\ m[ad].T = `x&T`) \/
    (exists T, empty |-- t is T        /\ m[ad].T = `w&T`)
  ) as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]]
    by eauto using consistent_insert;
  eauto using cr_mem_setR, cr_mem_setX, cr_mem_setW.
Qed.

Lemma cr_preservation_read : forall m t1 t2 ad t,
  consistent_references m t ->
  (* --- *)
  m[ad].t = Some t ->
  consistent_references m t1 ->
  t1 --[e_read ad t]--> t2 ->
  consistent_references m t2.
Proof.
  intros. ind_tstep; invc_cr; eauto using consistent_references.
Qed.

Lemma cr_preservation_mem_write : forall m t1 t2 ad t,
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  ad < #m ->
  forall_memory m (consistent_references m) ->
  t1 --[e_write ad t]--> t2 ->
  forall_memory m[ad.t <- t] (consistent_references m[ad.t <- t]).
Proof.
  intros ** ? ? Had.
  assert (exists T, empty |-- t is T /\ m[ad].T = `w&T`) as [Te [? ?]]
    by eauto using consistent_write.
  omicron; invc Had; eauto using cr_mem_setW, cr_write_term.
Qed.

Lemma cr_preservation_write : forall m t1 t2 ad t,
  well_typed_term t1 ->
  (* --- *)
  ad < #m ->
  consistent_references m t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_references m[ad.t <- t] t2.
Proof.
  intros.
  assert (exists T, empty |-- t is T /\ m[ad].T = `w&T`) as [Te [? ?]]
    by eauto using consistent_write.
  ind_tstep; invc_wtt; invc_cr;
  eauto using cr_mem_setW, consistent_references.
Qed.

Lemma cr_preservation_unt_write : forall m t1 t2 tu ad t,
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  ad < #m ->
  consistent_references m tu ->
  t1 --[e_write ad t]--> t2 ->
  consistent_references m[ad.t <- t] tu.
Proof.
  intros.
  assert (exists T, empty |-- t is T /\ m[ad].T = `w&T`) as [Te [? ?]]
    by eauto using consistent_write.
  eauto using cr_mem_setW.
Qed.

Lemma cr_preservation_acq : forall m t1 t2 ad t,
  m[ad].t = Some t ->
  consistent_references m t ->
  (* --- *)
  ad < #m ->
  consistent_references m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  consistent_references m[ad.X <- true] t2.
Proof.
  intros. ind_tstep; repeat invc_cr;
  eauto using cr_mem_acq, cr_subst, consistent_references;
  constructor; omicron; auto.
Qed.

Lemma cr_preservation_rel : forall m t1 t2 ad,
  ad < #m ->
  consistent_references m t1 ->
  t1 --[e_rel ad]--> t2 ->
  consistent_references m[ad.X <- false] t2.
Proof.
  intros. ind_tstep; invc_cr; eauto using cr_mem_rel, consistent_references;
  constructor; sigma; omicron; auto.
Qed.

Lemma cr_preservation_spawn : forall m t1 t2 tid t,
  consistent_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistent_references m t2.
Proof.
  intros. ind_tstep; invc_cr; eauto using consistent_references.
Qed.

Lemma cr_preservation_spawned : forall m t1 t2 tid t,
  consistent_references m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistent_references m t.
Proof.
  intros. ind_tstep; invc_cr; auto.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem cr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 well_typed_term ->
  forall_program m1 ths1 (consistent_inits m1) ->
  (* --- *)
  forall_program m1 ths1 (consistent_references m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 (consistent_references m2).
Proof.
  intros * [? ?] [? ?] [? ?] ?.
  invc_cstep; try invc_mstep; split; trivial.
  - upsilon. eauto using cr_preservation_none.
  - intros ? **. upsilon. eauto using cr_mem_add.
  - upsilon; eauto using cr_mem_add, cr_preservation_alloc.
  - eauto using cr_preservation_mem_insert.
  - upsilon; eauto using cr_preservation_insert, cr_preservation_unt_insert.
  - upsilon. eauto using cr_preservation_read.
  - eauto using cr_preservation_mem_write.
  - upsilon; eauto using cr_preservation_write, cr_preservation_unt_write.
  - intros ? **. upsilon. eauto using cr_mem_acq.
  - upsilon; eauto using cr_mem_acq, cr_preservation_acq.
  - intros ? **. upsilon. eauto using cr_mem_rel.
  - upsilon; eauto using cr_mem_rel, cr_preservation_rel.
  - upsilon; eauto using cr_preservation_spawn, cr_preservation_spawned.
Qed.

