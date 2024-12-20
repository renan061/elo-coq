From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentTerm.

(* ------------------------------------------------------------------------- *)
(* safe-spawns                                                               *)
(* ------------------------------------------------------------------------- *)

Inductive safe_spawns : tm -> Prop :=
  | ss_unit  :                 safe_spawns <{unit         }>
  | ss_nat   : forall n,       safe_spawns <{nat n        }>
  | ss_var   : forall x,       safe_spawns <{var x        }>
  | ss_fun   : forall x Tx t,  safe_spawns t  ->
                               safe_spawns <{fn x Tx t    }>
  | ss_call  : forall t1 t2,   safe_spawns t1 ->
                               safe_spawns t2 ->
                               safe_spawns <{call t1 t2   }>
  | ss_ref   : forall ad T,    safe_spawns <{&ad : T      }>
  | ss_new   : forall T t,     safe_spawns t  ->
                               safe_spawns <{new t : T    }>
  | ss_init  : forall ad T t,  safe_spawns t  ->
                               safe_spawns <{init ad t : T}>
  | ss_load  : forall t,       safe_spawns t  ->
                               safe_spawns <{*t           }>
  | ss_asg   : forall t1 t2,   safe_spawns t1 ->
                               safe_spawns t2 ->
                               safe_spawns <{t1 := t2     }>
  | ss_acq   : forall t1 x t2, safe_spawns t1 ->
                               safe_spawns t2 ->
                               safe_spawns <{acq t1 x t2  }>
  | ss_cr    : forall ad t,    safe_spawns t  ->
                               safe_spawns <{cr ad t      }>
  | ss_spawn : forall t,       no_wrefs t      ->
                               safe_spawns <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _ss tt :=
  match goal with
  | H : safe_spawns <{unit          }> |- _ => clear H
  | H : safe_spawns <{nat _         }> |- _ => clear H
  | H : safe_spawns <{var _         }> |- _ => clear H
  | H : safe_spawns <{fn _ _ _      }> |- _ => tt H
  | H : safe_spawns <{call _ _      }> |- _ => tt H
  | H : safe_spawns <{&_ : _        }> |- _ => clear H
  | H : safe_spawns <{new _ : _     }> |- _ => tt H
  | H : safe_spawns <{init _ _ : _  }> |- _ => tt H
  | H : safe_spawns <{* _           }> |- _ => tt H
  | H : safe_spawns <{_ := _        }> |- _ => tt H
  | H : safe_spawns <{acq _ _ _     }> |- _ => tt H
  | H : safe_spawns <{cr _ _        }> |- _ => tt H
  | H : safe_spawns <{spawn _       }> |- _ => tt H
  end.

Ltac inv_ss  := _ss inv.
Ltac invc_ss := _ss invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma ss_from_nowrefs : forall t,
  no_wrefs t ->
  safe_spawns t.
Proof.
  intros. induction t; invc_nowrefs; auto using safe_spawns.
Qed.

Lemma ss_insert_term : forall t1 t2 ad t T,
  safe_spawns t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  safe_spawns t.
Proof.
  intros. ind_tstep; invc_ss; auto using safe_spawns.
Qed.

Lemma ss_write_term : forall t1 t2 ad t,
  safe_spawns t1 ->
  t1 --[e_write ad t]--> t2 ->
  safe_spawns t.
Proof.
  intros. ind_tstep; invc_ss; auto using safe_spawns.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Local Lemma nowrefs_safe_value : forall Gamma x tx t Tx T,
  value tx ->
  empty |-- tx is Tx ->
  safe Gamma[x <== Tx] |-- t is T ->
  has_var x t ->
  no_wrefs tx.
Proof.
  intros * Hval **. invc Hval; invc_typeof;
  try solve [intros ?; eauto using no_wref];
  exfalso;
  match goal with H : safe _ |-- _ is _ |- _ =>
    eapply (hasvar_type_contradiction _ _ _ _ H); eauto
  end;
  unfold safe; rewrite lookup_update_eq; reflexivity.
Qed.

Local Lemma ss_subst : forall Gamma x tx t Tx T,
  value tx ->
  empty |-- tx is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  safe_spawns t ->
  safe_spawns tx ->
  safe_spawns <{[x := tx] t}>.
Proof.
  intros * ? ? ? Hvs ?. gendep Gamma. gendep T. gendep Tx.
  induction Hvs; intros; invc_typeof;
  simpl; try destruct _str_eq_dec; eauto using safe_spawns;
  eauto 8 using safe_spawns,
    MapEqv.update_permutation, ctx_eqv_typeof,
    MapInc.update_inclusion, update_safe_includes_safe_update,
    context_weakening, context_weakening_empty,
    nowrefs_subst1.
  Unshelve.
  eauto.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_ss_preservation :=
  intros; ind_tstep; repeat invc_ss; eauto using ss_from_nowrefs, safe_spawns.

Lemma ss_preservation_none : forall t1 t2,
  well_typed_term t1 ->
  (* --- *)
  safe_spawns t1 ->
  t1 --[e_none]--> t2 ->
  safe_spawns t2.
Proof.
  intros * [T ?] **. gendep T; ind_tstep; intros;
  repeat invc_typeof; repeat invc_ss; eauto using ss_subst, safe_spawns.
Qed.

Lemma ss_preservation_alloc : forall t1 t2 ad T,
  safe_spawns t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  safe_spawns t2.
Proof. solve_ss_preservation. Qed.

Lemma ss_preservation_insert : forall t1 t2 ad t T,
  safe_spawns t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  safe_spawns t2.
Proof. solve_ss_preservation. Qed.

Lemma ss_preservation_read : forall t1 t2 ad t,
  safe_spawns t ->
  (* --- *)
  safe_spawns t1 ->
  t1 --[e_read ad t]--> t2 ->
  safe_spawns t2.
Proof. solve_ss_preservation. Qed.

Lemma ss_preservation_write : forall t1 t2 ad t,
  safe_spawns t1 ->
  t1 --[e_write ad t]--> t2 ->
  safe_spawns t2.
Proof. solve_ss_preservation. Qed.

Lemma ss_preservation_acq : forall m t1 t2 ad' t',
  forall_memory m value ->
  forall_memory m safe_spawns ->
  well_typed_term t1 ->
  consistent_term m t1 ->
  (* --- *)
  m[ad'].t = Some t' ->
  safe_spawns t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  safe_spawns t2.
Proof.
  intros * ? ? [T ?] **. gendep T; ind_tstep; intros;
  repeat invc_typeof; repeat invc_ctm; repeat invc_ss;
  eauto using ss_subst, safe_spawns.
  invc_eq. rewrite <- empty_eq_safe_empty in *. 
  eauto using ss_subst, safe_spawns.
Qed.

Lemma ss_preservation_rel : forall t1 t2 ad,
  safe_spawns t1 ->
  t1 --[e_rel ad]--> t2 ->
  safe_spawns t2.
Proof. solve_ss_preservation. Qed.

Lemma ss_preservation_spawn : forall t1 t2 tid t,
  safe_spawns t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  safe_spawns t2.
Proof. solve_ss_preservation. Qed.

Lemma ss_preservation_spawned : forall t1 t2 tid t,
  safe_spawns t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  safe_spawns t.
Proof. solve_ss_preservation. Qed.

Theorem ss_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistent_term m1) ->
  (* --- *)
  forall_program m1 ths1 safe_spawns ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 safe_spawns.
Proof.
  intros until 3. intros Hvb ?.
  assert (Hvb' := Hvb). destruct Hvb as [? ?].
  invc_cstep; try invc_mstep; upsilon.
  - eauto using ss_preservation_none.
  - eauto using ss_preservation_alloc.
  - eauto using ss_insert_term, ss_preservation_insert.
  - eauto using ss_preservation_read.
  - eauto using ss_write_term, ss_preservation_write.
  - eauto using ss_preservation_acq.
  - eauto using ss_preservation_rel.
  - eauto using ss_preservation_spawn, ss_preservation_spawned.
Qed.

