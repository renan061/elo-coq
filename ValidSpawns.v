From Elo Require Import Core.

From Elo Require Import WellTypedTerm.
From Elo Require Import NoWRef.
From Elo Require Import HasVar.

From Elo Require Import ConsistentRefs.

(* ------------------------------------------------------------------------- *)
(* valid-spawns                                                              *)
(* ------------------------------------------------------------------------- *)

Inductive valid_spawns : tm -> Prop :=
  | vs_unit  :                valid_spawns <{unit         }>
  | vs_nat   : forall n,      valid_spawns <{nat n        }>
  | vs_var   : forall x,      valid_spawns <{var x        }>
  | vs_fun   : forall x Tx t, valid_spawns t  ->
                              valid_spawns <{fn x Tx t    }>
  | vs_call  : forall t1 t2,  valid_spawns t1 ->
                              valid_spawns t2 ->
                              valid_spawns <{call t1 t2   }>
  | vs_ref   : forall ad T,   valid_spawns <{&ad : T      }>
  | vs_new   : forall T t,    valid_spawns t  ->
                              valid_spawns <{new t : T    }>
  | vs_init  : forall ad T t, valid_spawns t  ->
                              valid_spawns <{init ad t : T}>
  | vs_load  : forall t,      valid_spawns t  ->
                              valid_spawns <{*t           }>
  | vs_asg   : forall t1 t2,  valid_spawns t1 ->
                              valid_spawns t2 ->
                              valid_spawns <{t1 := t2     }>
  | vs_acq   : forall t1 t2,  valid_spawns t1 ->
                              valid_spawns t2 ->
                              valid_spawns <{acq t1 t2    }>
  | vs_cr    : forall ad t,   valid_spawns t  ->
                              valid_spawns <{cr ad t      }>
  | vs_spawn : forall t,      no_wrefs t      ->
                              valid_spawns <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vs tt :=
  match goal with
  | H : valid_spawns <{unit          }> |- _ => clear H
  | H : valid_spawns <{nat _         }> |- _ => clear H
  | H : valid_spawns <{var _         }> |- _ => clear H
  | H : valid_spawns <{fn _ _ _      }> |- _ => tt H
  | H : valid_spawns <{call _ _      }> |- _ => tt H
  | H : valid_spawns <{&_ : _        }> |- _ => clear H
  | H : valid_spawns <{new _ : _     }> |- _ => tt H
  | H : valid_spawns <{init _ _ : _  }> |- _ => tt H
  | H : valid_spawns <{* _           }> |- _ => tt H
  | H : valid_spawns <{_ := _        }> |- _ => tt H
  | H : valid_spawns <{acq _ _       }> |- _ => tt H
  | H : valid_spawns <{cr _ _        }> |- _ => tt H
  | H : valid_spawns <{spawn _       }> |- _ => tt H
  end.

Ltac inv_vs  := _vs inv.
Ltac invc_vs := _vs invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma vs_from_nowrefs : forall t,
  no_wrefs t ->
  valid_spawns t.
Proof.
  intros. induction t; invc_nowrefs; auto using valid_spawns.
Qed.

Lemma vs_insert_term : forall t1 t2 ad t,
  valid_spawns t1 ->
  t1 --[e_insert ad t]--> t2 ->
  valid_spawns t.
Proof.
  intros. ind_tstep; invc_vs; auto using valid_spawns.
Qed.

Lemma vs_write_term : forall t1 t2 ad t,
  valid_spawns t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_spawns t.
Proof.
  intros. ind_tstep; invc_vs; auto using valid_spawns.
Qed.

Lemma nowref_spawn_term : forall ad t1 t2 tid t,
  valid_spawns t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_wref ad t.
Proof.
  intros. ind_tstep; invc_vs; auto.
Qed.

Corollary nowrefs_spawn_term : forall t1 t2 tid t,
  valid_spawns t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_wrefs t.
Proof.
  unfold no_wrefs. eauto using nowref_spawn_term.
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

Local Lemma vs_subst : forall Gamma x tx t Tx T,
  value tx ->
  empty |-- tx is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  valid_spawns t ->
  valid_spawns tx ->
  valid_spawns <{[x := tx] t}>.
Proof.
  intros * ? ? ? Hvs ?. gendep Gamma. gendep T. gendep Tx.
  induction Hvs; intros; invc_typeof;
  simpl; try destruct str_eq_dec; eauto using valid_spawns;
  eauto using valid_spawns,
    MapEqv.update_permutation, ctx_eqv_typeof,
    update_safe_includes_safe_update, context_weakening.
  constructor. destruct (hasvar_dec x t); subst.
  - eauto using nowrefs_safe_value, nowrefs_subst1.
  - rewrite <- hasvar_subst; auto.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_vs_preservation :=
  intros; ind_tstep; repeat invc_vs; eauto using vs_from_nowrefs, valid_spawns.

Lemma vs_preservation_none : forall t1 t2,
  well_typed_term t1 ->
  (* --- *)
  valid_spawns t1 ->
  t1 --[e_none]--> t2 ->
  valid_spawns t2.
Proof.
  intros * [T ?] **. gendep T; ind_tstep; intros;
  repeat invc_typeof; repeat invc_vs; eauto using vs_subst, valid_spawns.
Qed.

Lemma vs_preservation_alloc : forall t1 t2 ad T,
  valid_spawns t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  valid_spawns t2.
Proof. solve_vs_preservation. Qed.

Lemma vs_preservation_insert : forall t1 t2 ad t,
  valid_spawns t1 ->
  t1 --[e_insert ad t]--> t2 ->
  valid_spawns t2.
Proof. solve_vs_preservation. Qed.

Lemma vs_preservation_read : forall t1 t2 ad t,
  valid_spawns t ->
  (* --- *)
  valid_spawns t1 ->
  t1 --[e_read ad t]--> t2 ->
  valid_spawns t2.
Proof. solve_vs_preservation. Qed.

Lemma vs_preservation_write : forall t1 t2 ad t,
  valid_spawns t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_spawns t2.
Proof. solve_vs_preservation. Qed.

Lemma vs_preservation_acq : forall m t1 t2 ad' t',
  forall_memory m value ->
  forall_memory m valid_spawns ->
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  m[ad'].t = Some t' ->
  valid_spawns t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  valid_spawns t2.
Proof.
  intros * ? ? [T ?] **. gendep T; ind_tstep; intros;
  repeat invc_typeof; repeat invc_cr; repeat invc_vs;
  eauto using vs_subst, valid_spawns.
  invc_eq. rewrite <- empty_eq_safe_empty in *. 
  eauto using vs_subst, valid_spawns.
Qed.

Lemma vs_preservation_rel : forall t1 t2 ad,
  valid_spawns t1 ->
  t1 --[e_rel ad]--> t2 ->
  valid_spawns t2.
Proof. solve_vs_preservation. Qed.

Lemma vs_preservation_spawn : forall t1 t2 tid t,
  valid_spawns t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_spawns t2.
Proof. solve_vs_preservation. Qed.

Lemma vs_preservation_spawned : forall t1 t2 tid t,
  valid_spawns t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_spawns t.
Proof. solve_vs_preservation. Qed.

Theorem vs_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistent_references m1) ->
  (* --- *)
  forall_program m1 ths1 valid_spawns ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 valid_spawns.
Proof.
  intros until 3. intros Hvb ?.
  assert (Hvb' := Hvb). destruct Hvb as [? ?].
  invc_cstep; try invc_mstep; upsilon.
  - eauto using vs_preservation_none.
  - eauto using vs_preservation_alloc.
  - eauto using vs_insert_term, vs_preservation_insert.
  - eauto using vs_preservation_read.
  - eauto using vs_write_term, vs_preservation_write.
  - eauto using vs_preservation_acq.
  - eauto using vs_preservation_rel.
  - eauto using vs_preservation_spawn, vs_preservation_spawned.
Qed.

