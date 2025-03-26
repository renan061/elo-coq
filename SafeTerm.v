From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentTerm.
From Elo Require Import Soundness.

(* ------------------------------------------------------------------------- *)
(* safe-term                                                                 *)
(* ------------------------------------------------------------------------- *)

Inductive safe_term : tm -> Prop :=
  | stm_unit  :                  safe_term <{unit                     }>
  | stm_nat   : forall n,        safe_term <{nat n                    }>
  | stm_plus  : forall t1 t2,    safe_term t1 ->
                                 safe_term t2 ->
                                 safe_term <{t1 + t2                  }>
  | stm_monus : forall t1 t2,    safe_term t1 ->
                                 safe_term t2 ->
                                 safe_term <{t1 - t2                  }>
  | stm_seq   : forall t1 t2,    safe_term t1 ->
                                 safe_term t2 ->
                                 safe_term <{t1; t2                   }>
  | stm_if    : forall t1 t2 t3, safe_term t1 ->
                                 safe_term t2 ->
                                 safe_term t3 ->
                                 safe_term <{if t1 then t2 else t3 end}>
  | stm_while : forall t1 t2,    safe_term t1 ->
                                 safe_term t2 ->
                                 safe_term <{while t1 do t2 end       }>
  | stm_var   : forall x,        safe_term <{var x                    }>
  | stm_fun   : forall x Tx t,   safe_term t  ->
                                 safe_term <{fn x Tx t                }>
  | stm_call  : forall t1 t2,    safe_term t1 ->
                                 safe_term t2 ->
                                 safe_term <{call t1 t2               }>
  | stm_ref   : forall ad T,     safe_term <{&ad : T                  }>
  | stm_newR  : forall t T,      safe_term t  ->
                                 safe_term <{new t : r&T              }>
  | stm_newX  : forall t T,      no_wrefs  t  ->
                                 safe_term t  ->
                                 safe_term <{new t : x&T              }>
  | stm_newW  : forall t T,      safe_term t  ->
                                 safe_term <{new t : w&T              }>
  | stm_init  : forall ad t T,   safe_term t  ->
                                 safe_term <{init ad t : T            }>
  | stm_load  : forall t,        safe_term t  ->
                                 safe_term <{*t                       }>
  | stm_asg   : forall t1 t2,    safe_term t1 ->
                                 safe_term t2 ->
                                 safe_term <{t1 := t2                 }>
  | stm_acq   : forall t1 x t2,  no_wrefs  t2 ->
                                 safe_term t1 ->
                                 safe_term t2 ->
                                 safe_term <{acq t1 x t2              }>
  | stm_cr    : forall ad t,     (exists T, empty |-- t is `Safe T`) ->
                                 safe_term t  ->
                                 safe_term <{cr ad t                  }>
  | stm_wait  : forall t,        safe_term t  ->
                                 safe_term <{wait t                   }>
  | stm_reacq : forall ad,       safe_term <{reacq ad                 }>
  | stm_spawn : forall t,        no_wrefs  t  ->
                                 safe_term t  ->
                                 safe_term <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _stm tt :=
  match goal with
  | H : safe_term <{unit                  }>   |- _ => clear H
  | H : safe_term <{nat _                 }>   |- _ => clear H
  | H : safe_term <{_ + _                 }>   |- _ => tt H
  | H : safe_term <{_ - _                 }>   |- _ => tt H
  | H : safe_term <{_; _                  }>   |- _ => tt H
  | H : safe_term <{if _ then _ else _ end}>   |- _ => tt H
  | H : safe_term <{while _ do _ end      }>   |- _ => tt H
  | H : safe_term <{var _                 }>   |- _ => clear H
  | H : safe_term <{fn _ _ _              }>   |- _ => tt H
  | H : safe_term <{call _ _              }>   |- _ => tt H
  | H : safe_term <{& _ : _               }>   |- _ => clear H
  | H : safe_term <{new _ : _             }>   |- _ => tt H
  | H : safe_term <{init _ _ : _          }>   |- _ => tt H
  | H : safe_term <{* _                   }>   |- _ => tt H
  | H : safe_term <{_ := _                }>   |- _ => tt H
  | H : safe_term <{acq _ _ _             }>   |- _ => tt H
  | H : safe_term <{cr _ _                }>   |- _ => tt H
  | H : safe_term <{wait _                }>   |- _ => tt H
  | H : safe_term <{reacq _               }>   |- _ => clear H
  | H : safe_term <{spawn _               }>   |- _ => tt H
  end.

Ltac inv_stm  := _stm inv.
Ltac invc_stm := _stm invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma stm_from_norefs_nocrs_wtt : forall t,
  no_refs         t ->
  no_crs          t ->
  well_typed_term t ->
  safe_term t.
Proof.
  intros * ? ? [T ?].
  remember empty as Gamma. clear HeqGamma. gendep Gamma. gendep T.
  induction t; intros; invc_norefs; invc_nocrs; invc_typeof;
  eauto using nowrefs_from_norefs, safe_term.
Qed.

Lemma stm_init_term : forall t1 t2 ad t,
  safe_term t1 ->
  t1 --[e_init ad t]--> t2 ->
  safe_term t.
Proof.
  intros. ind_tstep; invc_stm; auto using safe_term.
Qed.

Lemma stm_write_term : forall t1 t2 ad t,
  safe_term t1 ->
  t1 --[e_write ad t]--> t2 ->
  safe_term t.
Proof.
  intros. ind_tstep; invc_stm; auto using safe_term.
Qed.

Lemma nowref_spawn_term : forall ad t1 t2 t,
  safe_term t1 ->
  t1 --[e_spawn t]--> t2 ->
  no_wref ad t.
Proof.
  intros. ind_tstep; invc_stm; auto.
Qed.

Corollary nowrefs_spawn_term : forall t1 t2 t,
  safe_term t1 ->
  t1 --[e_spawn t]--> t2 ->
  no_wrefs t.
Proof.
  unfold no_wrefs. eauto using nowref_spawn_term.
Qed.

(* preservation ------------------------------------------------------------ *)

Corollary typeof_simpl : forall Gamma1 Gamma2 x Tx t T,
  Gamma2 includes Gamma1      ->
  Gamma1[x <== Tx] |-- t is T ->
  Gamma2[x <== Tx] |-- t is T.
Proof.
  eauto using context_weakening, MapInc.update_inclusion.
Qed.

Corollary typeof_permutation : forall Gamma x y Tx Ty t T,
  x <> y ->
  Gamma[x <== Tx][y <== Ty] |-- t is T ->
  Gamma[y <== Ty][x <== Tx] |-- t is T.
Proof.
  eauto using context_weakening, MapInc.update_permutation.
Qed.


Corollary typeof_safe_triple : forall Gamma x y z Tx Ty Tz t T,
  x <> y ->
  x <> z ->
  (safe Gamma[x <== Tx])[y <== Ty][z <== Tz] |-- t is T ->
  (safe Gamma)[y <== Ty][z <== Tz][x <== Tx] |-- t is T.
Proof.
  intros.
  eapply (context_weakening _ (safe Gamma)[y <== Ty][x <== Tx][z <== Tz]);
  eauto using MapInc.update_permutation. 
  eapply (context_weakening _ (safe Gamma)[x <== Tx][y <== Ty][z <== Tz]);
  eauto using MapInc.update_permutation, MapInc.update_inclusion. 
  eapply (context_weakening _ (safe Gamma[x <== Tx])[y <== Ty][z <== Tz]);
  eauto using update_safe_includes_safe_update, MapInc.update_inclusion. 
Qed.

Local Lemma stm_subst : forall Gamma x tx t Tx T,
  value tx ->
  empty |-- tx is Tx ->
  Gamma[x <== Tx] |-- t is T ->
  (* --- *)
  safe_term t ->
  safe_term tx ->
  safe_term <{[x := tx] t}>.
Proof.
  intros. gendep Gamma. gendep T.
  induction t; intros; simpl; repeat destruct _str_eq_dec;
  invc_typeof; invc_stm; eauto using safe_term;
  eauto using typeof_permutation, safe_term;
  eauto 6 using typeof_safe_triple, nowrefs_subst2, safe_term;
  eauto using safe_term, nowrefs_subst1,
    context_weakening, update_safe_includes_safe_update;
  try solve [match goal with H : safe_term ?t, _ : empty |-- ?t is ?T |- _ =>
    specialize (IHt H T empty);
    eauto using safe_term, context_weakening_empty
  end].
  match goal with H : exists _, _ |- _ => destruct H end.
  erewrite <- hasvar_subst; eauto using hasvar_type_contradiction, safe_term.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma stm_preservation_none : forall t1 t2,
  keywords t1        ->
  well_typed_term t1 ->
  (* --- *)
  safe_term t1 ->
  t1 --[e_none]--> t2 ->
  safe_term t2.
Proof.
  intros * ? [T ?] **. gendep T.
  ind_tstep; intros; invc_kw; repeat invc_typeof; repeat invc_stm;
  eauto using stm_subst, safe_term.
  match goal with H : exists _, _ |- _ => destruct H end.
  apply_deterministic_typing. 
  eauto using typeof_preservation_none, safe_term.
Qed.

Local Lemma stm_preservation_alloc : forall t1 t2 ad T,
  safe_term t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  safe_term t2.
Proof.
  intros. ind_tstep; intros; invc_stm; auto using safe_term.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_alloc, safe_term.
Qed.

Local Lemma stm_preservation_init : forall t1 t2 ad t,
  safe_term t1 ->
  t1 --[e_init ad t]--> t2 ->
  safe_term t2.
Proof.
  intros. ind_tstep; intros; invc_stm; auto using safe_term.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_init, safe_term.
Qed.

Local Lemma stm_preservation_read : forall m t1 t2 ad t,
  consistent_term m t1 ->
  forall_memory m safe_term ->
  (* --- *)
  m[ad].t = Some t ->
  safe_term t1 ->
  t1 --[e_read ad t]--> t2 ->
  safe_term t2.
Proof.
  intros. ind_tstep; intros; invc_ctm; invc_stm; eauto using safe_term.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_read, safe_term.
Qed.

Local Lemma stm_preservation_write : forall t1 t2 ad t,
  safe_term t1 ->
  t1 --[e_write ad t]--> t2 ->
  safe_term t2.
Proof.
  intros. ind_tstep; intros; invc_stm; auto using safe_term.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_write, safe_term.
Qed.

Local Lemma stm_preservation_acq : forall m t1 t2 ad t,
  forall_memory m value     ->
  forall_memory m safe_term ->
  keywords t1               ->
  keywords t                ->
  well_typed_term t1        ->
  consistent_term m t1      ->
  (* --- *)
  m[ad].t = Some t ->
  safe_term t1 ->
  t1 --[e_acq ad t]--> t2 ->
  safe_term t2.
Proof.
  intros * ? ? ? ? [T ?] **. gendep T.
  ind_tstep; intros;
  invc_kw; repeat invc_typeof; repeat invc_ctm; repeat invc_stm;
  try invc_eq; eauto using stm_subst, safe_term.
  - constructor.
    + rewrite <- empty_eq_safe_empty in *.
      eauto using kw_subst, typeof_subst, type_of.
    + eauto 6 using typeof_subst, stm_subst, value, type_of, safe_term.
  - match goal with H : exists _, _ |- _ => destruct H end.
    eauto using typeof_preservation_acq, safe_term.
Qed.

Local Lemma stm_preservation_rel : forall t1 t2 ad,
  safe_term t1 ->
  t1 --[e_rel ad]--> t2 ->
  safe_term t2.
Proof.
  intros. ind_tstep; intros; invc_stm; auto using safe_term.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_rel, safe_term.
Qed.

Local Lemma stm_preservation_wacq : forall t1 t2 ad,
  safe_term t1 ->
  t1 --[e_wacq ad]--> t2 ->
  safe_term t2.
Proof.
  intros. ind_tstep; intros; invc_stm; auto using safe_term.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_wacq, safe_term.
Qed.

Local Lemma stm_preservation_wrel : forall t1 t2 ad,
  safe_term t1 ->
  t1 --[e_wrel ad]--> t2 ->
  safe_term t2.
Proof.
  intros. ind_tstep; intros; invc_stm; auto using safe_term.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_wrel, safe_term.
Qed.

Local Lemma stm_preservation_spawn : forall t1 t2 t,
  safe_term t1 ->
  t1 --[e_spawn t]--> t2 ->
  safe_term t2.
Proof.
  intros. ind_tstep; intros; invc_stm; auto using safe_term.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using typeof_preservation_spawn, safe_term.
Qed.

Local Lemma stm_preservation_spawned : forall t1 t2 t,
  safe_term t1 ->
  t1 --[e_spawn t]--> t2 ->
  safe_term t.
Proof.
  intros. ind_tstep; intros; invc_stm; auto using safe_term.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem stm_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1      value ->
  forall_program m1 ths1 keywords ->
  forall_program m1 ths1 well_typed_term ->
  forall_program m1 ths1 (consistent_term m1) ->
  (* --- *)
  forall_program m1 ths1 safe_term ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  forall_program m2 ths2 safe_term.
Proof.
  intros * ? [? ?] [? ?] [? ?] [? ?] ?. split.
  - invc_cstep; try invc_mstep; trivial; intros ? ? ?; omicron; upsilon;
    auto; eauto using stm_init_term, stm_write_term.
  - invc_cstep; try invc_mstep; upsilon.
    + eauto using stm_preservation_none.
    + eauto using stm_preservation_alloc.
    + eauto using stm_preservation_init.
    + eauto using stm_preservation_read.
    + eauto using stm_preservation_write.
    + eauto using stm_preservation_acq.
    + eauto using stm_preservation_rel.
    + eauto using stm_preservation_wacq.
    + eauto using stm_preservation_wrel.
    + eauto using stm_preservation_spawn.
    + eauto using stm_preservation_spawned.
Qed.

Theorem stm_preservation_base : forall t,
  no_refs         t ->
  no_crs          t ->
  well_typed_term t ->
  forall_program nil (base t) safe_term.
Proof.
  intros. eapply forallprogram_base;
  eauto using stm_from_norefs_nocrs_wtt, safe_term.
Qed.

