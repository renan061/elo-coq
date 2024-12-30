From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import WellTypedTerm.
From Elo Require Import ConsistentTerm.
From Elo Require Import PointerTypes.
From Elo Require Import SafeTerm.

(* ------------------------------------------------------------------------- *)
(* consistent-regions                                                        *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_regions (m : mem) (R : region) : tm -> Prop :=
  | creg_unit  :                  consistent_regions m R <{unit           }>
  | creg_nat   : forall n,        consistent_regions m R <{nat n          }>
  | creg_seq   : forall t1 t2,    consistent_regions m R t1 ->
                                  consistent_regions m R t2 ->
                                  consistent_regions m R <{t1; t2         }>
  | creg_if    : forall t1 t2 t3, consistent_regions m R t1 ->
                                  consistent_regions m R t2 ->
                                  consistent_regions m R t3 ->
                                  consistent_regions m R (tm_if t1 t2 t3  )
  | creg_while : forall t1 t2,    consistent_regions m R t1 ->
                                  consistent_regions m R t2 ->
                                  consistent_regions m R (tm_while t1 t2  )
  | creg_var   : forall x,        consistent_regions m R <{var x          }>
  | creg_fun   : forall x Tx t,   consistent_regions m R t  ->
                                  consistent_regions m R <{fn x Tx t      }>
  | creg_call  : forall t1 t2,    consistent_regions m R t1 ->
                                  consistent_regions m R t2 ->
                                  consistent_regions m R <{call t1 t2     }>
  | creg_refR  : forall ad T,     consistent_regions m R <{&ad : r&T      }>
  | creg_refX  : forall ad T,     consistent_regions m R <{&ad : x&T      }>
  | creg_refW  : forall ad T,     R = m[ad].R               ->
                                  consistent_regions m R <{&ad : w&T      }>
  | creg_new   : forall t T,      consistent_regions m R t  ->
                                  consistent_regions m R <{new t : T      }>
  | creg_initR : forall ad t T,   consistent_regions m R t  ->
                                  consistent_regions m R <{init ad t : r&T}>
  | creg_initX : forall ad t T,   consistent_regions m (R_ad ad) t ->
                                  consistent_regions m R <{init ad t : x&T}>
  | creg_initW : forall ad t T,   R = m[ad].R               ->
                                  consistent_regions m R t  ->
                                  consistent_regions m R <{init ad t : w&T}>
  | creg_load  : forall t,        consistent_regions m R t  ->
                                  consistent_regions m R <{*t             }>
  | creg_asg   : forall t1 t2,    consistent_regions m R t1 ->
                                  consistent_regions m R t2 ->
                                  consistent_regions m R <{t1 := t2       }>
  | creg_acq   : forall t1 x t2,  consistent_regions m R t1 ->
                                  consistent_regions m R t2 ->
                                  consistent_regions m R <{acq t1 x t2    }>
  | creg_cr    : forall ad t,     consistent_regions m (R_ad ad) t ->
                                  consistent_regions m R <{cr ad t        }>
  | creg_spawn : forall t,        consistent_regions m R t  ->
                                  consistent_regions m R <{spawn t        }>
  .

Definition forall_threads_consistent_regions (m : mem) (ths : threads) :=
  forall tid, consistent_regions m (R_tid tid) ths[tid].

Definition forall_memory_consistent_regions (m : mem) :=
  forall ad t,
  m[ad].t = Some t ->
    (forall T, m[ad].T = `r&T` -> no_wrefs t)                       /\
    (forall T, m[ad].T = `x&T` -> consistent_regions m (R_ad ad) t) /\
    (forall T, m[ad].T = `w&T` -> consistent_regions m (m[ad].R) t).

(* inversion --------------------------------------------------------------- *)

Local Ltac _creg tt :=
  match goal with
  | H : consistent_regions _ _ <{unit                  }> |- _ => clear H
  | H : consistent_regions _ _ <{nat _                 }> |- _ => clear H
  | H : consistent_regions _ _ <{_; _                  }> |- _ => tt H
  | H : consistent_regions _ _ <{if _ then _ else _ end}> |- _ => tt H
  | H : consistent_regions _ _ <{while _ do _ end      }> |- _ => tt H
  | H : consistent_regions _ _ <{var _                 }> |- _ => clear H
  | H : consistent_regions _ _ <{fn _ _ _              }> |- _ => tt H
  | H : consistent_regions _ _ <{call _ _              }> |- _ => tt H
  | H : consistent_regions _ _ <{& _ : _               }> |- _ => tt H
  | H : consistent_regions _ _ <{new _ : _             }> |- _ => tt H
  | H : consistent_regions _ _ <{init _ _ : _          }> |- _ => tt H
  | H : consistent_regions _ _ <{* _                   }> |- _ => tt H
  | H : consistent_regions _ _ <{_ := _                }> |- _ => tt H
  | H : consistent_regions _ _ <{acq _ _ _             }> |- _ => tt H
  | H : consistent_regions _ _ <{cr _ _                }> |- _ => tt H
  | H : consistent_regions _ _ <{spawn _               }> |- _ => tt H
  end.

Ltac inv_creg  := _creg inv.
Ltac invc_creg := _creg invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma creg_from_nowrefs_noinits : forall Gamma m R t T,
  Gamma |-- t is T ->
  (* --- *)
  no_wrefs t ->
  no_inits t ->
  consistent_regions m R t.
Proof.
  intros. gendep R. gendep T. gendep Gamma.
  induction t; intros; invc_typeof; try invc_nowrefs; invc_noinits;
  eauto using consistent_regions.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma creg_subst : forall m R x tx t,
  no_inits t ->
  no_crs   t ->
  consistent_regions m R t ->
  consistent_regions m R tx ->
  consistent_regions m R <{[x := tx] t}>.
Proof.
  intros. induction t; intros; simpl; try destruct _str_eq_dec;
  invc_noinits; invc_nocrs; invc_creg; eauto using consistent_regions.
Qed.

Local Lemma creg_mem_add : forall m R R' t T,
  valid_term m t ->
  (* --- *)
  consistent_regions m R t ->
  consistent_regions (m +++ (None, T, false, R')) R t.
Proof.
  intros. gendep R. induction t; intros;
  invc_vtm; invc_creg; constructor; sigma; eauto.
Qed.

Local Lemma creg_mem_set : forall m R t ad' t',
  consistent_regions m R t ->
  consistent_regions m[ad'.t <- t'] R t.
Proof.
  intros. gendep R. induction t; intros;
  invc_creg; constructor; sigma; auto; repeat omicron; auto.
Qed.

Local Lemma creg_mem_acq : forall m R t ad,
  consistent_regions m R t ->
  consistent_regions m[ad.X <- true] R t.
Proof.
  intros. gendep R. induction t; intros;
  invc_creg; constructor; sigma; auto; repeat omicron; auto.
Qed.

Local Lemma creg_mem_rel : forall m R t ad,
  consistent_regions m R t ->
  consistent_regions m[ad.X <- false] R t.
Proof.
  intros. gendep R. induction t; intros;
  invc_creg; constructor; sigma; auto; repeat omicron; auto.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma creg_preservation_none : forall m R t1 t2,
  valid_term m t1 ->
  (* --- *)
  consistent_regions m R t1 ->
  t1 --[e_none]--> t2 ->
  consistent_regions m R t2.
Proof.
  intros. gendep R.
  ind_tstep; intros; repeat invc_vtm; repeat invc_creg;
  eauto using creg_subst, consistent_regions.
Qed.

Local Lemma creg_preservation_alloc : forall m R t1 t2 T,
  well_typed_term t1 ->
  valid_term m t1 ->
  safe_term t1 ->
  (* --- *)
  consistent_regions m R t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  consistent_regions (m +++ (None, T, false, gcr t1 R)) R t2.
Proof.
  intros * [T' ?] **. gendep R. gendep T'.
  ind_tstep; intros; invc_typeof; invc_vtm; invc_stm; invc_creg;
  try solve [constructor; sigma; try omicron;
             simpl; eauto using creg_from_nowrefs_noinits, creg_mem_add];
  constructor; kappa; eauto using creg_mem_add;
  value_does_not_step.
Qed.

Local Lemma creg_preservation_insert : forall m R t1 t2 ad t T,
  consistent_regions m R t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  consistent_regions m[ad.t <- t] R t2.
Proof.
  intros. gendep R. ind_tstep; intros; inv_creg;
  constructor; eauto using creg_mem_set; repeat omicron; eauto.
Qed.

Local Lemma creg_preservation_read : forall m R t1 t2 ad t,
  no_inits t ->
  well_typed_term t1 ->
  consistent_term m t1 ->
  forall_memory_consistent_regions m ->
  (* --- *)
  m[ad].t = Some t ->
  consistent_regions m R t1 ->
  t1 --[e_read ad t]--> t2 ->
  consistent_regions m R t2.
Proof.
  intros * ? [T ?] ? Hfmcr **. gendep R. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_ctm; repeat invc_creg;
  eauto using consistent_regions;
  invc_eq; specialize (Hfmcr ad); repeat spec;
  decompose record Hfmcr; eauto using creg_from_nowrefs_noinits.
Qed.

Local Lemma creg_preservation_write : forall m R t1 t2 ad t,
  consistent_regions m R t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_regions m[ad.t <- t] R t2.
Proof.
  intros. gendep R. ind_tstep; intros; invc_creg;
  constructor; eauto using creg_mem_set. repeat omicron; eauto.
Qed.

Local Lemma creg_preservation_acq : forall m R t1 t2 ad t,
  valid_term m t1 ->
  well_typed_term t1 ->
  consistent_term m t1 ->
  safe_term t1 ->
  forall_memory_consistent_regions m ->
  (* --- *)
  m[ad].t = Some t ->
  consistent_regions m R t1 ->
  t1 --[e_acq ad t]--> t2 ->
  consistent_regions m[ad.X <- true] R t2.
Proof.
  intros * ? [T ?] **. gendep R. gendep T.
  ind_tstep; intros;
  repeat invc_typeof; repeat invc_vtm; repeat invc_ctm; invc_stm;
  repeat invc_creg;
  constructor; eauto; repeat omicron; eauto using creg_mem_acq.
  invc_eq.
  decompose record (H3 ad t1 H4).
  eauto using creg_from_nowrefs_noinits, creg_subst, creg_mem_acq.
Qed.

Local Lemma creg_preservation_rel : forall m R t1 t2 ad,
  valid_term m t1 ->
  safe_term t1 ->
  (* --- *)
  consistent_regions m R t1 ->
  t1 --[e_rel ad]--> t2 ->
  consistent_regions m[ad.X <- false] R t2.
Proof.
  intros. gendep R. ind_tstep; intros;
  invc_vtm; invc_stm; invc_creg;
  try constructor; eauto using creg_mem_rel; repeat omicron; eauto.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using nowrefs_from_type, noinits_from_value, creg_from_nowrefs_noinits.
Qed.

Local Lemma creg_preservation_spawn : forall m R t1 t2 tid t,
  consistent_regions m R t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistent_regions m R t2.
Proof.
  intros. gendep R.
  ind_tstep; intros; invc_creg; eauto using consistent_regions.
Qed.

Local Corollary creg_preservation_spawned : forall m R t1 t2 tid t,
  well_typed_term t1 ->
  valid_term m t1 ->
  safe_term t1 ->
  (* --- *)
  t1 --[e_spawn tid t]--> t2 ->
  consistent_regions m R t.
Proof.
  intros. assert (well_typed_term t) as [? ?] by eauto using wtt_spawn_term.
  eauto using nowrefs_spawn_term, noinits_spawn_term, creg_from_nowrefs_noinits.
Qed.

(* ------------------------------------------------------------------------- *)

Theorem creg_preservation_rstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1      value                ->
  forall_program m1 ths1 well_typed_term      ->
  forall_program m1 ths1 (valid_term m1)      ->
  forall_program m1 ths1 (consistent_term m1) ->
  forall_program m1 ths1 safe_term            ->
  (* --- *)
  forall_memory_consistent_regions  m1 ->
  forall_threads_consistent_regions m1 ths1 ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  forall_threads_consistent_regions m2 ths2.
Proof.
  intros * ? [? ?] [? ?] [? ?] [? ?] ** tid'. nat_eq_dec tid' tid.
  - invc_rstep; invc_cstep; try invc_mstep; sigma.
    + eauto using creg_preservation_none.
    + upsilon. eauto using creg_preservation_alloc.
    + eauto using creg_preservation_insert.
    + eauto using noinits_from_value, creg_preservation_read.
    + eauto using creg_preservation_write.
    + eauto using creg_preservation_acq.
    + eauto using creg_preservation_rel.
    + eauto using creg_preservation_spawn.
  - invc_rstep; invc_cstep; try invc_mstep; sigma; upsilon; trivial.
    + eauto using creg_mem_add.
    + eauto using creg_mem_set.
    + eauto using creg_mem_set.
    + eauto using creg_mem_acq.
    + eauto using creg_mem_rel.
    + omicron; eauto using creg_preservation_spawned, consistent_regions.
Qed.

Theorem creg_preservation_base : forall t,
  no_refs         t ->
  no_inits        t ->
  no_crs          t ->
  well_typed_term t ->
  forall_threads_consistent_regions nil (base t).
Proof.
  unfold base. intros * ? ? ? [T ?] tid. simpl.
  destruct tid.
  - eauto using nowrefs_from_norefs, creg_from_nowrefs_noinits.
  - destruct tid; eauto using consistent_regions. 
Qed.

(* ------------------------------------------------------------------------- *)
(* forall-memory-consistent-regions preservation                             *)
(* ------------------------------------------------------------------------- *)

Ltac destruct_mcreg ad :=
  match goal with
  | Hmcreg : forall_memory_consistent_regions ?m
  , Hsome  : ?m[ad].t = Some ?t
  |- _ =>
    specialize (Hmcreg ad t Hsome) as [HmcregR [HmcregX HmcregW]]
  end;
  match goal with 
  | Hmcreg : forall _, ?m[ad].T = `r&_` -> _
  , Hptyp  : ?m[ad].T = `r&?T` |- _ =>
    specialize (Hmcreg T Hptyp)
  | Hmcreg : forall _, ?m[ad].T = `x&_` -> _
  , Hptyp  : ?m[ad].T = `x&?T` |- _ =>
    specialize (Hmcreg T Hptyp)
  | Hmcreg : forall _, ?m[ad].T = `w&_` -> _
  , Hptyp  : ?m[ad].T = `w&?T` |- _ =>
    specialize (Hmcreg T Hptyp)
  end.

Lemma mcreg_preservation_insert_termX : forall m R t1 t2 ad t T,
  consistent_regions m R t1 ->
  t1 --[e_insert ad t `x&T`]--> t2 ->
  consistent_regions m (R_ad ad) t.
Proof.
  intros. gendep R. ind_tstep; intros; invc_creg; eauto.
Qed.

Lemma mcreg_preservation_insert_termW : forall m R t1 t2 ad t T,
  consistent_regions m R t1 ->
  t1 --[e_insert ad t `w&T`]--> t2 ->
  consistent_regions m m[ad].R t.
Proof.
  intros. gendep R. ind_tstep; intros; invc_creg; eauto.
Qed.

Lemma mcreg_preservation_write_term : forall m R t1 t2 ad t,
  well_typed_term t1 ->
  (* --- *)
  consistent_regions m R t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_regions m m[ad].R t.
Proof.
  intros * [T ?] **. gendep R. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_creg; eauto.
Qed.

Local Lemma mcreg_preservation_alloc : forall m ths tid t T R,
  forall_memory m (valid_term m) ->
  memory_pointer_types m ->
  forall_threads_consistent_regions m ths ->
  forall_memory_consistent_regions  m ->
  (* --- *)
  R = gcr ths[tid] (R_tid tid) ->
  ths[tid] --[e_alloc (#m) T]--> t ->
  forall_memory_consistent_regions (m +++ (None, T, false, R)).
Proof.
  intros. subst. intros ad'' t'' Hsome.
  assert (ad'' < #m) by (lt_eq_gt (#m) ad''; sigma; upsilon; auto). sigma.
  destruct_mpt ad'';
  repeat split; intros; invc_eq; destruct_mcreg ad''; eauto using creg_mem_add.
Qed.

Local Lemma mcreg_preservation_insert : forall m ths tid t ad' t' T',
  forall_memory m (valid_term m) ->
  memory_pointer_types m ->
  forall_threads ths well_typed_term ->
  forall_threads ths (consistent_term m) ->
  forall_threads_consistent_regions m ths ->
  forall_memory_consistent_regions  m ->
  (* --- *)
  ths[tid] --[e_insert ad' t' T']--> t ->
  forall_memory_consistent_regions m[ad'.t <- t'].
Proof.
  intros. subst.
  assert (value t') by eauto using value_insert_term.
  intros ad'' t'' Hsome.
  repeat omicron; try invc Hsome.
  - upsilon.
    assert ((exists T'', T' = `r&T''`) \/
            (exists T'', T' = `x&T''`) \/
            (exists T'', T' = `w&T''`))
      as [[T'' ?] | [[T'' ?] | [T'' ?]]]
      by eauto using wtt_insert_type; subst.
    + assert (empty |-- t'' is `Safe T''`)
        by eauto using wtt_typeof_insert_term_R.
      assert (m[ad''].T = `r&T''`) by eauto using ptyp_for_insert.
      repeat split; intros; invc_eq.
      eauto using nowrefs_from_type.
    + assert (empty |-- t'' is T'') by eauto using wtt_typeof_insert_term_X.
      assert (m[ad''].T = `x&T''`) by eauto using ptyp_for_insert.
      repeat split; intros; invc_eq.
      eauto using creg_mem_set, mcreg_preservation_insert_termX.
    + assert (empty |-- t'' is T'') by eauto using wtt_typeof_insert_term_W.
      assert (m[ad''].T = `w&T''`) by eauto using ptyp_for_insert.
      repeat split; intros; try invc_eq.
      eauto using creg_mem_set, mcreg_preservation_insert_termW.
  - assert (ad'' < #m) by (lt_eq_gt (#m) ad''; sigma; upsilon; auto).
    destruct_mpt ad''; repeat split; intros; invc_eq; destruct_mcreg ad'';
    eauto using creg_mem_set.
Qed.

Local Lemma mcreg_preservation_write : forall m ths tid t ad' t',
  forall_threads ths well_typed_term ->
  forall_threads ths (consistent_term m) ->
  forall_threads_consistent_regions m ths ->
  forall_memory_consistent_regions  m ->
  (* --- *)
  ths[tid] --[e_write ad' t']--> t ->
  forall_memory_consistent_regions m[ad'.t <- t'].
Proof.
  intros.
  assert (exists T, m[ad'].T = `w&T`) as [T ?] by eauto using ptyp_for_write.
  repeat split; intros; repeat omicron; upsilon;
  try invc_eq; try destruct_mcreg ad;
  eauto using creg_mem_set, mcreg_preservation_write_term.
Qed.

Local Lemma mcreg_preservation_acq : forall m ths tid t ad' t',
  forall_memory_consistent_regions m ->
  ths[tid] --[e_acq ad' t']--> t ->
  forall_memory_consistent_regions m[ad'.X <- true].
Proof.
  intros ** ad'' t'' Hsome.
  repeat omicron; try invc Hsome; repeat split; intros; upsilon;
  destruct_mcreg ad''; eauto using creg_mem_acq.
Qed.

Local Lemma mcreg_preservation_rel : forall m ths tid t ad',
  forall_memory_consistent_regions m ->
  ths[tid] --[e_rel ad']--> t ->
  forall_memory_consistent_regions m[ad'.X <- false].
Proof.
  intros ** ad'' t'' Hsome.
  repeat omicron; try invc Hsome; repeat split; intros; upsilon;
  destruct_mcreg ad''; eauto using creg_mem_rel.
Qed.

Theorem mcreg_preservation_rstep : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 (valid_term m1)      ->
  forall_program m1 ths1 well_typed_term      ->
  forall_program m1 ths1 (consistent_term m1) ->
  memory_pointer_types m1                     ->
  (* --- *)
  forall_threads_consistent_regions m1 ths1   ->
  forall_memory_consistent_regions  m1        ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2          ->
  forall_memory_consistent_regions  m2.
Proof.
  intros * [? ?] [? ?] [? ?] ? ? Hmcreg ?.
  invc_rstep; invc_cstep; try invc_mstep; auto.
  - sigma. upsilon. eauto using mcreg_preservation_alloc.
  - eauto using mcreg_preservation_insert.
  - eauto using mcreg_preservation_write.
  - eauto using mcreg_preservation_acq.
  - eauto using mcreg_preservation_rel.
Qed.

Theorem mcreg_preservation_base :
  forall_memory_consistent_regions nil.
Proof.
  intros ad ? H. invc H. destruct ad; upsilon; auto.
Qed.

