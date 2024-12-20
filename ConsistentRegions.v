From Coq Require Import Lia.
From Coq Require Import Lists.List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

(* ------------------------------------------------------------------------- *)
(* consistent-regions                                                        *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_regions (m : mem) (R : region) : tm -> Prop :=
  | creg_unit  :                 consistent_regions m R <{unit           }>
  | creg_nat   : forall n,       consistent_regions m R <{nat n          }>
  | creg_var   : forall x,       consistent_regions m R <{var x          }>
  | creg_fun   : forall x Tx t,  consistent_regions m R t  ->
                                 consistent_regions m R <{fn x Tx t      }>
  | creg_call  : forall t1 t2,   consistent_regions m R t1 ->
                                 consistent_regions m R t2 ->
                                 consistent_regions m R <{call t1 t2     }>
  | creg_refR  : forall ad T,    consistent_regions m R <{&ad : r&T      }>
  | creg_refX  : forall ad T,    consistent_regions m R <{&ad : x&T      }>
  | creg_refW  : forall ad T,    R = m[ad].R               ->
                                 consistent_regions m R <{&ad : w&T      }>
  | creg_new   : forall t T,     consistent_regions m R t  ->
                                 consistent_regions m R <{new t : T      }>
  | creg_initR : forall ad t T,  consistent_regions m R t  ->
                                 consistent_regions m R <{init ad t : r&T}>
  | creg_initX : forall ad t T,  consistent_regions m (R_ad ad) t ->
                                 consistent_regions m R <{init ad t : x&T}>
  | creg_initW : forall ad t T,  R = m[ad].R               ->
                                 consistent_regions m R t  ->
                                 consistent_regions m R <{init ad t : w&T}>
  | creg_load  : forall t,       consistent_regions m R t  ->
                                 consistent_regions m R <{*t             }>
  | creg_asg   : forall t1 t2,   consistent_regions m R t1 ->
                                 consistent_regions m R t2 ->
                                 consistent_regions m R <{t1 := t2       }>
  | creg_acq   : forall t1 x t2, consistent_regions m R t1 ->
                                 consistent_regions m R t2 ->
                                 consistent_regions m R <{acq t1 x t2    }>
  | creg_cr    : forall ad t,    consistent_regions m (R_ad ad) t ->
                                 consistent_regions m R <{cr ad t        }>
  | creg_spawn : forall t,       consistent_regions m R t  ->
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
  | H : consistent_regions _ _ <{unit        }> |- _ => clear H
  | H : consistent_regions _ _ <{nat _       }> |- _ => clear H
  | H : consistent_regions _ _ <{var _       }> |- _ => clear H
  | H : consistent_regions _ _ <{fn _ _ _    }> |- _ => tt H
  | H : consistent_regions _ _ <{call _ _    }> |- _ => tt H
  | H : consistent_regions _ _ <{& _ : _     }> |- _ => tt H
  | H : consistent_regions _ _ <{new _ : _   }> |- _ => tt H
  | H : consistent_regions _ _ <{init _ _ : _}> |- _ => tt H
  | H : consistent_regions _ _ <{* _         }> |- _ => tt H
  | H : consistent_regions _ _ <{_ := _      }> |- _ => tt H
  | H : consistent_regions _ _ <{acq _ _ _   }> |- _ => tt H
  | H : consistent_regions _ _ <{cr _ _      }> |- _ => tt H
  | H : consistent_regions _ _ <{spawn _     }> |- _ => tt H
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
  induction t; intros; invc_typeof; invc_nowrefs; invc_noinits;
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

Local Lemma gcr_call_t1 : forall t1 t2 R,
  ~ value t1 ->
  gcr <{call t1 t2}> R = gcr t1 R.
Proof.
  intros * H. simpl. destruct t1; auto; exfalso; auto using value.
Qed.

Local Lemma gcr_call_t2 : forall t1 t2 R,
  value t1 ->
  gcr <{call t1 t2}> R = gcr t2 R.
Proof.
  intros * H. simpl. destruct t1; auto; invc H.
Qed.

Local Lemma gcr_initR : forall ad t T R,
  gcr <{init ad t : r&T}> R = gcr t R.
Proof. trivial. Qed.

Local Lemma gcr_initX : forall ad t T R,
  gcr <{init ad t : x&T}> R = gcr t (R_ad ad).
Proof. trivial. Qed.

Local Lemma gcr_initW : forall ad t T R,
  gcr <{init ad t : w&T}> R = gcr t R.
Proof. trivial. Qed.

Local Lemma gcr_asg_t1 : forall t1 t2 R,
  ~ value t1 ->
  gcr <{t1 := t2}> R = gcr t1 R.
Proof.
  intros * H. simpl. destruct t1; auto; exfalso; auto using value.
Qed.

Local Lemma gcr_asg_t2 : forall t1 t2 R,
  value t1 ->
  gcr <{t1 := t2}> R = gcr t2 R.
Proof.
  intros * H. simpl. destruct t1; auto; invc H.
Qed.

Local Lemma creg_preservation_alloc : forall m R t1 t2 T,
  well_typed_term t1 ->
  valid_term m t1 ->
  safe_newx t1 ->
  (* --- *)
  consistent_regions m R t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  consistent_regions (m +++ (None, T, false, gcr t1 R)) R t2.
Proof.
  intros * [T' ?] **. gendep R. gendep T'.
  ind_tstep; intros; invc_typeof; invc_vtm; invc_snx; invc_creg;
  try solve [constructor; sigma; try omicron;
             simpl; eauto using creg_from_nowrefs_noinits, creg_mem_add];
  constructor; eauto using creg_mem_add.
  - rewrite gcr_call_t1; eauto. intros ?; value_does_not_step.
  - rewrite gcr_call_t2; eauto.
  - rewrite gcr_asg_t1;  eauto. intros ?; value_does_not_step.
  - rewrite gcr_asg_t2;  eauto.
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
  forall_memory m no_inits ->
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
  safe_acq t1 ->
  forall_memory_consistent_regions m ->
  (* --- *)
  m[ad].t = Some t ->
  consistent_regions m R t1 ->
  t1 --[e_acq ad t]--> t2 ->
  consistent_regions m[ad.X <- true] R t2.
Proof.
  intros * ? [T ?] **. gendep R. gendep T.
  ind_tstep; intros;
  repeat invc_typeof; repeat invc_vtm; repeat invc_ctm; inv_sacq;
  repeat invc_creg;
  constructor; eauto; repeat omicron; eauto using creg_mem_acq.
  invc_eq.
  decompose record (H3 ad t1 H4).
  eauto using creg_from_nowrefs_noinits, creg_subst, creg_mem_acq.
Qed.

Local Lemma creg_preservation_rel : forall m R t1 t2 ad,
  valid_term m t1 ->
  safe_cr t1 ->
  (* --- *)
  consistent_regions m R t1 ->
  t1 --[e_rel ad]--> t2 ->
  consistent_regions m[ad.X <- false] R t2.
Proof.
  intros. gendep R. ind_tstep; intros;
  invc_vtm; invc_scr; invc_creg;
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
  safe_spawns t1 ->
  (* --- *)
  t1 --[e_spawn tid t]--> t2 ->
  consistent_regions m R t.
Proof.
  intros. assert (well_typed_term t) as [? ?] by eauto using wtt_spawn_term.
  eauto using nowrefs_spawn_term, noinits_spawn_term, creg_from_nowrefs_noinits.
Qed.

Theorem creg_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   no_inits ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (valid_term m1) ->
  forall_threads ths1 (consistent_term m1) ->
  forall_threads ths1 safe_newx ->
  forall_threads ths1 safe_acq ->
  forall_threads ths1 safe_cr ->
  forall_threads ths1 safe_spawns ->
  (* --- *)
  forall_memory_consistent_regions  m1 ->
  forall_threads_consistent_regions m1 ths1 ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  forall_threads_consistent_regions m2 ths2.
Proof.
  intros ** tid'. nat_eq_dec tid' tid.
  - invc_ostep; invc_cstep; try invc_mstep; sigma.
    + eauto using creg_preservation_none.
    + upsilon. eauto using creg_preservation_alloc.
    + eauto using creg_preservation_insert.
    + eauto using creg_preservation_read.
    + eauto using creg_preservation_write.
    + eauto using creg_preservation_acq.
    + eauto using creg_preservation_rel.
    + eauto using creg_preservation_spawn.
  - invc_ostep; invc_cstep; try invc_mstep; sigma; upsilon; trivial.
    + eauto using creg_mem_add.
    + eauto using creg_mem_set.
    + eauto using creg_mem_set.
    + eauto using creg_mem_acq.
    + eauto using creg_mem_rel.
    + omicron; eauto using creg_preservation_spawned, consistent_regions.
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

Theorem mcreg_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   (valid_term m1) ->
  memory_pointer_types m1 ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistent_term m1) ->
  (* --- *)
  forall_threads_consistent_regions m1 ths1 ->
  forall_memory_consistent_regions  m1 ->
  m1 / ths1 ~~~[tid, e]~~> m2 / ths2 ->
  forall_memory_consistent_regions  m2.
Proof.
  intros until 4. intros ? Hmcreg ?.
  invc_ostep; invc_cstep; try invc_mstep; auto.
  - sigma. upsilon. eauto using mcreg_preservation_alloc.
  - eauto using mcreg_preservation_insert.
  - eauto using mcreg_preservation_write.
  - eauto using mcreg_preservation_acq.
  - eauto using mcreg_preservation_rel.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_noinits_nocrs : forall t R,
  no_inits t ->
  no_crs t ->
  gcr t R = R.
Proof.
  intros. induction t; invc_noinits; invc_nocrs; simpl; eauto;
  destruct (is_value t1); eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma gcr_read_t1 : forall m t1 t2 ad' t' T' R,
  well_typed_term t1 ->
  consistent_term m t1 ->
  consistent_regions m R t1 ->
  (* --- *)
  m[ad'].T = `w&T'` ->
  m[ad'].t = Some t' ->
  t1 --[e_read ad' t']--> t2 ->
  gcr t1 R = m[ad'].R.
Proof.
  intros * [T ?] **. gendep R. gendep T. ind_tstep; intros;
  repeat invc_typeof; repeat invc_ctm; repeat invc_creg; eauto.
  - rewrite gcr_call_t1; eauto. intros ?; value_does_not_step.
  - rewrite gcr_call_t2; eauto.
  - rewrite gcr_initR. eauto.
  - rewrite gcr_initX. eauto.
  - rewrite gcr_initW. eauto.
  - rewrite gcr_asg_t1; eauto. intros ?; value_does_not_step.
  - rewrite gcr_asg_t2; eauto.
Qed.

Lemma gcr_read_term : forall m t1 t2 ad' t' R,
  forall_memory m no_inits ->
  forall_memory m no_crs   ->
  (* --- *)
  m[ad'].t = Some t' ->
  t1 --[e_read ad' t']--> t2 ->
  gcr t' R = R.
Proof.
  intros. erewrite gcr_noinits_nocrs; eauto.
Qed.

Lemma gcr_read_t1_term : forall m t1 t2 ad' t' T' R,
  forall_memory m no_inits ->
  forall_memory m no_crs   ->
  well_typed_term t1 ->
  consistent_term m t1 ->
  consistent_regions m R t1  ->
  (* --- *)
  m[ad'].T = `w&T'` ->
  m[ad'].t = Some t' ->
  t1 --[e_read ad' t']--> t2 ->
  gcr t1 R = gcr t' m[ad'].R.
Proof.
  intros. erewrite gcr_read_t1; eauto. erewrite gcr_read_term; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma gcr_write_t1 : forall m t1 t2 ad' t' R,
  well_typed_term t1 ->
  valid_term m t1 ->
  consistent_regions m R t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  gcr t1 R = m[ad'].R.
Proof.
  intros * [T ?] **. gendep R. gendep T.
  assert (value t') by eauto using value_write_term.
  ind_tstep; intros; repeat invc_typeof; repeat invc_vtm; repeat invc_creg;
  eauto.
  - rewrite gcr_call_t1; eauto. intros ?; value_does_not_step.
  - rewrite gcr_call_t2; eauto.
  - rewrite gcr_initR. eauto.
  - rewrite gcr_initX. eauto.
  - rewrite gcr_initW. eauto.
  - rewrite gcr_asg_t1; eauto. intros ?; value_does_not_step.
  - rewrite gcr_asg_t2; eauto.
  - simpl. rewrite gcr_noinits_nocrs;
    eauto using noinits_from_value, nocrs_from_value.
Qed.

Corollary ostep_gcr_write : forall m1 m2 ths1 ths2 tid ad' t',
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (valid_term m1)    ->
  forall_threads_consistent_regions m1 ths1 ->
  (* --- *)
  m1 / ths1 ~~~[tid, e_write ad' t']~~> m2 / ths2 ->
  gcr ths1[tid] (R_tid tid) = m1[ad'].R.
Proof.
  intros * ? ? Hcreg **. specialize (Hcreg tid).
  invc_ostep. invc_cstep. invc_mstep.
  eauto using gcr_write_t1.
Qed.

Lemma gcr_write_term : forall m t1 t2 ad' t' R,
  valid_term m t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  gcr t' R = R.
Proof.
  intros.
  assert (value t') by eauto using value_write_term.
  assert (valid_term m t') by eauto using vtm_write_term.
  rewrite gcr_noinits_nocrs; eauto using noinits_from_value, nocrs_from_value.
Qed.

Lemma gcr_write_t1_term : forall m t1 t2 ad' t' R,
  well_typed_term t1 ->
  valid_term m t1 ->
  consistent_regions m R t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  gcr t1 R = gcr t' m[ad'].R.
Proof.
  intros. erewrite gcr_write_t1; eauto. erewrite gcr_write_term; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* region-exclusivity                                                        *)
(* ------------------------------------------------------------------------- *)

Definition region_exclusivity (t : tm) := forall ad,
  (one_init ad t \/ no_init ad t) /\
  (one_cr   ad t \/ no_cr   ad t) /\
  (one_init ad t -> no_cr   ad t) /\
  (one_cr   ad t -> no_init ad t).

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_regexc :=
  intros * H; try match goal with |- _ /\ _ => split end; intros ad';
  specialize (H ad') as [[? | ?] [[? | ?] [? ?]]]; repeat split; repeat spec;
  try inv_oneinit; try inv_onecr; try inv_nocr; try inv_noinit; auto; intros ?;
  exfalso; eauto using noinit_oneinit_contradiction, nocr_onecr_contradiction. 

Local Lemma inv_regexc_fun : forall x Tx t,
  region_exclusivity <{fn x Tx t}> ->
  region_exclusivity t.
Proof. solve_inv_regexc. Qed.

Local Lemma inv_regexc_call : forall t1 t2,
  region_exclusivity <{call t1 t2}> ->
  region_exclusivity t1 /\ region_exclusivity t2.
Proof. solve_inv_regexc. Qed.

Local Lemma inv_regexc_new : forall t T,
  region_exclusivity <{new t : T}> ->
  region_exclusivity t.
Proof. solve_inv_regexc. Qed.

Local Lemma inv_regexc_init : forall ad t T,
  region_exclusivity <{init ad t : T}> ->
  region_exclusivity t.
Proof. solve_inv_regexc. Qed.

Local Lemma inv_regexc_load : forall t,
  region_exclusivity <{*t}> ->
  region_exclusivity t.
Proof. solve_inv_regexc. Qed.

Local Lemma inv_regexc_asg : forall t1 t2,
  region_exclusivity <{t1 := t2}> ->
  region_exclusivity t1 /\ region_exclusivity t2.
Proof. solve_inv_regexc. Qed.

Local Lemma inv_regexc_acq : forall t1 x t2,
  region_exclusivity <{acq t1 x t2}> ->
  region_exclusivity t1 /\ region_exclusivity t2.
Proof. solve_inv_regexc. Qed.

Local Lemma inv_regexc_cr : forall ad t,
  region_exclusivity <{cr ad t}> ->
  region_exclusivity t.
Proof. solve_inv_regexc. Qed.

Local Lemma inv_regexc_spawn : forall t,
  region_exclusivity <{spawn t}> ->
  region_exclusivity t.
Proof. solve_inv_regexc. Qed.

Ltac invc_regexc :=
  match goal with
  | H : region_exclusivity <{unit        }> |- _ => clear H
  | H : region_exclusivity <{nat _       }> |- _ => clear H
  | H : region_exclusivity <{var _       }> |- _ => clear H
  | H : region_exclusivity <{fn _ _ _    }> |- _ => eapply inv_regexc_fun   in H
  | H : region_exclusivity <{call _ _    }> |- _ => eapply inv_regexc_call  in H
  | H : region_exclusivity <{& _ : _     }> |- _ => clear H
  | H : region_exclusivity <{new _ : _   }> |- _ => eapply inv_regexc_new   in H
  | H : region_exclusivity <{init _ _ : _}> |- _ => eapply inv_regexc_init  in H
  | H : region_exclusivity <{* _         }> |- _ => eapply inv_regexc_load  in H
  | H : region_exclusivity <{_ := _      }> |- _ => eapply inv_regexc_asg   in H
  | H : region_exclusivity <{acq _ _ _   }> |- _ => eapply inv_regexc_acq   in H
  | H : region_exclusivity <{cr _ _      }> |- _ => eapply inv_regexc_cr    in H
  | H : region_exclusivity <{spawn _     }> |- _ => eapply inv_regexc_spawn in H
  end;
  repeat match goal with
  | H : region_exclusivity _ /\ region_exclusivity _ |- _ => destruct H
  end.

(* ------------------------------------------------------------------------- *)

Local Lemma gcr_rewrite_call_t1 : forall t1 t2 R,
  ~ value t1 ->
  gcr <{call t1 t2}> R = gcr t1 R.
Proof.
  intros * H. simpl. destruct t1; auto; exfalso; auto using value.
Qed.

Local Lemma gcr_rewrite_call_t2 : forall t1 t2 R,
  value t1 ->
  gcr <{call t1 t2}> R = gcr t2 R.
Proof.
  intros * H. simpl. destruct t1; auto; invc H.
Qed.

Local Lemma gcr_rewrite_initX : forall ad t T R,
  gcr <{init ad t : x&T}> R = gcr t (R_ad ad).
Proof. trivial. Qed.

Local Lemma gcr_rewrite_initW : forall ad t T R,
  gcr <{init ad t : w&T}> R = gcr t R.
Proof. trivial. Qed.

Local Lemma gcr_rewrite_asg_t1 : forall t1 t2 R,
  ~ value t1 ->
  gcr <{t1 := t2}> R = gcr t1 R.
Proof.
  intros * H. simpl. destruct t1; auto; exfalso; auto using value.
Qed.

Local Lemma gcr_rewrite_asg_t2 : forall t1 t2 R,
  value t1 ->
  gcr <{t1 := t2}> R = gcr t2 R.
Proof.
  intros * H. simpl. destruct t1; auto; invc H.
Qed.

(* gcr (get-current-region) simplification *)
Ltac kappa :=
 repeat match goal with
 | H : context C [ gcr <{call ?t1 ?t2}> ?R ], H' : ~ value ?t1 |- _ =>
   rewrite (gcr_rewrite_call_t1 t1 t2 R H') in H

 | H : context C [ gcr <{call ?t1 ?t2}> ?R ], H' : value   ?t1 |- _ =>
   rewrite (gcr_rewrite_call_t2 t1 t2 R H') in H

 | H : context C [ gcr <{?t1 := ?t2}> ?R ], H' : ~ value ?t1 |- _ =>
   rewrite (gcr_rewrite_asg_t1 t1 t2 R H') in H

 | H : context C [ gcr <{?t1 := ?t2}> ?R ], H' : value   ?t1 |- _ =>
   rewrite (gcr_rewrite_asg_t2 t1 t2 R H') in H

 | H : context C [gcr <{unit                }> _] |- _ => simpl in H
 | H : context C [gcr <{nat _               }> _] |- _ => simpl in H
 | H : context C [gcr <{var _               }> _] |- _ => simpl in H
 | H : context C [gcr <{fn _ _ _            }> _] |- _ => simpl in H
 | H : context C [gcr <{call ?t _           }> _] |- _ => destruct (value_dec t)
 | H : context C [gcr <{& _ : _             }> _] |- _ => simpl in H
 | H : context C [gcr <{new _ : _           }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : Unit     }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : Num      }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : r&_      }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : x&_      }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : w&_      }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : (_ --> _)}> _] |- _ => simpl in H 
 | H : context C [gcr <{init _ _ : Safe ?T  }> _] |- _ => destruct T 
 | H : context C [gcr <{init _ _ : ?T       }> _] |- _ => destruct T 
 | H : context C [gcr <{* _                 }> _] |- _ => simpl in H
 | H : context C [gcr <{?t := _             }> _] |- _ => destruct (value_dec t)
 | H : context C [gcr <{acq _ _ _           }> _] |- _ => simpl in H
 | H : context C [gcr <{cr _ _              }> _] |- _ => simpl in H
 | H : context C [gcr <{spawn _             }> _] |- _ => simpl in H
 end.

Lemma gcr_noinit_nocr_contradiction : forall ad t R,
  R <> R_ad ad ->
  gcr t R = R_ad ad ->
  no_init ad t ->
  no_cr ad t ->
  False.
Proof.
  intros * ? Hgcr **. gendep R. induction t; intros;
  invc_noinit; invc_nocr; kappa; auto; invc Hgcr; eauto; do 2 spec;
  match goal with _ : addr, ad : addr |- _ => eapply (IHt (R_ad ad)) end;
  trivial; intros F; invc F; eauto.
Qed.

Corollary gcr_noinit_nocr_contradiction1 : forall tid ad t,
  gcr t (R_tid tid) = R_ad ad ->
  no_init ad t ->
  no_cr ad t ->
  False.
Proof.
  intros. eapply gcr_noinit_nocr_contradiction; eauto. intros F. invc F.
Qed.

Corollary gcr_noinit_nocr_contradiction2 : forall ad' ad t,
  gcr t (R_ad ad') = R_ad ad ->
  ad <> ad' ->
  no_init ad t ->
  no_cr ad t ->
  False.
Proof.
  intros. eapply gcr_noinit_nocr_contradiction; eauto. intros F. invc F. auto.
Qed.

Lemma oneinit_or_onecr_from_gcr : forall ad t tid,
  region_exclusivity t ->
  (* --- *)
  gcr t (R_tid tid) = R_ad ad ->
  (one_init ad t \/ one_cr ad t).
Proof.
  intros * Hregexc Hgcr. assert (Hregexc' := Hregexc).
  induction t; kappa; invc_regexc; repeat spec; try solve [invc Hgcr];
  destruct (Hregexc ad) as [[? | ?] [[? | ?] _]]; eauto; invc_noinit; invc_nocr;
  try solve [exfalso; eauto using gcr_noinit_nocr_contradiction1];
  match goal with ad1 : addr, ad2 : addr |- _ => nat_eq_dec ad1 ad2 end;
  exfalso; eauto using gcr_noinit_nocr_contradiction2.
Qed.

#[export] Hint Extern 8 =>
  match goal with
  | |- R_invalid <> R_tid _   => intros F; invc F
  | |- R_invalid <> R_ad  _   => intros F; invc F
  | |- R_tid _   <> R_ad  _   => intros F; invc F
  | |- R_tid _   <> R_invalid => intros F; invc F
  | |- R_ad _    <> R_invalid => intros F; invc F
  | |- R_ad _    <> R_tid _   => intros F; invc F
  end : core.

Lemma gcr_ad_tid_contradiction : forall tid ad t,
  gcr t (R_ad ad) = R_tid tid ->
  False.
Proof.
  intros * Hgcr. gendep ad.
  induction t; intros; kappa; eauto; invc Hgcr; auto.
Qed.

Lemma gcr_tid1_tid2_contradiction : forall tid1 tid2 t,
  tid1 <> tid2 ->
  gcr t (R_tid tid1) = R_tid tid2 ->
  False.
Proof.
  intros * ? Hgcr.
  induction t; intros; kappa; eauto using gcr_ad_tid_contradiction;
  invc Hgcr; auto.
Qed.

Lemma gcr_invalid_impossibility  : forall t R,
  R <> R_invalid ->
  gcr t R = R_invalid ->
  False.
Proof.
  intros * Hgcr. gendep R.
  induction t; intros; kappa; eauto; try solve [invc Hgcr; auto];
  match goal with ad : addr |- _ => eapply (IHt (R_ad ad)); eauto end.
Qed.

Corollary gcr_tid_invalid_contradiction : forall tid t,
  gcr t (R_tid tid) = R_invalid ->
  False.
Proof.
  intros. eapply (gcr_invalid_impossibility t (R_tid tid)); eauto.
Qed.

Corollary gcr_ad_invalid_contradiction : forall ad t,
  gcr t (R_ad ad) = R_invalid ->
  False.
Proof.
  intros. eapply (gcr_invalid_impossibility t (R_ad ad)); eauto.
Qed.

(* ------------------------------------------------------------------------- *)

(* TODO
Notation "'[[' p1 '..' tc '..' p2 ']]'" := (p2 :: tc ++ p1 :: nil)
  (at level 40).
*)

Local Lemma _destruct_ustep2 : forall tc m1 m3 ths1 ths3 tid e,
  m1 / ths1 ~~[tc ++ (tid, e) :: nil]~~>* m3 / ths3 ->
  (exists m2 ths2,
    m1 / ths1 ~~~[tid, e]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*     m3 / ths3 ).
Proof.
  intros ?. induction tc; intros; invc_ustep.
  - invc_ustep. eauto using multistep.
  - match goal with Hustep : _ / _ ~~[ _ ]~~>* _ / _ |- _ => 
      decompose record (IHtc _ _ _ _ _ _ Hustep); eauto using multistep
    end.
Qed.

Ltac destruct_ustep2 :=
  match goal with
  | H : _ / _  ~~[_ ++ (_, _) :: nil]~~>* _ / _ |- _ =>
    eapply _destruct_ustep2 in H as [? [? [? ?]]]
  end.

Local Lemma _destruct_ustep3 : forall tc m1 m4 ths1 ths4 tid1 tid2 e1 e2,
  m1 / ths1 ~~[(tid2, e2) :: tc ++ (tid1, e1) :: nil]~~>* m4 / ths4 ->
  (exists m2 ths2 m3 ths3,
    m1 / ths1 ~~~[tid1, e1]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*      m3 / ths3 /\
    m3 / ths3 ~~~[tid2, e2]~~> m4 / ths4 ).
Proof.
  intros. invc_ustep. destruct_ustep2. do 4 eexists. repeat split; eauto.
Qed.

Ltac destruct_ustep3 :=
  match goal with 
  | H : _ / _ ~~[(_, _) :: _ ++ (_, _) :: nil]~~>* _ / _ |- _ =>
    eapply _destruct_ustep3 in H
      as [mA [thsA [mB [thsB [H1A [HAB HB2]]]]]]
  end.

Theorem safety_write_read :
  forall m1 m2 ths1 ths2 tc,
  forall tc' tid1 tid2 ad t1 t2,


  forall_threads ths1 (valid_term m1)  ->
  forall_threads ths1 well_typed_term ->
  forall_threads_consistent_regions m1 ths1 ->

  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  tc = (tid2, e_read ad t2) :: tc' ++ (tid1, e_write ad t1) :: nil ->
  False.
Proof.
  intros. subst.
  destruct_ustep3.

  assert (gcr ths1[tid1] (R_tid tid1) = m1[ad].R)
    by eauto using ostep_gcr_write.
  assert (gcr ths2[tid2] (R_tid tid2) = m2[ad].R) by admit.
Qed.


