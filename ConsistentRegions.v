From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

(* ------------------------------------------------------------------------- *)
(* consistent-regions                                                        *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_regions (o : owners) (R : region) : tm -> Prop :=
  | creg_unit  :                 consistent_regions o R <{unit           }>
  | creg_nat   : forall n,       consistent_regions o R <{nat n          }>
  | creg_var   : forall x,       consistent_regions o R <{var x          }>
  | creg_fun   : forall x Tx t,  consistent_regions o R t  ->
                                 consistent_regions o R <{fn x Tx t      }>
  | creg_call  : forall t1 t2,   consistent_regions o R t1 ->
                                 consistent_regions o R t2 ->
                                 consistent_regions o R <{call t1 t2     }>
  | creg_refR  : forall ad T,    consistent_regions o R <{&ad : r&T      }>
  | creg_refX  : forall ad T,    consistent_regions o R <{&ad : x&T      }>
  | creg_refW  : forall ad T,    R = o[ad].R               ->
                                 consistent_regions o R <{&ad : w&T      }>
  | creg_new   : forall t T,     consistent_regions o R t  ->
                                 consistent_regions o R <{new t : T      }>
  | creg_initR : forall ad t T,  consistent_regions o R t  ->
                                 consistent_regions o R <{init ad t : r&T}>
  | creg_initX : forall ad t T,  consistent_regions o (R_ad ad) t ->
                                 consistent_regions o R <{init ad t : x&T}>
  | creg_initW : forall ad t T,  R = o[ad].R               ->
                                 consistent_regions o R t  ->
                                 consistent_regions o R <{init ad t : w&T}>
  | creg_load  : forall t,       consistent_regions o R t  ->
                                 consistent_regions o R <{*t             }>
  | creg_asg   : forall t1 t2,   consistent_regions o R t1 ->
                                 consistent_regions o R t2 ->
                                 consistent_regions o R <{t1 := t2       }>
  | creg_acq   : forall t1 x t2, consistent_regions o R t1 ->
                                 consistent_regions o R t2 ->
                                 consistent_regions o R <{acq t1 x t2    }>
  | creg_cr    : forall ad t,    consistent_regions o (R_ad ad) t ->
                                 consistent_regions o R <{cr ad t        }>
  | creg_spawn : forall t,       consistent_regions o R t  ->
                                 consistent_regions o R <{spawn t        }>
  .

Definition forall_threads_consistent_regions (o : owners) (ths : threads) :=
  forall tid, consistent_regions o (R_tid tid) ths[tid].

Definition forall_memory_consistent_regions (o : owners) (m : mem) :=
  forall ad t,
  m[ad].t = Some t ->
    (forall T, m[ad].T = `r&T` -> no_wrefs t)                       /\
    (forall T, m[ad].T = `x&T` -> consistent_regions o (R_ad ad) t) /\
    (forall T, m[ad].T = `w&T` -> consistent_regions o (o[ad].R) t).

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

Lemma creg_from_nowrefs_noinits : forall Gamma o R t T,
  Gamma |-- t is T ->
  (* --- *)
  no_wrefs t ->
  no_inits t ->
  consistent_regions o R t.
Proof.
  intros. gendep R. gendep T. gendep Gamma.
  induction t; intros; invc_typeof; invc_nowrefs; invc_noinits;
  eauto using consistent_regions.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma creg_subst : forall o R x tx t,
  no_inits t ->
  no_crs   t ->
  consistent_regions o R t ->
  consistent_regions o R tx ->
  consistent_regions o R <{[x := tx] t}>.
Proof.
  intros. induction t; intros; simpl; try destruct _str_eq_dec;
  invc_noinits; invc_nocrs; invc_creg; eauto using consistent_regions.
Qed.

Local Lemma creg_mem_add : forall m o R R' t,
  #o = #m ->
  valid_addresses m t ->
  (* --- *)
  consistent_regions o R t ->
  consistent_regions (o +++ R') R t.
Proof.
  intros. gendep R. induction t; intros;
  invc_vad; invc_creg; constructor; try omicron; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma creg_preservation_none : forall o R t1 t2,
  valid_blocks t1 ->
  (* --- *)
  consistent_regions o R t1 ->
  t1 --[e_none]--> t2 ->
  consistent_regions o R t2.
Proof.
  intros. gendep R.
  ind_tstep; intros; repeat invc_vb; repeat invc_creg;
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

Local Lemma creg_preservation_alloc : forall m o R t1 t2 T,
  #o = #m ->
  well_typed_term t1 ->
  valid_addresses m t1 ->
  valid_blocks t1 ->
  safe_newx t1 ->
  (* --- *)
  consistent_regions o R t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  consistent_regions (o +++ gcr t1 R) R t2.
Proof.
  intros * Hom [T' ?] **. gendep R. gendep T'.
  ind_tstep; intros; invc_typeof; invc_vad; invc_vb; invc_snx; invc_creg;
  try solve [try rewrite <- Hom; constructor; sigma; try omicron;
             simpl; eauto using creg_from_nowrefs_noinits, creg_mem_add];
  constructor; eauto using creg_mem_add.
  - rewrite gcr_call_t1; eauto. intros ?; value_does_not_step.
  - rewrite gcr_call_t2; eauto.
  - rewrite gcr_asg_t1;  eauto. intros ?; value_does_not_step.
  - rewrite gcr_asg_t2;  eauto.
Qed.

Local Lemma creg_preservation_insert : forall o R t1 t2 ad t T,
  consistent_regions o R t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  consistent_regions o R t2.
Proof.
  intros. gendep R. ind_tstep; intros; inv_creg;
  eauto using consistent_regions.
Qed.

Local Lemma creg_preservation_read : forall m o R t1 t2 ad t,
  forall_memory m no_inits ->
  well_typed_term t1 ->
  consistent_references m t1 ->
  forall_memory_consistent_regions o m ->
  (* --- *)
  m[ad].t = Some t ->
  consistent_regions o R t1 ->
  t1 --[e_read ad t]--> t2 ->
  consistent_regions o R t2.
Proof.
  intros * ? [T ?] ? Hfmcr **. gendep R. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_cr; repeat invc_creg;
  eauto using consistent_regions;
  invc_eq; specialize (Hfmcr ad); repeat spec;
  decompose record Hfmcr; eauto using creg_from_nowrefs_noinits.
Qed.

Local Lemma creg_preservation_write : forall o R t1 t2 ad t,
  consistent_regions o R t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_regions o R t2.
Proof.
  intros. gendep R.
  ind_tstep; intros; invc_creg; eauto using consistent_regions.
Qed.

Local Lemma creg_preservation_acq : forall m o R t1 t2 ad t,
  well_typed_term t1 ->
  consistent_references m t1 ->
  valid_blocks t1 ->
  safe_acq t1 ->
  forall_memory_consistent_regions o m ->
  (* --- *)
  m[ad].t = Some t ->
  consistent_regions o R t1 ->
  t1 --[e_acq ad t]--> t2 ->
  consistent_regions o R t2.
Proof.
  intros * [T ?] **. gendep R. gendep T.
  ind_tstep; intros;
  repeat invc_typeof; repeat invc_cr; repeat invc_vb; inv_sacq;
  repeat invc_creg;  eauto using consistent_regions.
  invc_eq.
  decompose record (H3 ad t1 H4).
  eauto using creg_from_nowrefs_noinits, creg_subst, consistent_regions.
Qed.

Local Lemma creg_preservation_rel : forall o R t1 t2 ad,
  valid_blocks t1 ->
  safe_cr t1 ->
  (* --- *)
  consistent_regions o R t1 ->
  t1 --[e_rel ad]--> t2 ->
  consistent_regions o R t2.
Proof.
  intros. gendep R. ind_tstep; intros;
  invc_vb; invc_scr; invc_creg; eauto using consistent_regions.
  match goal with H : exists _, _ |- _ => destruct H end.
  eauto using nowrefs_from_type, noinits_from_value, creg_from_nowrefs_noinits.
Qed.

Local Lemma creg_preservation_spawn : forall o R t1 t2 tid t,
  consistent_regions o R t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistent_regions o R t2.
Proof.
  intros. gendep R.
  ind_tstep; intros; invc_creg; eauto using consistent_regions.
Qed.

Local Corollary creg_preservation_spawned : forall o R t1 t2 tid t,
  well_typed_term t1 ->
  valid_blocks t1 ->
  safe_spawns t1 ->
  (* --- *)
  t1 --[e_spawn tid t]--> t2 ->
  consistent_regions o R t.
Proof.
  intros. assert (well_typed_term t) as [? ?] by eauto using wtt_spawn_term.
  eauto using nowrefs_spawn_term, noinits_spawn_term, creg_from_nowrefs_noinits.
Qed.

Theorem creg_preservation : forall m1 m2 ths1 ths2 o1 o2 tid e,
  forall_memory  m1   no_inits ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 (consistent_references m1) ->
  forall_threads ths1 valid_blocks ->
  forall_threads ths1 safe_newx ->
  forall_threads ths1 safe_acq ->
  forall_threads ths1 safe_cr ->
  forall_threads ths1 safe_spawns ->
  #o1 = #m1 ->
  (* --- *)
  forall_memory_consistent_regions  o1 m1 ->
  forall_threads_consistent_regions o1 ths1 ->
  m1 / ths1 / o1 ~~[tid, e]~~> m2 / ths2 / o2 ->
  forall_threads_consistent_regions o2 ths2.
Proof.
  intros * ? Hcreg ** tid'.
  unfold forall_threads_consistent_regions in Hcreg.
  nat_eq_dec tid' tid.
  - invc_ostep; invc_cstep; try invc_mstep; sigma.
    + eauto using creg_preservation_none.
    + eauto using creg_preservation_alloc.
    + eauto using creg_preservation_insert.
    + eauto using creg_preservation_read.
    + eauto using creg_preservation_write.
    + eauto using creg_preservation_acq.
    + eauto using creg_preservation_rel.
    + eauto using creg_preservation_spawn.
  - invc_ostep; invc_cstep; try invc_mstep; sigma; trivial.
    + eauto using creg_mem_add.
    + omicron; eauto using creg_preservation_spawned, consistent_regions.
Qed.

(* ------------------------------------------------------------------------- *)
(* forall-memory-consistent-regions preservation                             *)
(* ------------------------------------------------------------------------- *)

Ltac destruct_mcreg ad :=
  match goal with
  | Hmcreg : forall_memory_consistent_regions ?o ?m
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

Lemma mcreg_preservation_insertX : forall o R t1 t2 ad t T,
  consistent_regions o R t1 ->
  t1 --[e_insert ad t `x&T`]--> t2 ->
  consistent_regions o (R_ad ad) t.
Proof.
  intros. gendep R. ind_tstep; intros; invc_creg; eauto.
Qed.

Lemma mcreg_preservation_insertW : forall o R t1 t2 ad t T,
  consistent_regions o R t1 ->
  t1 --[e_insert ad t `w&T`]--> t2 ->
  consistent_regions o o[ad].R t.
Proof.
  intros. gendep R. ind_tstep; intros; invc_creg; eauto.
Qed.

Lemma mcreg_preservation_write : forall o R t1 t2 ad t,
  well_typed_term t1 ->
  (* --- *)
  consistent_regions o R t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_regions o o[ad].R t.
Proof.
  intros * [T ?] **. gendep R. gendep T.
  ind_tstep; intros; repeat invc_typeof; repeat invc_creg; eauto.
Qed.

Theorem mcreg_preservation : forall m1 m2 ths1 ths2 o1 o2 tid e,
  forall_memory  m1   (valid_addresses m1) ->
  memory_pointer_types m1 ->
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (consistent_inits m1) ->
  forall_threads ths1 (consistent_references m1) ->
  #o1 = #m1 ->
  (* --- *)
  forall_threads_consistent_regions o1 ths1 ->
  forall_memory_consistent_regions o1 m1 ->
  m1 / ths1 / o1 ~~[tid, e]~~> m2 / ths2 / o2 ->
  forall_memory_consistent_regions o2 m2.
Proof.
  intros until 5. intros Hom ? Hmcreg ? ad t Hsome.
  invc_ostep; invc_cstep; try invc_mstep; auto;
  upsilon; sigma; simpl; auto.
  - assert (ad < #o1) by (erewrite Hom in *; assumption).
    destruct_mpt ad;
    repeat split; intros; try invc_eq;
    destruct_mcreg ad; sigma;
    eauto using creg_mem_add.
  - assert ((exists T', T = `r&T'`) \/
            (exists T', T = `x&T'`) \/
            (exists T', T = `w&T'`))
      as [[T' ?] | [[T' ?] | [T' ?]]]
      by eauto using wtt_insert_type; subst.
    + assert (value t0) by eauto using value_insert_term.
      assert (empty |-- t0 is `Safe T'`)
          by eauto using wtt_typeof_insert_term_R.
      assert (m1[ad0].T = `r&T'`) by eauto using ptyp_for_insert.
      repeat split; intros; try invc_eq; eauto using nowrefs_from_type.
    + assert (value t0) by eauto using value_insert_term.
      assert (empty |-- t0 is T') by eauto using wtt_typeof_insert_term_X.
      assert (m1[ad0].T = `x&T'`) by eauto using ptyp_for_insert.
      repeat split; intros; try invc_eq.
      eauto using mcreg_preservation_insertX.
    + assert (value t0) by eauto using value_insert_term.
      assert (empty |-- t0 is T') by eauto using wtt_typeof_insert_term_W.
      assert (m1[ad0].T = `w&T'`) by eauto using ptyp_for_insert.
      repeat split; intros; try invc_eq.
      eauto using mcreg_preservation_insertW.
  - assert (exists T, m1[ad0].T = `w&T`) as [T ?] by eauto using ptyp_for_write.
    repeat split; intros; try invc_eq.
    eauto using mcreg_preservation_write.
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

Lemma gcr_read_t1 : forall m t1 t2 ad' t' T' o R,
  well_typed_term t1 ->
  consistent_references m t1 ->
  consistent_regions o R t1 ->
  (* --- *)
  m[ad'].T = `w&T'` ->
  m[ad'].t = Some t' ->
  t1 --[e_read ad' t']--> t2 ->
  gcr t1 R = o[ad'].R.
Proof.
  intros * [T ?] **. gendep R. gendep T. ind_tstep; intros;
  repeat invc_typeof; repeat invc_cr; repeat invc_creg; eauto.
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

Lemma gcr_read_t1_term : forall m t1 t2 ad' t' T' o R,
  forall_memory m no_inits ->
  forall_memory m no_crs   ->
  well_typed_term t1 ->
  consistent_references m t1 ->
  consistent_regions o R t1  ->
  (* --- *)
  m[ad'].T = `w&T'` ->
  m[ad'].t = Some t' ->
  t1 --[e_read ad' t']--> t2 ->
  gcr t1 R = gcr t' o[ad'].R.
Proof.
  intros. erewrite gcr_read_t1; eauto. erewrite gcr_read_term; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma gcr_write_t1 : forall t1 t2 ad' t' o R,
  well_typed_term t1 ->
  valid_blocks t1 ->
  consistent_regions o R t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  gcr t1 R = o[ad'].R.
Proof.
  intros * [T ?] **. gendep R. gendep T.
  assert (value t') by eauto using value_write_term.
  ind_tstep; intros; repeat invc_typeof; repeat invc_vb; repeat invc_creg;
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

Lemma gcr_write_term : forall t1 t2 ad' t' R,
  valid_blocks t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  gcr t' R = R.
Proof.
  intros.
  assert (value t') by eauto using value_write_term.
  assert (valid_blocks t') by eauto using vb_write_term.
  rewrite gcr_noinits_nocrs; eauto using noinits_from_value, nocrs_from_value.
Qed.

Lemma gcr_write_t1_term : forall t1 t2 ad' t' o R,
  well_typed_term t1 ->
  valid_blocks t1 ->
  consistent_regions o R t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  gcr t1 R = gcr t' o[ad'].R.
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

