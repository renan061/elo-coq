From Elo Require Import Core.

From Elo Require Import Properties1.
From Elo Require Import Properties2.

From Elo Require Import SafeNewX.

From Elo Require Import AccessCore.

(* ------------------------------------------------------------------------- *)
(* consistent-regions                                                        *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_regions (o : owners) : owner -> tm -> Prop :=
  | creg_unit  : forall O,        consistent_regions o O <{unit           }>
  | creg_nat   : forall O n,      consistent_regions o O <{nat n          }>
  | creg_var   : forall O x,      consistent_regions o O <{var x          }>
  | creg_fun   : forall O x Tx t, consistent_regions o O t  ->
                                  consistent_regions o O <{fn x Tx t      }>
  | creg_call  : forall O t1 t2,  consistent_regions o O t1 ->
                                  consistent_regions o O t2 ->
                                  consistent_regions o O <{call t1 t2     }>
  | creg_refR  : forall O ad T,   consistent_regions o O <{&ad : r&T      }>
  | creg_refX  : forall O ad T,   consistent_regions o O <{&ad : x&T      }>
  | creg_refW  : forall O ad T,   O = o[ad] or o_none       ->
                                  consistent_regions o O <{&ad : w&T      }>
  | creg_new   : forall O t T,    consistent_regions o O t  ->
                                  consistent_regions o O <{new t : T      }>
  | creg_initR : forall O ad t T, consistent_regions o O t  ->
                                  consistent_regions o O <{init ad t : r&T}>
  | creg_initX : forall O ad t T, consistent_regions o (o_monitor ad) t ->
                                  consistent_regions o O <{init ad t : x&T}>
  | creg_initW : forall O ad t T, consistent_regions o O t  ->
                                  consistent_regions o O <{init ad t : w&T}>
  | creg_load  : forall O t,      consistent_regions o O t  ->
                                  consistent_regions o O <{*t             }>
  | creg_asg   : forall O t1 t2,  consistent_regions o O t1 ->
                                  consistent_regions o O t2 ->
                                  consistent_regions o O <{t1 := t2       }>
  | creg_acq   : forall O t1 t2,  consistent_regions o O t1 ->
                                  consistent_regions o O t2 ->
                                  consistent_regions o O <{acq t1 t2      }>
  | creg_cr    : forall O ad t,   consistent_regions o (o_monitor ad) t ->
                                  consistent_regions o O <{cr ad t        }>
  | creg_spawn : forall O t,      consistent_regions o O t  ->
                                  consistent_regions o O <{spawn t        }>
  .

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
  | H : consistent_regions _ _ <{acq _ _     }> |- _ => tt H
  | H : consistent_regions _ _ <{cr _ _      }> |- _ => tt H
  | H : consistent_regions _ _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_creg  := _creg inv.
Ltac invc_creg := _creg invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma creg_from_nowrefs : forall o O t,
  well_typed_term t ->
  (* --- *)
  no_wrefs t ->
  consistent_regions o O t.
Proof.
  intros * [T ?] **.
  remember empty as Gamma. clear HeqGamma.
  gendep O. gendep T. gendep Gamma.
  induction t; intros; invc_typeof; invc_nowrefs;
  eauto using consistent_regions.
Qed.

(* ------------------------------------------------------------------------- *)
(* forall-threads consistent-regions                                         *)
(* ------------------------------------------------------------------------- *)

Definition forall_threads_consistent_regions (o : owners) (ths : threads) :=
  forall tid, consistent_regions o (o_thread tid) ths[tid].

(* ------------------------------------------------------------------------- *)
(* clustered-addresses                                                       *)
(* ------------------------------------------------------------------------- *)

Definition clustered_addresses (m : mem) (o : owners) :=
  forall ad1 ad2 t,
  m[ad1].t = Some t ->
  access ad2 t ->
  o[ad1] or o_none = o[ad2] or o_none.

(* ------------------------------------------------------------------------- *)
(* consistent-regions preservation                                           *)
(* ------------------------------------------------------------------------- *)

Local Lemma creg_subst : forall o O x tx t,
  no_inits t ->
  no_crs   t ->
  consistent_regions o O t ->
  consistent_regions o O tx ->
  consistent_regions o O <{[x := tx] t}>.
Proof.
  intros. induction t; intros; simpl; try destruct str_eq_dec;
  invc_noinits; invc_nocrs; invc_creg; eauto using consistent_regions.
Qed.

Local Lemma creg_mem_add : forall m o O O' t,
  #o = #m ->
  valid_addresses m t ->
  (* --- *)
  consistent_regions o O t ->
  consistent_regions (o +++ O') O t.
Proof.
  intros. gendep O. induction t; intros;
  invc_vad; invc_creg; constructor; try omicron; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma creg_preservation_none : forall o O t1 t2,
  valid_blocks t1 ->
  (* --- *)
  consistent_regions o O t1 ->
  t1 --[e_none]--> t2 ->
  consistent_regions o O t2.
Proof.
  intros. gendep O.
  ind_tstep; intros; repeat invc_vb; repeat invc_creg;
  eauto using creg_subst, consistent_regions.
Qed.

Local Lemma creg_preservation_alloc : forall m o r tid O t1 t2 T,
  #o = #m ->
  well_typed_term t1 ->
  valid_addresses m t1 ->
  safe_newx t1 ->
  (* --- *)
  consistent_regions o O t1 ->
  t1 --[e_alloc (#m) T]--> t2 ->
  consistent_regions (o +++ regions_peek r tid) O t2.
Proof.
  intros * ? Hwtt **.
  assert (Hwtt' := Hwtt). specialize Hwtt' as [T' ?].
  gendep O. gendep T'.
  ind_tstep; intros; invc_wtt; invc_typeof; invc_vad; invc_snx; invc_creg;
  eauto using creg_from_nowrefs, creg_mem_add, consistent_regions.
Qed.

Local Lemma creg_preservation_insert : forall o O t1 t2 ad t,
  consistent_regions o O t1 ->
  t1 --[e_insert ad t]--> t2 ->
  consistent_regions o O t2.
Proof.
  intros. gendep O. ind_tstep; intros;
  invc_creg; eauto using consistent_regions.
  constructor.
Abort.

Local Lemma creg_preservation_read : forall o O t1 t2 ad t,
  consistent_regions o O t1 ->
  t1 --[e_read ad t]--> t2 ->
  consistent_regions o O t2.
Proof.
  intros. gendep O.
  ind_tstep; intros; invc_creg; eauto using consistent_regions.
Abort.

Local Lemma creg_preservation_write : forall o O t1 t2 ad t,
  consistent_regions o O t1 ->
  t1 --[e_write ad t]--> t2 ->
  consistent_regions o O t2.
Proof.
  intros. gendep O.
  ind_tstep; intros; invc_creg; eauto using consistent_regions.
Qed.

(*
  | T_acq : forall Gamma t1 t2 T1 T2,
    Gamma |-- t1 is `x&T1` ->
    safe Gamma |-- t2 is `T1 --> Safe T2` ->
    Gamma |-- <{acq t1 t2}> is `Safe T2`
*)

Local Lemma creg_preservation_acq : forall m o O t1 t2 ad t,
  well_typed_term t1 ->
  consistent_references m t1 ->
  (* --- *)
  m[ad].t = Some t ->
  consistent_regions o O t1 ->
  t1 --[e_acq ad t]--> t2 ->
  consistent_regions o O t2.
Proof.
  intros * [T ?] **. gendep O. gendep T.
  ind_tstep; intros;
  invc_typeof; invc_cr; invc_creg; eauto using consistent_regions.
  do 2 invc_typeof. do 2 invc_creg.
  constructor.
Abort.

Local Lemma creg_preservation_rel : forall o O t1 t2 ad,
  consistent_regions o O t1 ->
  t1 --[e_rel ad]--> t2 ->
  consistent_regions o O t2.
Proof.
  intros. gendep O.
  ind_tstep; intros; invc_creg; eauto using consistent_regions.
Abort.

Local Lemma creg_preservation_spawn : forall o O t1 t2 tid t,
  consistent_regions o O t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  consistent_regions o O t2.
Proof.
  intros. gendep O.
  ind_tstep; intros; invc_creg; eauto using consistent_regions.
Qed.

Local Corollary creg_preservation_spawned : forall o O t1 t2 tid t,
  well_typed_term t1 ->
  valid_spawns t1 ->
  (* --- *)
  t1 --[e_spawn tid t]--> t2 ->
  consistent_regions o O t.
Proof.
  eauto using wtt_spawn_term, nowrefs_spawn_term, creg_from_nowrefs.
Qed.

Theorem creg_preservation : forall m1 m2 ths1 ths2 o1 o2 r1 r2 tid e,
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (valid_addresses m1) ->
  forall_threads ths1 valid_blocks ->
  forall_threads ths1 valid_spawns ->
  forall_threads ths1 safe_newx ->
  #o1 = #m1 ->
  (* --- *)
  forall_threads_consistent_regions o1 ths1 ->
  m1 / ths1 / o1 / r1 ~~[tid, e]~~> m2 / ths2 / o2 / r2 ->
  forall_threads_consistent_regions o2 ths2.
Proof.
  intros * ? Hcreg ** tid'. unfold forall_threads_consistent_regions in Hcreg.
  destruct (nat_eq_dec tid' tid); subst.
  - invc_ostep; invc_cstep; try invc_mstep; sigma.
    + eauto using creg_preservation_none.
    + eauto using creg_preservation_alloc.
    + admit.
    + admit.
    + eauto using creg_preservation_write.
    + admit.
    + admit.
    + eauto using creg_preservation_spawn.
  - invc_ostep; invc_cstep; try invc_mstep; sigma; trivial.
    + admit.
    + omicron; eauto using creg_preservation_spawned, consistent_regions.
Abort.

(* ------------------------------------------------------------------------- *)
(* clustered-addresses preservation                                          *)
(* ------------------------------------------------------------------------- *)

Local Lemma ca_preservation_insert : forall m o ths tid t ad' t',
  #o = #m ->
  (* --- *)
  ad' < #m ->
  clustered_addresses m o ->
  ths[tid] --[e_insert ad' t']--> t ->
  clustered_addresses m[ad'.t <- t'] o.
Proof.
  intros ** ? **. upsilon; eauto.
Abort.

Local Lemma ca_preservation_write : forall m o ths tid t ad' t',
  #o = #m ->
  (* --- *)
  ad' < #m ->
  clustered_addresses m o ->
  ths[tid] --[e_write ad' t']--> t ->
  clustered_addresses m[ad'.t <- t'] o.
Proof.
  intros ** ? **. upsilon; eauto.
Abort.

Theorem ca_preservation : forall m1 m2 ths1 ths2 o1 o2 r1 r2 tid e,
  forall_memory m1 (valid_addresses m1) ->
  #o1 = #m1 ->
  (* --- *)
  clustered_addresses m1 o1 ->
  m1 / ths1 / o1 / r1 ~~[tid, e]~~> m2 / ths2 / o2 / r2 ->
  clustered_addresses m2 o2.
Proof.
  intros * ? Hsmo **.
  invc_ostep; invc_cstep; try invc_mstep; trivial.
  - intros ? **. upsilon.
    repeat omicron; eauto; exfalso; rewrite Hsmo in *; sigma; upsilon;
    eauto using acc_vad_contradiction1, acc_vad_contradiction2.
  - admit.
  - admit.
  - intros ? **. upsilon; eauto.
  - intros ? **. upsilon; eauto.
Abort.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Theorem omlen_preservation : forall m1 m2 ths1 ths2 o1 o2 r1 r2 tid e,
  #o1 = #m1 ->
  m1 / ths1 / o1 / r1 ~~[tid, e]~~> m2 / ths2 / o2 / r2 ->
  #o2 = #m2.
Proof.
  intros. invc_ostep; invc_cstep; try invc_mstep; sigma; auto.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

(*

Se:
  ths[tid] --[insert ad _]--> _
Ou:
  ths[tid] --[write  ad _]--> _
Então:
  A região em que tid está é igual ao dono de ad.

Se:
  access ad ths[tid]
Então:
  tid é owner de ad

Se:
  xaccess adx ad ths[tid]
Então:
  adx é owner de ad

Se:
  adx é owner de ad
Então:
  forall tid, ~ access ad ths[tid]

Se:
  tid é owner de ad
Então:
  forall tid', tid <> tid' -> ~ access ad ths[tid]

Se:
  tid é owner de ad
Então:
  forall adx tid', ~ xaccess adx ad ths[tid]

*)
