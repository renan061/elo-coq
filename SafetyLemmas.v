From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Multistep.

#[local] Hint Extern 8 =>
  match goal with
  (* _ <> e_rel _ *)
  |                 |- e_none         <> e_rel _    => intros F; invc F
  |                 |- e_alloc  _ _   <> e_rel _    => intros F; invc F
  |                 |- e_insert _ _ _ <> e_rel _    => intros F; invc F
  |                 |- e_read   _ _   <> e_rel _    => intros F; invc F
  |                 |- e_write  _ _   <> e_rel _    => intros F; invc F
  |                 |- e_acq    _ _   <> e_rel _    => intros F; invc F
  |                 |- e_spawn  _ _   <> e_rel _    => intros F; invc F
  | _ : ?ad' <> ?ad |- e_rel    ?ad   <> e_rel ?ad' => intros F; invc F
  (* _ <> e_insert _ _ _ *)
  |                 |- e_none            <> e_insert _ _ _   => intros F; invc F
  |                 |- e_alloc  _ _      <> e_insert _ _ _   => intros F; invc F
  | _ : ?ad' <> ?ad |- e_insert ?ad' _ _ <> e_insert ?ad _ _ => intros F; invc F
  |                 |- e_read   _ _      <> e_insert _ _ _   => intros F; invc F
  |                 |- e_write  _ _      <> e_insert _ _ _   => intros F; invc F
  |                 |- e_acq    _ _      <> e_insert _ _ _   => intros F; invc F
  |                 |- e_spawn  _ _      <> e_insert _ _ _   => intros F; invc F
  | _ : ?ad' <> ?ad |- e_rel    _        <> e_insert _ _ _   => intros F; invc F
  end : core.

(* ------------------------------------------------------------------------- *)
(* one-cr inheritance                                                        *)
(* ------------------------------------------------------------------------- *)

Lemma onecr_inheritance_rstep :
  forall ad m1 m2 ths1 ths2 tid tid' e,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_cr ad ths2[tid] ->
    m1 \ ths1 ~~~[tid', e]~~> m2 \ ths2 ->
    exists t, (e <> e_acq ad t /\ one_cr ad ths1[tid]) \/
              (e =  e_acq ad t /\ tid' = tid).
Proof.
  intros.
  assert (forall_memory m1 value) by eauto with inva.
  assert (forall_memory m1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (valid_term m1)) by eauto with inva.
  assert (unique_critical_regions m1 ths1) by eauto with inva.
  assert (Hucr : unique_critical_regions m2 ths2) by eauto with inva.
  assert (forall_threads ths1 term_init_cr_exc) by eauto with inva.
  assert (H' : forall_threads ths2 term_init_cr_exc) by eauto with inva.
  invc_rstep; invc_cstep; try invc_mstep.
  - exists <{unit}>. left. split. 1: intros F; invc F.
    omicron; eauto using onecr_inheritance_none.
  - exists <{unit}>. left. split. 1: intros F; invc F.
    omicron; eauto using onecr_inheritance_alloc.
  - exists <{unit}>. left. split. 1: intros F; invc F.
    omicron; eauto using onecr_inheritance_insert.
  - exists <{unit}>. left. split. 1: intros F; invc F.
    omicron; eauto using nocrs_from_value, onecr_inheritance_read.
  - exists <{unit}>. left. split. 1: intros F; invc F.
    omicron; eauto using onecr_inheritance_write.
  - exists t.
    match goal with _ : _ --[e_acq ?ad' _]--> _ |- _ => nat_eq_dec ad' ad end.
    + omicron; eauto.
      match goal with _ : _ --[_]--> ?t |- _ =>
        assert (term_init_cr_exc t) by (specialize (H' tid'); sigma; trivial);
        assert (no_cr ad ths1[tid']) by eauto using nocr_from_acq with inva;
        assert (one_cr ad t) by eauto using nocr_to_onecr, nocrs_from_value;
        assert (one_cr ad ths1[tid' <- t][tid']) by (sigma; trivial);
        assert (one_cr ad ths1[tid' <- t][tid])  by (sigma; trivial)
      end.
      exfalso. eauto using ucr_onecr_contradiction.
    + left. split.
      * intros F. invc F. auto.
      * omicron; eauto using nocrs_from_value, onecr_inheritance_acq.
  - exists <{unit}>. left. split. 1: intros F; invc F.
    match goal with _ : _ --[e_rel ?ad']--> _ |- _ => nat_eq_dec ad' ad end;
    omicron; eauto using onecr_inheritance_rel.
    exfalso.
    eauto using onecr_from_rel, onecr_to_nocr, nocr_onecr_contradiction.
  - exists <{unit}>. left. split. 1: intros F; invc F.
    omicron; eauto using onecr_inheritance_spawn.
    exfalso. eauto using nocr_spawn_term, nocr_onecr_contradiction.
Qed.

(* ------------------------------------------------------------------------- *)
(* initialized preservation                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma initialized_preservation_rstep : forall m1 m2 ths1 ths2 tid e ad t,
  m1[ad].t = Some t ->
  m1 \ ths1 ~~~[tid, e]~~> m2 \ ths2 ->
  exists t', m2 [ad].t = Some t'.
Proof.
  intros.
  assert (ad < #m1) by (lt_eq_gt ad (#m1); sigma; upsilon; eauto).
  invc_rstep; invc_cstep; try invc_mstep; sigma; eauto;
  omicron; upsilon; eauto.
Qed.

Lemma initialized_preservation_ustep : forall m1 m2 ths1 ths2 tc ad t,
  m1[ad].t = Some t ->
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  exists t', m2 [ad].t = Some t'.
Proof.
  intros. ind_ustep; eauto.
  destruct IHmultistep; trivial.
  eauto using initialized_preservation_rstep.
Qed.

(* ------------------------------------------------------------------------- *)
(* one-init preservation                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma oneinit_preservation_rstep :
  forall ad m1 m2 ths1 ths2 tid tid' e,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_init ad ths1[tid] ->
    m1 \ ths1 ~~~[tid', e]~~> m2 \ ths2 ->
     (forall t T, e <> e_insert ad t T /\ one_init ad ths2[tid]) \/
     (exists t T, e =  e_insert ad t T /\ tid' = tid /\ m2[ad].t = Some t).
Proof.
  intros.
  assert (forall_memory m1 value) by eauto with inva.
  assert (forall_memory m1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (consistent_term m1)) by eauto with inva.
  assert (unique_initializers m1 ths1) by eauto with inva.
  invc_rstep; invc_cstep; try invc_mstep.
  - left. intros. split; auto.
    omicron; eauto using oneinit_preservation_none.
  - left. split; try omicron; auto.
    assert (ad < #m1) by eauto using oneinit_ad_bound.
    eauto using oneinit_preservation_alloc.
  - match goal with _ : _ --[e_insert ?ad _ _]--> _ |- _ =>
      rename ad into ad'
    end.
    nat_eq_dec ad' ad.
    + assert (ad < #m1) by eauto using vtm_insert_address.
      right. repeat eexists; sigma; upsilon; trivial.
      eauto using oneinit_from_insert, ui_oneinit_equality.
    + left. intros. split; auto.
      omicron; eauto using oneinit_preservation_insert.
  - left. split; auto.
    omicron; eauto using noinits_from_value, oneinit_preservation_read.
  - left. split; auto.
    omicron; eauto using oneinit_preservation_write.
  - left. split; auto.
    omicron; eauto using noinits_from_value, oneinit_preservation_acq.
  - left. split; auto.
    omicron; eauto using oneinit_preservation_rel.
  - left. split; auto.
    omicron; eauto using oneinit_preservation_spawn.
    invc_oneinit.
Qed.

Lemma oneinit_preservation_ustep :
  forall tc m1 m2 ths1 ths2 ad tid,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_init ad ths1[tid] ->
    m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
    one_init ad ths2[tid] \/ exists t, m2[ad].t = Some t.
Proof.
  intros. ind_ustep; auto.
  match goal with _ : ?m \ ?ths ~~~[?tid, _]~~> ?m' \ ?ths' |- _ =>
    rename tid into tid';
    rename m' into m3; rename ths' into ths3;
    rename m  into m2; rename ths  into ths2
  end.
  assert (invariants m2 ths2) by eauto using invariants_preservation_ustep.
  destruct IHmultistep as [? | [? ?]]; trivial.
  - assert (
      (forall t T, e <> e_insert ad t T /\ one_init ad ths3[tid]) \/
      (exists t T, e =  e_insert ad t T /\ tid' = tid /\ m3[ad].t = Some t)
    ) as [H' | [t' [T' [? [? ?]]]]]
      by eauto using oneinit_preservation_rstep.
    + specialize (H' <{unit}> `Unit`) as [? ?]. eauto.
    + subst. eauto.
  - right. eauto using initialized_preservation_rstep.
Qed.

(* ------------------------------------------------------------------------- *)
(* one-cr preservation                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma onecr_preservation_rstep :
  forall ad m1 m2 ths1 ths2 tid tid' e,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_cr ad ths1[tid] ->
    m1 \ ths1 ~~~[tid', e]~~> m2 \ ths2 ->
    (e <> e_rel ad /\ one_cr ad ths2[tid]) \/
    (e =  e_rel ad /\ tid' = tid).
Proof.
  intros.
  assert (forall_memory m1 value) by eauto with inva.
  assert (forall_memory m1 (valid_term m1)) by eauto with inva.
  assert (forall_threads ths1 (valid_term m1)) by eauto with inva.
  assert (unique_critical_regions m1 ths1) by eauto with inva.
  invc_rstep; invc_cstep; try invc_mstep.
  - left. split; auto.
    omicron; eauto using onecr_preservation_none.
  - left. split; auto.
    omicron; eauto using onecr_preservation_alloc.
  - left. split; auto.
    omicron; eauto using onecr_preservation_insert.
  - left. split; auto.
    omicron; eauto using nocrs_from_value, onecr_preservation_read.
  - left. split; auto.
    omicron; eauto using onecr_preservation_write.
  - left. split; auto.
    match goal with _ : _ --[e_acq ?ad ?t]--> _ |- _ =>
        rename ad into ad'; rename t into t'
    end.
    nat_eq_dec ad ad'; omicron; auto.
    + assert (Htrue : m1[ad'].X = true) by eauto using locked_from_onecr.
      rewrite Htrue in *. auto.
    + eauto 6 using nocr_from_nocrs, nocrs_from_value, onecr_preservation_acq.
  - match goal with _ : _ --[e_rel ?ad]--> _ |- _ => rename ad into ad' end.
    nat_eq_dec ad ad'.
    + right. split; eauto using onecr_from_rel, ucr_onecr_equality.
    + left; split; try omicron; eauto using onecr_preservation_rel.
  - left. split; auto.
    omicron; eauto using onecr_preservation_spawn.
    invc_onecr.
Qed.

