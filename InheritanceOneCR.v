From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Multistep.

Lemma onecr_inheritance_rstep :
  forall ad m1 m2 ths1 ths2 tid tid' e,
    invariants m1 ths1 ->
    invariants m2 ths2 ->
    (* --- *)
    one_cr ad ths2[tid] ->
    m1 / ths1 ~~~[tid', e]~~> m2 / ths2 ->
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
  invc_ostep; invc_cstep; try invc_mstep.
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




