From Elo Require Import Core.
From Elo Require Import Properties.

Lemma nwacc_alloc : forall m t t' ad te T,
  ad < #m ->
  ~ write_access ad m t ->
  t --[e_alloc (#m) te T]--> t' ->
  ~ write_access ad m t'.
Proof.
  intros. ind_tstep.
  - inv_nwacc. eauto with wacc.
  - inv_nwacc. eauto with wacc.
  - inv_nwacc. eauto with wacc.
  - inv_nwacc. eauto with wacc.
  - inv_nwacc. eauto with wacc.
  - inv_nwacc.
    intros ?.
    eapply H0. clear H0.
    invc H2.
    + Array.simpl_array. simpl in *. inv H5.
    +
  - inv_nwacc. eauto with wacc.
  - inv_nwacc. eauto with wacc.
  - inv_nwacc. eauto with wacc.
  - inv_nwacc. eauto with wacc.
  - inv_nwacc. eauto with wacc.
  - inv_nwacc. eauto with wacc.
Abort.

Lemma nwacc_spawn : forall m t t' te ad,
  ~ write_access ad m t ->
  t --[e_spawn te]--> t' ->
  ~ write_access ad m t'.
Proof.
  intros. ind_tstep; try inv_nwacc; eauto with wacc.
Qed.

Lemma todo : forall m m' ths ths' ad tid e,
  ~ write_access ad m ths[tid] ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  write_access ad m ths'[tid] ->
  exists ad' t, e = e_acq ad' t.
Proof.
  intros * Hnwacc ? Hwacc.
  invc_cstep; Array.simpl_array.
  - contradict Hwacc. eauto using nwacc_spawn.
  - invc_mstep. 
    +
Qed.
