From Elo Require Import Core.
From Elo Require Import Properties.

Lemma read_requires_acc : forall m m' ths ths' tid ad v,
  m / ths ~~[tid, EF_Read ad v]~~> m' / ths' ->
  access ad m ths[tid].
Proof.
  intros. invc_cstep. invc_mstep. induction_tstep; eauto using access.
Qed.

Lemma write_requires_uacc : forall m m' ths ths' tid ad v Tr,
  well_typed_term ths[tid] ->
  m / ths ~~[tid, EF_Write ad v Tr]~~> m' / ths' ->
  unsafe_access ad m ths[tid].
Proof.
  intros * [T ?] **.
  invc_cstep. invc_mstep. generalize dependent T.
  induction_tstep; intros; inv_type; eauto using unsafe_access.
  inv_type. eauto using unsafe_access.
Qed.

Lemma spawn_nuacc : forall m t t' block ad,
  safe_spawns t ->
  t --[EF_Spawn block]--> t' ->
  ~ unsafe_access ad m block.
Proof.
  intros. induction_tstep; invc_ss; eauto.
  intros Huacc. match goal with Hnm : no_mut _ |- _ => induction Hnm end;
  inv_uacc; eauto.
Qed.

Lemma consistently_typed_write_effect : forall m t t' ad v T,
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  t --[EF_Write ad v T]--> t' ->
  exists Tv, T = <{{&Tv}}>
          /\ empty |-- v is Tv
          /\ empty |-- m[ad].tm is Tv
          /\ m[ad].typ = <{{&Tv}}>.
Proof.
  intros * Hwtt **. inversion Hwtt as [T' ?].
  clear Hwtt. generalize dependent T'.
  induction_tstep; intros; inv_type; inv_ctr; eauto.
  inv_type. inv_ctr. eauto.
Qed.

Lemma nacc_vad_length : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ access (#m) m t.
Proof.
  intros * ? Hvad Hacc. induction Hacc; inv_vad; eauto.
Qed.

Corollary nuacc_vad_length : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ unsafe_access (#m) m t.
Proof.
  eauto using nacc_then_nuacc, nacc_vad_length.
Qed.

Lemma vad_acc : forall m t ad,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  access ad m t ->
  ad < #m.
Proof.
  intros * ? ? Hacc. induction Hacc; inv_vad; eauto.
Qed.

