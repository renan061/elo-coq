From Elo Require Import Core.
From Elo Require Import Properties.

Lemma consistently_typed_write_effect : forall m t t' ad v T,
  valid_addresses m t ->
  well_typed_term t ->
  consistently_typed_references m t ->
  (* --- *)
  t --[EF_Write ad v T]--> t' ->
  exists Tv, T = <{{&Tv}}>
          /\ empty |-- v is Tv
          /\ empty |-- m[ad].tm is Tv
          /\ m[ad].typ = <{{&Tv}}>.
Proof.
  intros * ? Hwtt **. inversion Hwtt as [T' ?].
  clear Hwtt. generalize dependent T'.
  induction_tstep; intros; inv_vad; inv_type; inv_ctr; eauto.
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

Lemma nomut_block : forall t t' block,
  safe_spawns t ->
  t --[EF_Spawn block]--> t' ->
  no_mut block.
Proof.
  intros. induction_tstep; inv_ss; eauto.
Qed.

Lemma nomut_then_nuacc: forall m t ad,
  no_mut t ->
  unsafe_access ad m t ->
  False.
Proof.
  intros * Hnm Huacc. induction Hnm; inv_uacc; eauto.
Qed.

Theorem nuacc_spawn_block : forall m t t' block ad,
  safe_spawns t ->
  t --[EF_Spawn block]--> t' ->
  ~ unsafe_access ad m block.
Proof.
  eauto using nomut_block, nomut_then_nuacc.
Qed.
