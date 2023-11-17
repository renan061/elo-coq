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
  intros * ? Hvad Hacc. remember (#m) as ad.
  induction Hacc; inv_vad; eauto. rewrite Heqad in *. eauto.
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

