From Elo Require Import Core.
From Elo Require Import Properties.

(* ------------------------------------------------------------------------- *)
(* ptyp preservation                                                         *)
(* ------------------------------------------------------------------------- *)

Theorem ptyp_cstep_preservation : forall m m' ths ths' tid e ad,
  consistently_typed_references m ths[tid] ->
  (* --- *)
  ad < #m ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  m[ad].typ = m'[ad].typ.
Proof.
  intros. invc_cstep; trivial. invc_mstep; trivial.
  - simpl_array. trivial.
  - match goal with |- _ = (_[?ad' <- _])[_].typ =>
      destruct (nat_eq_dec ad ad'); subst
    end;
    simpl_array; trivial.
    induction_tstep; inv_ctr; eauto. inv_ctr; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* ptyp & uacc/sacc                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma ptyp_mut_iff_uacc : forall m t ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  (* --- *)
  access ad m t ->
  unsafe_access ad m t <-> (exists T, m[ad].typ = <{{&T}}>).
Proof.
  intros * ? Hmctr ? Hacc. split.
  - intros Huacc. clear Hacc. induction Huacc; inv_ctr; eauto.
  - intros [? Heq]. induction Hacc; inv_ctr; eauto using unsafe_access.
    + exfalso. eapply nuacc_from_immutable_type; eauto.
    + rewrite Heq in *. discriminate.
Qed.

Corollary uacc_by_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  consistently_typed_references m t' ->
  (* --- *)
  access ad m t ->
  unsafe_access ad m t' ->
  unsafe_access ad m t.
Proof.
  intros.
  eapply ptyp_mut_iff_uacc; eauto.
  eapply ptyp_mut_iff_uacc; eauto using uacc_then_acc.
Qed.

Lemma ptyp_immut_iff_sacc : forall m t ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  (* --- *)
  access ad m t ->
  safe_access ad m t <-> (exists T, m[ad].typ = <{{i&T}}>).
Proof.
  intros * Hval ? ? Hacc. split; intros [? Hx].
  - induction Hacc; inv_ctr; inv_nuacc; eauto.
  - split; trivial.
    induction Hacc; intros ?; invc_ctr; inv_uacc; eauto;
    try (eapply IHHacc; eauto using uacc_by_association).
    rewrite Hx in *. discriminate.
Qed.

Corollary sacc_by_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  consistently_typed_references m t' ->
  (* --- *)
  access ad m t ->
  safe_access ad m t' ->
  safe_access ad m t.
Proof.
  intros * ? ? ? ? ? Hsacc.
  eapply ptyp_immut_iff_sacc; eauto.
  specialize Hsacc as Hsacc'. destruct Hsacc' as [? ?].
  eapply ptyp_immut_iff_sacc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* ptyp sacc-uacc-contradiction                                              *)
(* ------------------------------------------------------------------------- *)

Lemma ptyp_sacc_uacc_contradiction : forall m1 m2 t1 t2 ad,
  forall_memory m1 value ->
  forall_memory m2 value ->
  forall_memory m1 (consistently_typed_references m1) ->
  forall_memory m2 (consistently_typed_references m2) ->
  consistently_typed_references m1 t1 ->
  consistently_typed_references m2 t2 ->
  (* --- *)
  m1[ad].typ = m2[ad].typ ->
  safe_access ad m1 t1 ->
  unsafe_access ad m2 t2 ->
  False.
Proof.
  intros * ? ? ? ? ? ? Heq Hsacc Huacc.
  eapply ptyp_immut_iff_sacc in Hsacc as [? Htyp1]; eauto using sacc_then_acc.
  eapply ptyp_mut_iff_uacc   in Huacc as [? Htyp2]; eauto using uacc_then_acc.
  rewrite Htyp1 in Heq. rewrite Htyp2 in Heq. discriminate.
Qed.

