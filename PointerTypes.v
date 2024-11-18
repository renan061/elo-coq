From Elo Require Import Core.

From Elo Require Import Properties.

From Elo Require Import AccessCore.

(* ------------------------------------------------------------------------- *)
(* pointer types                                                             *)
(* ------------------------------------------------------------------------- *)

Theorem ptyp_preservation : forall m1 m2 ths1 ths2 tid e ad,
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  ad < #m1 ->
  m1[ad].T = m2[ad].T.
Proof.
  intros. invc_cstep; trivial. invc_mstep; sigma; trivial; omicron; trivial.
Qed.

Lemma ptyp_wacc_correlation : forall m t ad,
  forall_memory m value ->
  forall_memory m (consistent_references m) ->
  consistent_references m t ->
  (* --- *)
  access ad m t ->
  write_access ad m t <-> (exists T, m[ad].T = `w&T`).
Proof.
  intros * ? ? ? Hacc. split.
  - intros Hwacc. clear Hacc. induction Hwacc; invc_cr; eauto.
  - intros [? ?]. induction Hacc; invc_cr; eauto using write_access;
    invc_eq. exfalso. eauto using wacc_safe_contradiction.
Qed.

Corollary wacc_by_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (consistent_references m) ->
  consistent_references m t ->
  consistent_references m t' ->
  (* --- *)
  access ad m t ->
  write_access ad m t' ->
  write_access ad m t.
Proof.
  intros.
  eapply ptyp_wacc_correlation; eauto.
  eapply ptyp_wacc_correlation; eauto using wacc_then_acc.
Qed.

(*
Lemma ptyp_racc_correlation : forall m t ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  access ad m t ->
  read_access ad m t <-> (exists T, m[ad].T = `r&T`).
Proof.
  intros * Hval ? ? Hacc. split; intros [? ?].
  - induction Hacc; invc_vr; invc_nwacc; eauto using safe_then_nwacc.
  - split; trivial. induction Hacc; intros ?; invc_vr; inv_wacc; eauto;
    eapply IHHacc; eauto using wacc_by_association.
Qed.

Corollary racc_by_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t ->
  valid_references m t' ->
  (* --- *)
  access ad m t ->
  read_access ad m t' ->
  read_access ad m t.
Proof.
  intros * ? ? ? ? ? Hracc.
  eapply ptyp_racc_correlation; eauto.
  duplicate Hracc Hracc'. destruct Hracc' as [? ?].
  eapply ptyp_racc_correlation; eauto.
Qed.

Theorem ptyp_racc_wacc_contradiction : forall m1 m2 t1 t2 ad,
  forall_memory m1 value ->
  forall_memory m2 value ->
  forall_memory m1 (valid_references m1) ->
  forall_memory m2 (valid_references m2) ->
  valid_references m1 t1 ->
  valid_references m2 t2 ->
  (* --- *)
  m1[ad].T = m2[ad].T ->
  read_access  ad m1 t1 ->
  write_access ad m2 t2 ->
  False.
Proof.
  intros until 7. intros Hracc Hwacc.
  eapply ptyp_racc_correlation in Hracc as [? Htyp1];
  eauto using racc_then_acc.
  eapply ptyp_wacc_correlation in Hwacc as [? Htyp2];
  eauto using wacc_then_acc.
  rewrite Htyp1 in *. rewrite Htyp2 in *. discriminate.
Qed.
*)
