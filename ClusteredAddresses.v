From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import ConsistentRegions.
From Elo Require Import Access.
From Elo Require Import XAccess.

(* ------------------------------------------------------------------------- *)
(* clustered-addresses                                                       *)
(* ------------------------------------------------------------------------- *)

Definition clustered_addresses (m : mem) (o : owners) :=
  forall ad1 ad2 t,
  m[ad1].t = Some t ->
  access ad2 t ->
  o[ad1] or R_invalid = o[ad2] or R_invalid.

(* ------------------------------------------------------------------------- *)
(* clustered-addresses preservation                                          *)
(* ------------------------------------------------------------------------- *)

Local Lemma ca_preservation_insert : forall m o ths tid t ad' t' T',
  #o = #m ->
  forall_threads_consistent_regions o ths ->
  forall_memory_consistent_regions  o m ->
  (* --- *)
  ad' < #m ->
  clustered_addresses m o ->
  ths[tid] --[e_insert ad' t' T']--> t ->
  clustered_addresses m[ad'.t <- t'] o.
Proof.
  intros * ? Hcreg Hmcreg ** ? ? ? ? ?. upsilon; eauto.
  specialize (Hcreg tid). remember (R_tid tid) as R. clear HeqR. gendep R.
  ind_tstep; intros; inv_creg; eauto;

  repeat clean.
  - admit.
  - assert (exists t, m[ad2].t = Some t) as [t Hsome] by admit.
    specialize (Hmcreg ad2 t Hsome) as [? [? ?]].
    admit.
  - repeat invc_creg. repeat clean. eauto.
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
*)
