From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

(* TODO: remove this and try to use discriminate *)
#[export] Hint Extern 8 =>
  match goal with
  | |- R_invalid <> R_tid     _ => intros F; invc F
  | |- R_invalid <> R_ad      _ => intros F; invc F
  | |- R_invalid <> R_reacq   _ => intros F; invc F
  | |- R_tid   _ <> R_ad      _ => intros F; invc F
  | |- R_tid   _ <> R_invalid   => intros F; invc F
  | |- R_tid   _ <> R_reacq   _ => intros F; invc F
  | |- R_ad    _ <> R_invalid   => intros F; invc F
  | |- R_ad    _ <> R_tid     _ => intros F; invc F
  | |- R_ad    _ <> R_reacq   _ => intros F; invc F
  | |- R_reacq _ <> R_invalid   => intros F; invc F
  | |- R_reacq _ <> R_tid     _ => intros F; invc F
  | |- R_reacq _ <> R_ad      _ => intros F; invc F
  end : gcr.

(* ------------------------------------------------------------------------- *)
(* gcr-noinit(s)-nocr(s)-noreacq(s)                                          *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_noinits_nocrs_noreacqs : forall t R,
  no_inits  t ->
  no_crs    t ->
  no_reacqs t ->
  gcr t R = R.
Proof.
  intros. induction t; invc_noinits; invc_nocrs; invc_noreacqs;
  simpl; auto; destruct (is_value t1); auto.
Qed.

Lemma gcr_noinit_nocr_noreacq1 : forall ad t R,
  no_init  ad t     ->
  no_cr    ad t     ->
  no_reacq ad t     ->
  gcr t R = R_ad ad ->
  R = R_ad ad.
Proof.
  intros. gendep R. induction t; intros;
  invc_noinit; invc_nocr; invc_noreacq; kappa; auto; try discriminate;
  do 3 spec; match goal with _ : ?ad' <> ?ad |- _ = R_ad ?ad' =>
    specialize (IHt (R_ad ad)); spec
  end;
  congruence.
Qed.

Lemma gcr_noinit_nocr_noreacq2 : forall ad t R,
  no_init  ad t        ->
  no_cr    ad t        ->
  no_reacq ad t        ->
  gcr t R = R_reacq ad ->
  R = R_reacq ad.
Proof.
  intros. gendep R. induction t; intros;
  invc_noinit; invc_nocr; invc_noreacq; kappa; auto; try congruence;
  do 3 spec; match goal with _ : ?ad' <> ?ad |- _ = R_reacq ?ad' =>
    specialize (IHt (R_ad ad)); spec
  end;
  congruence.
Qed.

(* ------------------------------------------------------------------------- *)
(* gcr-value                                                                 *)
(* ------------------------------------------------------------------------- *)

Corollary gcr_value : forall m t R,
  valid_term m t ->
  (* --- *)
  value t ->
  gcr t R = R.
Proof.
  eauto using gcr_noinits_nocrs_noreacqs,
    noinits_from_value, nocrs_from_value, noreacqs_from_value.
Qed.

(* ------------------------------------------------------------------------- *)
(* gcr-read & gcr-write                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_read : forall m t1 t2 ad' t' T' R,
  consistent_term m t1      ->
  consistent_regions m R t1 ->
  (* --- *)
  m[ad'].T = `w&T'`          ->
  t1 --[e_read ad' t']--> t2 ->
  gcr t1 R = m[ad'].R.
Proof.
  intros. gendep R. ind_tstep; intros;
  repeat invc_ctm; repeat invc_creg; kappa; auto; value_does_not_step.
Qed.

Lemma gcr_write : forall m t1 t2 ad' t' R,
  valid_term m t1           ->
  well_typed_term t1        ->
  consistent_regions m R t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  gcr t1 R = m[ad'].R.
Proof.
  intros * ? [T ?] **. gendep R. gendep T.
  assert (value t') by eauto using value_write_term.
  ind_tstep; intros; repeat invc_vtm; repeat invc_typeof; repeat invc_creg;
  kappa; eauto; try value_does_not_step; eauto using gcr_value.
Qed.

Corollary cstep_gcr_read : forall m1 m2 ths1 ths2 tid ad' t' T',
  forall_threads ths1 (consistent_term m1)  ->
  forall_threads_consistent_regions m1 ths1 ->
  (* --- *)
  m1[ad'].T = `w&T'`                            ->
  m1 \ ths1 ~~[tid, e_read ad' t']~~> m2 \ ths2 ->
  gcr ths1[tid] (R_tid tid) = m1[ad'].R.
Proof.
  intros. invc_cstep. invc_mstep. eauto using gcr_read.
Qed.

Corollary cstep_gcr_write : forall m1 m2 ths1 ths2 tid ad' t',
  forall_threads ths1 well_typed_term       ->
  forall_threads ths1 (valid_term m1)       ->
  forall_threads_consistent_regions m1 ths1 ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  gcr ths1[tid] (R_tid tid) = m1[ad'].R.
Proof.
  intros. invc_cstep. invc_mstep. eauto using gcr_write.
Qed.

(* ------------------------------------------------------------------------- *)
(* oneinit-or-onecr                                                          *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Extern 8 =>
  match goal with _ : no_init ?ad ?t, _ : no_cr ?ad ?t |- _ =>
    match goal with
    (* --- *)
    | F : gcr ?t (R_tid ?tid) = R_ad ?ad |- _ =>
      apply (gcr_noinit_nocr_noreacq1 ad  t (R_tid tid)) in F; trivial; invc F
    (* --- *)
    | F : gcr ?t (R_ad  ?ad1) = R_ad ?ad2, _ : ?ad2 <> ?ad1 |- _ =>
      apply (gcr_noinit_nocr_noreacq1 ad2 t (R_ad ad1))  in F; trivial; invc F
    end
  end : gcr.

Local Corollary oneinit_or_onecr_contradiction : forall ad t,
  no_init  ad t                ->
  no_cr    ad t                ->
  one_init ad t \/ one_cr ad t ->
  False.
Proof.
  intros * ? ? [? | ?];
  eauto using noinit_oneinit_contradiction, nocr_onecr_contradiction.
Qed.

Lemma oneinit_or_onecr_from_gcr : forall tid ad t,
  consistent_waits WR_none t ->
  term_init_cr_exc t         ->
  (* --- *)
  gcr t (R_tid tid) = R_ad ad ->
  (one_init ad t \/ one_cr ad t).
Proof.
  intros * ? Hregexc Hgcr. assert (Hregexc' := Hregexc).
  induction t; intros; invc_cw; invc_tice;
  repeat spec; kappa; try solve [invc Hgcr];
  destruct (Hregexc ad) as [[? | ?] [[? | ?] _]]; eauto;
  invc_noinit; invc_nocr;
  exfalso; eauto using oneinit_or_onecr_contradiction;
  eauto using noreacq_from_nocr1, noreacq_from_nocr2 with gcr.
Qed.

(* ------------------------------------------------------------------------- *)
(* gcr-invalid                                                               *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_invalid  : forall t R,
  gcr t R = R_invalid ->
  R = R_invalid.
Proof.
  intros * H. gendep R; induction t; intros; try discriminate; kappa; auto;
  match goal with
  | IH : forall _, gcr _ _ = _ -> _ = _, H : gcr _ (R_ad ?ad) = _ |- _ =>
    specialize (IH (R_ad ad) H); invc IH
  end.
Qed.

#[export] Hint Extern 8 =>
  match goal with
  | F : gcr _ (R_tid   _) = R_invalid |- _ => apply gcr_invalid in F; invc F
  | F : gcr _ (R_ad    _) = R_invalid |- _ => apply gcr_invalid in F; invc F
  | F : gcr _ (R_reacq _) = R_invalid |- _ => apply gcr_invalid in F; invc F
  end : gcr.

(* ------------------------------------------------------------------------- *)
(* gcr-ad-tid                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_ad_tid : forall t ad tid,
  gcr t (R_ad ad) = R_tid tid ->
  False.
Proof.
  intros * H. gendep ad. induction t; intros; kappa; invc H; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* gcr-tid-tid                                                               *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_tid_tid : forall t tid1 tid2,
  gcr t (R_tid tid1) = R_tid tid2 ->
  tid1 = tid2.
Proof.
  intros * H. induction t; intros; kappa; invc H; auto;
  exfalso; eauto using gcr_ad_tid.
Qed.

Corollary gcr_tid_contradiction : forall ths1 ths2 tid1 tid2 tid,
  tid1 <> tid2 ->
  gcr ths1[tid1] (R_tid tid1) = R_tid tid ->
  gcr ths2[tid2] (R_tid tid2) = R_tid tid ->
  False.
Proof.
  intros * ? H1 H2.
  apply gcr_tid_tid in H1. apply gcr_tid_tid in H2. subst. congruence.
Qed.

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_preservation_write : forall m t1 t2 ad' t' R,
  valid_term m t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  gcr t1 R = gcr t2 R.
Proof.
  intros. gendep R.
  ind_tstep; intros; kappa; repeat invc_vtm; auto; try value_does_not_step;
  eauto using gcr_value;
  match goal with |- _ = gcr ?t _ =>
    rewrite (gcr_noinits_nocrs_noreacqs t); trivial;
    rewrite IHtstep; eauto using gcr_value, vtm_preservation_write
  end.
Qed.

Corollary gcr_preservation_write_cstep : forall m1 m2 ths1 ths2 tid ad' t' R,
  forall_threads ths1 (valid_term m1) ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_write ad' t']~~> m2 \ ths2 ->
  gcr ths1[tid] R = gcr ths2[tid] R.
Proof.
  intros. invc_cstep. invc_mstep. sigma.
  eauto using gcr_preservation_write.
Qed.

Lemma gcr_preservation_read : forall m t1 t2 ad' t' R,
  value t'        ->
  valid_term m t' ->
  valid_term m t1 ->
  (* --- *)
  t1 --[e_read ad' t']--> t2 ->
  gcr t1 R = gcr t2 R.
Proof.
  intros. gendep R.
  ind_tstep; intros; kappa; repeat invc_vtm; auto; try value_does_not_step;
  eauto using gcr_value;
  try solve [match goal with |- _ = gcr ?t _ =>
    rewrite (gcr_noinits_nocrs_noreacqs t); trivial;
    rewrite IHtstep; eauto using gcr_value, vtm_preservation_read
  end].
  erewrite gcr_value; eauto.
Qed.

Corollary gcr_preservation_read_cstep : forall m1 m2 ths1 ths2 tid ad' t' R,
  forall_memory m1 value              ->
  forall_memory m1 (valid_term m1)    ->
  forall_threads ths1 (valid_term m1) ->
  (* --- *)
  m1 \ ths1 ~~[tid, e_read ad' t']~~> m2 \ ths2 ->
  gcr ths1[tid] R = gcr ths2[tid] R.
Proof.
  intros. invc_cstep. invc_mstep. sigma.
  eauto using gcr_preservation_read.
Qed.

