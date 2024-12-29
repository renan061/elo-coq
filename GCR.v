From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

#[export] Hint Extern 8 =>
  match goal with
  | |- R_invalid <> R_tid _   => intros F; invc F
  | |- R_invalid <> R_ad  _   => intros F; invc F
  | |- R_tid _   <> R_ad  _   => intros F; invc F
  | |- R_tid _   <> R_invalid => intros F; invc F
  | |- R_ad _    <> R_invalid => intros F; invc F
  | |- R_ad _    <> R_tid _   => intros F; invc F
  end : gcr.

Lemma gcr_noinits_nocrs : forall t R,
  no_inits t ->
  no_crs   t ->
  gcr t R = R.
Proof.
  intros. induction t; invc_noinits; invc_nocrs; simpl; eauto;
  destruct (is_value t1); eauto.
Qed.

Lemma gcr_noinit_nocr : forall ad t R,
  no_init ad t ->
  no_cr   ad t ->
  gcr t R = R_ad ad ->
  R = R_ad ad.
Proof.
  intros. gendep R. induction t; intros;
  invc_noinit; invc_nocr; kappa; auto; do 2 spec;
  match goal with _ : addr, ad : addr |- _ => specialize (IHt (R_ad ad)) end;
  spec; invc IHt; auto.
Qed.

Lemma gcr_read : forall m t1 t2 ad' t' T' R,
  consistent_term m t1 ->
  consistent_regions m R t1 ->
  (* --- *)
  m[ad'].T = `w&T'` ->
  t1 --[e_read ad' t']--> t2 ->
  gcr t1 R = m[ad'].R.
Proof.
  intros. gendep R. ind_tstep; intros;
  repeat invc_ctm; repeat invc_creg; kappa; eauto; value_does_not_step.
Qed.

Lemma gcr_write : forall m t1 t2 ad' t' R,
  valid_term m t1 ->
  well_typed_term t1 ->
  consistent_regions m R t1 ->
  (* --- *)
  t1 --[e_write ad' t']--> t2 ->
  gcr t1 R = m[ad'].R.
Proof.
  intros * ? [T ?] **. gendep R. gendep T.
  assert (value t') by eauto using value_write_term.
  ind_tstep; intros; repeat invc_vtm; repeat invc_typeof; repeat invc_creg;
  kappa; eauto; try value_does_not_step.
  rewrite gcr_noinits_nocrs; eauto using noinits_from_value, nocrs_from_value.
Qed.

Corollary rstep_gcr_read : forall m1 m2 ths1 ths2 tid ad' t' T',
  forall_threads ths1 (consistent_term m1)  ->
  forall_threads_consistent_regions m1 ths1 ->
  (* --- *)
  m1[ad'].T = `w&T'` ->
  m1 / ths1 ~~~[tid, e_read ad' t']~~> m2 / ths2 ->
  gcr ths1[tid] (R_tid tid) = m1[ad'].R.
Proof.
  intros * ? Hcreg **. specialize (Hcreg tid).
  invc_rstep. invc_cstep. invc_mstep. eauto using gcr_read.
Qed.

Corollary rstep_gcr_write : forall m1 m2 ths1 ths2 tid ad' t',
  forall_threads ths1 well_typed_term       ->
  forall_threads ths1 (valid_term m1)       ->
  forall_threads_consistent_regions m1 ths1 ->
  (* --- *)
  m1 / ths1 ~~~[tid, e_write ad' t']~~> m2 / ths2 ->
  gcr ths1[tid] (R_tid tid) = m1[ad'].R.
Proof.
  intros * ? ? Hcreg **. specialize (Hcreg tid).
  invc_rstep. invc_cstep. invc_mstep. eauto using gcr_write.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Extern 8 =>
  match goal with _ : no_init ?ad ?t, _ : no_cr ?ad ?t |- _ =>
    match goal with
    (* --- *)
    | F : gcr ?t (R_tid ?tid) = R_ad ?ad |- _ =>
      apply (gcr_noinit_nocr ad  t (R_tid tid)) in F; trivial; invc F
    (* --- *)
    | F : gcr ?t (R_ad  ?ad1) = R_ad ?ad2, _ : ?ad2 <> ?ad1 |- _ =>
      apply (gcr_noinit_nocr ad2 t (R_ad ad1))  in F; trivial; invc F
    end
  end : gcr.

Lemma oneinit_or_onecr_from_gcr : forall ad t tid,
  term_init_cr_exc t ->
  (* --- *)
  gcr t (R_tid tid) = R_ad ad ->
  (one_init ad t \/ one_cr ad t).
Proof.
  intros * Hregexc Hgcr. assert (Hregexc' := Hregexc).
  induction t; kappa; invc_tice; repeat spec; try solve [invc Hgcr];
  destruct (Hregexc ad) as [[? | ?] [[? | ?] _]]; eauto;
  invc_noinit; invc_nocr; eauto with gcr.
Qed.

Lemma gcr_invalid  : forall t R,
  gcr t R = R_invalid ->
  R = R_invalid.
Proof.
  intros * H. gendep R; induction t; intros; kappa; eauto;
  match goal with ad : addr |- _ => specialize (IHt (R_ad ad) H) end; invc IHt.
Qed.

#[export] Hint Extern 8 =>
  match goal with
  | F : gcr _ (R_tid _) = R_invalid |- _ => apply gcr_invalid in F; invc F
  | F : gcr _ (R_ad  _) = R_invalid |- _ => apply gcr_invalid in F; invc F
  end : gcr.

Lemma gcr_ad_tid  : forall t ad tid,
  gcr t (R_ad ad) = R_tid tid ->
  False.
Proof.
  intros * H. gendep ad. induction t; intros; kappa; invc H; eauto.
Qed.

Lemma gcr_tid_tid  : forall t tid1 tid2,
  gcr t (R_tid tid1) = R_tid tid2 ->
  tid1 = tid2.
Proof.
  intros * H. induction t; intros; kappa; inv H; eauto;
  exfalso; eauto using gcr_ad_tid.
Qed.

Corollary gcr_tid_contradiction : forall ths1 ths2 tid1 tid2 tid,
  tid1 <> tid2 ->
  gcr ths1[tid1] (R_tid tid1) = R_tid tid ->
  gcr ths2[tid2] (R_tid tid2) = R_tid tid ->
  False.
Proof.
  intros * ? H1 H2.
  apply gcr_tid_tid in H1. apply gcr_tid_tid in H2.
  subst. auto.
Qed.

