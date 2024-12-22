From Coq Require Import Lists.List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Multistep.

#[export] Hint Extern 8 =>
  match goal with
  | |- R_invalid <> R_tid _   => intros F; invc F
  | |- R_invalid <> R_ad  _   => intros F; invc F
  | |- R_tid _   <> R_ad  _   => intros F; invc F
  | |- R_tid _   <> R_invalid => intros F; invc F
  | |- R_ad _    <> R_invalid => intros F; invc F
  | |- R_ad _    <> R_tid _   => intros F; invc F
  end : gcr.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_noinits_nocrs : forall t R,
  no_inits t ->
  no_crs   t ->
  gcr t R = R.
Proof.
  intros. induction t; invc_noinits; invc_nocrs; simpl; eauto;
  destruct (is_value t1); eauto.
Qed.

(* ------------------------------------------------------------------------- *)

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
  invc_ostep. invc_cstep. invc_mstep. eauto using gcr_read.
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
  invc_ostep. invc_cstep. invc_mstep. eauto using gcr_write.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_noinit_nocr_ad : forall ad t R,
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

#[export] Hint Extern 8 =>
  match goal with _ : no_init ?ad ?t, _ : no_cr ?ad ?t |- _ =>
    match goal with
    (* --- *)
    | F : gcr ?t (R_tid ?tid) = R_ad ?ad |- _ =>
      apply (gcr_noinit_nocr_ad ad  t (R_tid tid)) in F; trivial; invc F
    (* --- *)
    | F : gcr ?t (R_ad  ?ad1) = R_ad ?ad2, _ : ?ad2 <> ?ad1 |- _ =>
      apply (gcr_noinit_nocr_ad ad2 t (R_ad ad1))  in F; trivial; invc F
    end
  end : gcr.

Lemma oneinit_or_onecr_from_gcr : forall ad t tid,
  region_exclusivity t ->
  (* --- *)
  gcr t (R_tid tid) = R_ad ad ->
  (one_init ad t \/ one_cr ad t).
Proof.
  intros * Hregexc Hgcr. assert (Hregexc' := Hregexc).
  induction t; kappa; invc_regexc; repeat spec; try solve [invc Hgcr];
  destruct (Hregexc ad) as [[? | ?] [[? | ?] _]]; eauto;
  invc_noinit; invc_nocr; eauto with gcr.
Qed.

(* ------------------------------------------------------------------------- *)
(* TODO                                                                      *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)

(* TODO
Notation "'[[' p1 '..' tc '..' p2 ']]'" := (p2 :: tc ++ p1 :: nil)
  (at level 40).
*)

Local Lemma _destruct_ustep2 : forall tc m1 m3 ths1 ths3 tid e,
  m1 / ths1 ~~[tc ++ (tid, e) :: nil]~~>* m3 / ths3 ->
  (exists m2 ths2,
    m1 / ths1 ~~~[tid, e]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*     m3 / ths3 ).
Proof.
  intros ?. induction tc; intros; invc_ustep.
  - invc_ustep. eauto using multistep.
  - match goal with Hustep : _ / _ ~~[ _ ]~~>* _ / _ |- _ => 
      decompose record (IHtc _ _ _ _ _ _ Hustep); eauto using multistep
    end.
Qed.

Ltac destruct_ustep2 :=
  match goal with
  | H : _ / _  ~~[_ ++ (_, _) :: nil]~~>* _ / _ |- _ =>
    eapply _destruct_ustep2 in H as [? [? [? ?]]]
  end.

Local Lemma _destruct_ustep3 : forall tc m1 m4 ths1 ths4 tid1 tid2 e1 e2,
  m1 / ths1 ~~[(tid2, e2) :: tc ++ (tid1, e1) :: nil]~~>* m4 / ths4 ->
  (exists m2 ths2 m3 ths3,
    m1 / ths1 ~~~[tid1, e1]~~> m2 / ths2 /\
    m2 / ths2 ~~[tc]~~>*      m3 / ths3 /\
    m3 / ths3 ~~~[tid2, e2]~~> m4 / ths4 ).
Proof.
  intros. invc_ustep. destruct_ustep2. do 4 eexists. repeat split; eauto.
Qed.

Ltac destruct_ustep3 :=
  match goal with 
  | H : _ / _ ~~[(_, _) :: _ ++ (_, _) :: nil]~~>* _ / _ |- _ =>
    eapply _destruct_ustep3 in H
      as [mA [thsA [mB [thsB [H1A [HAB HB2]]]]]]
  end.

Theorem safety_write_read : forall m1 m2 ths1 ths2 tc tc' tid1 tid2 ad t1 t2,
  tid1 <> tid2 ->
  invariants m1 ths1 ->
  m1 / ths1 ~~[tc]~~>* m2 / ths2 ->
  tc = (tid2, e_read ad t2) :: tc' ++ (tid1, e_write ad t1) :: nil ->
  False.
Proof.
  intros. subst. destruct_ustep3.
  assert (invariants mA thsA) by eauto using invariants_preservation_rstep.
  assert (invariants mB thsB) by eauto using invariants_preservation_ustep.
  assert (invariants m2 ths2) by eauto using invariants_preservation_rstep.

  assert (exists T, m1[ad].T = `w&T`) as [T ?] by admit.
  assert (mB[ad].T = `w&T`)                    by admit.

  assert (gcr ths1[tid1] (R_tid tid1) = m1[ad].R)
    by eauto 7 using rstep_gcr_write with inva.
  assert (gcr thsB[tid2] (R_tid tid2) = mB[ad].R)
    by eauto using rstep_gcr_read with inva.

  assert (HR : m1[ad].R = mB[ad].R) by admit.
  rewrite <- HR in *.

  destruct (m1[ad].R); eauto using gcr_tid_contradiction with gcr.

  eapply oneinit_or_onecr_from_gcr in H6. 2: admit.
  eapply oneinit_or_onecr_from_gcr in H7. 2: admit.

Abort.



(*


ths1, tid1, READ ad   ---- tc1  REL tc2 ACQ tc3 ------->*   ths2, tid2, WRITE ad

m[ad].R = R_ad adx

one_init adx ths1[tid1] \/ one_cr adx ths1[tid1]

one_init adx ths2[tid2] \/ one_cr adx ths2[tid2]


init tid1 adx
init tid2 adx


init tid1 adx  X
cr   tid2 adx


cr   tid1 adx
init tid2 adx


cr tid1 adx  X
cr tid2 adx



*)


Lemma gcr_ad_tid_contradiction : forall tid ad t,
  gcr t (R_ad ad) = R_tid tid ->
  False.
Proof.
  intros * Hgcr. gendep ad.
  induction t; intros; kappa; eauto; invc Hgcr; auto.
Qed.

Lemma gcr_tid1_tid2_contradiction : forall tid1 tid2 t,
  tid1 <> tid2 ->
  gcr t (R_tid tid1) = R_tid tid2 ->
  False.
Proof.
  intros * ? Hgcr.
  induction t; intros; kappa; eauto using gcr_ad_tid_contradiction;
  invc Hgcr; auto.
Qed.

