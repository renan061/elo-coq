From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import Properties1.
From Elo Require Import Properties2.

(* ------------------------------------------------------------------------- *)
(* access                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Ignores monitor initializers, critical regions, and spawn blocks. *)
Inductive access (ad : addr) : tm -> Prop :=
  | acc_fun   : forall x Tx t,  access ad t  ->
                                access ad <{fn x Tx t       }>

  | acc_call1 : forall t1 t2,   access ad t1 ->
                                access ad <{call t1 t2      }>

  | acc_call2 : forall t1 t2,   access ad t2 ->
                                access ad <{call t1 t2      }>

  | acc_ref   : forall T,       access ad <{&ad  : w&T      }>

  | acc_new   : forall t T,     access ad t  ->
                                access ad <{new t : T       }>

  | acc_initR : forall ad' t T, access ad t  ->
                                access ad <{init ad' t : r&T}>

  | acc_initW : forall ad' t T, access ad t  ->
                                access ad <{init ad' t : w&T}>

  | acc_load  : forall t,       access ad t  ->
                                access ad <{*t              }>

  | acc_asg1  : forall t1 t2,   access ad t1 ->
                                access ad <{t1 := t2        }>

  | acc_asg2  : forall t1 t2,   access ad t2 ->
                                access ad <{t1 := t2        }>

  | acc_acq1  : forall t1 t2,   access ad t1 ->
                                access ad <{acq t1 t2       }>

  | acc_acq2  : forall t1 t2,   access ad t2 ->
                                access ad <{acq t1 t2       }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _acc tt :=
  match goal with
  | H : access _ <{unit          }>   |- _ => inv H
  | H : access _ <{nat _         }>   |- _ => inv H
  | H : access _ <{var _         }>   |- _ => inv H
  | H : access _ <{fn _ _ _      }>   |- _ => tt H
  | H : access _ <{call _ _      }>   |- _ => tt H
  | H : access _ <{& _ : _       }>   |- _ => tt H
  | H : access _ <{new _ : _     }>   |- _ => tt H
  | H : access _ <{init _ _ : _  }>   |- _ => tt H
  | H : access _ <{* _           }>   |- _ => tt H
  | H : access _ <{_ := _        }>   |- _ => tt H
  | H : access _ <{acq _  _      }>   |- _ => tt H
  | H : access _ <{cr _ _        }>   |- _ => inv H
  | H : access _ <{spawn _       }>   |- _ => inv H
  end.

Ltac inv_acc  := _acc inv.
Ltac invc_acc := _acc invc.

(* decidability ------------------------------------------------------------ *)

Corollary acc_dec : forall ad t,
  Decidable.decidable (access ad t).
Proof. eauto using classic_decidable. Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma acc_vad_ad_bounds : forall ad m t,
  valid_addresses m t ->
  (* --- *)
  access ad t ->
  ad < #m.
Proof.
  intros * ? Hacc. induction Hacc; invc_vad; auto.
Qed.

Corollary acc_vad_contradiction1 : forall m t,
  valid_addresses m t ->
  (* --- *)
  access (#m) t ->
  False.
Proof.
  intros. assert (#m < #m) by eauto using acc_vad_ad_bounds. lia.
Qed.

Corollary acc_vad_contradiction2 : forall ad m t,
  valid_addresses m t ->
  (* --- *)
  access ad t ->
  #m < ad ->
  False.
Proof.
  intros. assert (ad < #m) by eauto using acc_vad_ad_bounds. lia.
Qed.

Corollary acc_vad_contradiction3 : forall ad m t,
  valid_addresses m t ->
  (* --- *)
  access ad t ->
  #m <= ad ->
  False.
Proof.
  intros * ? ? H. eapply Lt.le_lt_or_eq in H as [? | ?]; subst;
  eauto using acc_vad_contradiction1, acc_vad_contradiction2.
Qed.

Lemma acc_noref_contradiction : forall ad t,
  access ad t ->
  no_ref ad t ->
  False.
Proof.
  intros * H **. induction H; invc_noref; auto.
Qed.

Lemma acc_nowref_contradiction : forall ad m t T,
  consistent_references m t ->
  (* --- *)
  m[ad].T = `w&T` ->
  access ad t ->
  no_wref ad t ->
  False.
Proof.
  intros * ? ? H **. induction H; invc_cr; invc_nowref; auto.
Qed.

Corollary acc_nowrefs_contradiction : forall ad m t T,
  consistent_references m t ->
  (* --- *)
  m[ad].T = `w&T` ->
  access ad t ->
  no_wrefs  t ->
  False.
Proof.
  unfold no_wrefs. eauto using acc_nowref_contradiction.
Qed.

(* ------------------------------------------------------------------------- *)
(* xaccess                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Access through monitor initializers and critical regions. *)
Inductive xaccess (adx ad : addr) : tm -> Prop :=
  | xacc_fun       : forall x Tx t,   xaccess adx ad t  ->
                                      xaccess adx ad <{fn x Tx t        }>

  | xacc_call1     : forall t1 t2,    xaccess adx ad t1 ->
                                      xaccess adx ad <{call t1 t2       }>

  | xacc_call2     : forall t1 t2,    xaccess adx ad t2 ->
                                      xaccess adx ad <{call t1 t2       }>

  | xacc_new       : forall t T,      xaccess adx ad t  ->
                                      xaccess adx ad <{new t : T        }>

  | xacc_initR     : forall adx' t T, xaccess adx ad t  ->
                                      xaccess adx ad <{init adx' t : r&T}>

  | xacc_initX_eq  : forall t T,      access ad t       ->
                                      xaccess adx ad <{init adx  t : x&T}>

  | xacc_initX_neq : forall adx' t T, adx <> adx'       ->
                                      xaccess adx ad t  ->
                                      xaccess adx ad <{init adx' t : x&T}>

  | xacc_initW     : forall adx' t T, xaccess adx ad t  ->
                                      xaccess adx ad <{init adx' t : w&T}>

  | xacc_load      : forall t,        xaccess adx ad t  ->
                                      xaccess adx ad <{*t               }>

  | xacc_asg1      : forall t1 t2,    xaccess adx ad t1 ->
                                      xaccess adx ad <{t1 := t2         }>

  | xacc_asg2      : forall t1 t2,    xaccess adx ad t2 ->
                                      xaccess adx ad <{t1 := t2         }>

  | xacc_acq1      : forall t1 t2,    xaccess adx ad t1 ->
                                      xaccess adx ad <{acq t1 t2        }>

  | xacc_acq2      : forall t1 t2,    xaccess adx ad t2 ->
                                      xaccess adx ad <{acq t1 t2        }>

  | xacc_cr_eq     : forall t,        access ad t       ->
                                      xaccess adx ad <{cr adx t         }>

  | xacc_cr_neq    : forall adx' t,   adx <> adx'       ->
                                      xaccess adx ad t  ->
                                      xaccess adx ad <{cr adx' t        }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _xacc tt :=
  match goal with
  | H : xaccess _ _ <{unit        }>   |- _ => inv H
  | H : xaccess _ _ <{nat _       }>   |- _ => inv H
  | H : xaccess _ _ <{var _       }>   |- _ => inv H
  | H : xaccess _ _ <{fn _ _ _    }>   |- _ => tt H
  | H : xaccess _ _ <{call _ _    }>   |- _ => tt H
  | H : xaccess _ _ <{& _ : _     }>   |- _ => inv H
  | H : xaccess _ _ <{new _ : _   }>   |- _ => tt H
  | H : xaccess _ _ <{init _ _ : _}>   |- _ => tt H
  | H : xaccess _ _ <{* _         }>   |- _ => tt H
  | H : xaccess _ _ <{_ := _      }>   |- _ => tt H
  | H : xaccess _ _ <{acq _  _    }>   |- _ => tt H
  | H : xaccess _ _ <{cr _ _      }>   |- _ => tt H
  | H : xaccess _ _ <{spawn _     }>   |- _ => inv H
  end.

Ltac inv_xacc  := _xacc inv.
Ltac invc_xacc := _xacc invc.

(* decidability ------------------------------------------------------------ *)

Corollary xacc_dec : forall adx ad t,
  Decidable.decidable (xaccess adx ad t).
Proof. eauto using classic_decidable. Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma xacc_vad_adx_bounds : forall adx ad m t,
  valid_addresses m t ->
  (* --- *)
  xaccess adx ad t ->
  adx < #m.
Proof.
  intros * ? Hxacc. induction Hxacc; invc_vad; auto.
Qed.

Lemma xacc_vad_ad_bounds : forall adx ad m t,
  valid_addresses m t ->
  (* --- *)
  xaccess adx ad t ->
  ad < #m.
Proof.
  intros * ? Hacc. induction Hacc; invc_vad; eauto using acc_vad_ad_bounds.
Qed.

Corollary xacc_vad_adx_contradiction1 : forall m ad t,
  valid_addresses m t ->
  (* --- *)
  xaccess (#m) ad t ->
  False.
Proof.
  intros. assert (#m < #m) by eauto using xacc_vad_adx_bounds. lia.
Qed.

Corollary xacc_vad_ad_contradiction1 : forall m adx t,
  valid_addresses m t ->
  (* --- *)
  xaccess adx (#m) t ->
  False.
Proof.
  intros. assert (#m < #m) by eauto using xacc_vad_ad_bounds. lia.
Qed.

Lemma xacc_noinit_nocr_contradiction : forall adx ad t,
  xaccess adx ad t ->
  no_init adx t ->
  no_cr   adx t ->
  False.
Proof.
  intros. induction t; invc_noinit; inv_nocr; invc_xacc; auto.
Qed.

Corollary xacc_value_contradiction : forall adx ad t,
  valid_blocks t ->
  (* --- *)
  xaccess adx ad t ->
  value t ->
  False.
Proof.
  eauto using noinit_from_value, nocr_from_value,
    xacc_noinit_nocr_contradiction.
Qed.

Corollary oneinit_or_onecr_from_xacc : forall adx ad t,
  (no_init adx t \/ one_init adx t) ->
  (no_cr   adx t \/ one_cr   adx t) ->
  (* --- *)
  xaccess adx ad t ->
  one_init adx t \/ one_cr adx t.
Proof.
  intros * [? | ?] [? | ?] ?; auto. exfalso.
  eauto using xacc_noinit_nocr_contradiction.
Qed.

Corollary oneinit_xor_onecr_from_xacc : forall adx ad m ths tid,
  forall_threads ths (valid_addresses m) ->
  unique_initializers m ths ->
  unique_critical_regions m ths ->
  init_cr_exclusivity ths ->
  (* --- *)
  xaccess adx ad ths[tid] ->
  (one_init adx ths[tid]) \x/ (one_cr adx ths[tid]).
Proof.
  intros * ? ? ? Hice **. 
  assert (adx < #m) by eauto using xacc_vad_adx_bounds.
  assert (tid < #ths) by (lt_eq_gt (#ths) tid; sigma; try invc_xacc; trivial).
  split; eauto using oneinit_or_onecr_from_xacc,
    noinit_or_oneinit_from_ui, nocr_or_onecr_from_ucr.
  destruct (Hice adx tid tid).
  intros [? ?]. eauto using nocr_onecr_contradiction.
Qed.

