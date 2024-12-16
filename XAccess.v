From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Access.

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

  | xacc_acq1      : forall t1 x t2,  xaccess adx ad t1 ->
                                      xaccess adx ad <{acq t1 x t2      }>

  | xacc_acq2      : forall t1 x t2,  xaccess adx ad t2 ->
                                      xaccess adx ad <{acq t1 x t2      }>

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
  | H : xaccess _ _ <{acq _ _ _   }>   |- _ => tt H
  | H : xaccess _ _ <{cr _ _      }>   |- _ => tt H
  | H : xaccess _ _ <{spawn _     }>   |- _ => inv H
  end.

Ltac inv_xacc  := _xacc inv.
Ltac invc_xacc := _xacc invc.

(* decidability ------------------------------------------------------------ *)

Corollary xacc_dec : forall adx ad t,
  Decidable.decidable (xaccess adx ad t).
Proof.
  unfold Decidable.decidable. intros. induction t;
  try destruct IHt; try destruct IHt1; try destruct IHt2; auto using xaccess;
  try solve [right; intros ?; invc_xacc; auto];
  try match goal with |- _ ?adx ?ad1 <{cr ?ad2 _}> \/ _ =>
    nat_eq_dec adx ad2; destruct (acc_dec ad1 t); auto using xaccess;
    right; intros ?; invc_xacc; auto
  end;
  match goal with     |- _ _ <{init _ _ : ?T}> \/ _        => destruct T end;
  try match goal with |- _ _ <{init _ _ : (Safe ?T)}> \/ _ => destruct T end;
  try solve [right; intros ?; invc_xacc; auto];
  match goal with |- _ ?adx ?ad1 <{init ?ad2 _ : _}> \/ _ =>
    nat_eq_dec adx ad2; destruct (acc_dec ad1 t); auto using xaccess;
    right; intros ?; invc_xacc; auto
  end.
Qed.

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

