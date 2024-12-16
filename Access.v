From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

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

  | acc_ref   : forall T,       access ad <{&ad : w&T       }>

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

  | acc_acq1  : forall t1 x t2, access ad t1 ->
                                access ad <{acq t1 x t2     }>

  | acc_acq2  : forall t1 x t2, access ad t2 ->
                                access ad <{acq t1 x t2     }>
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
  | H : access _ <{acq _ _ _     }>   |- _ => tt H
  | H : access _ <{cr _ _        }>   |- _ => inv H
  | H : access _ <{spawn _       }>   |- _ => inv H
  end.

Ltac inv_acc  := _acc inv.
Ltac invc_acc := _acc invc.

(* decidability ------------------------------------------------------------ *)

Corollary acc_dec : forall ad t,
  Decidable.decidable (access ad t).
Proof.
  unfold Decidable.decidable. intros. induction t;
  try destruct IHt; try destruct IHt1; try destruct IHt2; auto using access;
  try solve [right; intros ?; invc_acc; auto].
  - match goal with |- _ ?ad1 <{&?ad2 : ?T}> \/ _ =>
      nat_eq_dec ad1 ad2; destruct T
    end;
    auto using access; right; intros ?; invc_acc; auto.
  - match goal with     |- _ _ <{init _ _ : ?T}> \/ _        => destruct T end;
    try match goal with |- _ _ <{init _ _ : (Safe ?T)}> \/ _ => destruct T end;
    auto using access;
    right; intros ?; invc_acc.
Qed.

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

