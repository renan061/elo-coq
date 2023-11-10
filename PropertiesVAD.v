From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import AnyTerm.
From Elo Require Import Meta.

From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* valid-addresses implies valid-accesses                                    *)
(* ------------------------------------------------------------------------- *)

Local Lemma acc_then_hasad : forall m t ad,
  access ad m t ->
  t has_address ad \/ (exists ad', m[ad'].tm has_address ad).
Proof.
  intros * Hacc. induction Hacc; try decompose [or and] IHHacc;
  eauto using anyt, is_address.
Qed.

Lemma vad_then_vac : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  valid_accesses m t.
Proof.
  intros * Hmvad ? ? Hacc. autounfold with vad in Hmvad.
  eapply acc_then_hasad in Hacc as [? | [? ?]]; eauto.
Qed.

Lemma mvad_then_mvac : forall m,
  forall_memory m (valid_addresses m) ->
  forall_memory m (valid_accesses m).
Proof.
  intros * Hmvad ? ? Hacc. autounfold with vad in Hmvad.
  eapply acc_then_hasad in Hacc as [? | [? ?]]; eauto.
Qed.

Corollary forall_program_vad_then_vac : forall m ths,
  forall_program m ths (valid_addresses m) ->
  forall_program m ths (valid_accesses m).
Proof.
  intros * [? ?]; split; eauto using mvad_then_mvac.
  intros ?. eauto using vad_then_vac.
Qed.

