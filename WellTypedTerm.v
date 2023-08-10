From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

(* ------------------------------------------------------------------------- *)
(* well-typed-term                                                           *)
(* ------------------------------------------------------------------------- *)

Definition well_typed_term (t : tm) :=
  exists T, empty |-- t is T.

(* ------------------------------------------------------------------------- *)
(* hints                                                                     *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Unfold well_typed_term : wtt.

#[export] Hint Extern 4 => unfold well_typed_term : wtt.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_wtt_inversion := 
  intros * [? ?]; try split; inv_type; try discriminate; eauto; eexists; eauto.

Local Lemma inv_wtt_ad : forall ad T,
  well_typed_term <{&ad :: T}> ->
  (exists T', T = <{{&T'}}>) \/ (exists T', T = <{{i&T'}}>).
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_new : forall t T,
  well_typed_term <{new T t}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_load : forall t,
  well_typed_term <{*t}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_asg : forall t1 t2,
  well_typed_term <{t1 = t2}> ->
  well_typed_term t1 /\ well_typed_term t2.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_var : forall x,
  well_typed_term <{var x}> ->
  False.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_fun : forall x Tx t,
  well_typed_term <{fn x Tx t}> ->
  exists T, empty[x <== Tx] |-- t is T.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_call : forall t1 t2,
  well_typed_term <{call t1 t2}> ->
  well_typed_term t1 /\ well_typed_term t2.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_seq : forall t1 t2,
  well_typed_term <{t1; t2}> ->
  well_typed_term t1 /\ well_typed_term t2.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_spawn : forall t,
  well_typed_term <{spawn t}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Ltac inv_wtt :=
  match goal with
  (* irrelevant for unit *)
  (* irrelevant for num  *)
  | H : well_typed_term <{& _ :: _}> |- _ =>
      eapply inv_wtt_ad    in H as [[? ?] | [? ?]]
  | H : well_typed_term <{new _ _ }> |- _ =>
      eapply inv_wtt_new   in H
  | H : well_typed_term <{* _     }> |- _ =>
      eapply inv_wtt_load  in H
  | H : well_typed_term <{_ = _   }> |- _ =>
      eapply inv_wtt_asg   in H as [? ?]
  | H : well_typed_term <{fn _ _ _}> |- _ =>
      eapply inv_wtt_fun   in H as [? ?]
  | H : well_typed_term <{call _ _}> |- _ =>
      eapply inv_wtt_call  in H as [? ?]
  | H : well_typed_term <{_ ; _   }> |- _ =>
      eapply inv_wtt_seq   in H as [? ?]
  | H : well_typed_term <{spawn _ }> |- _ =>
      eapply inv_wtt_spawn in H
  end.

(* ------------------------------------------------------------------------- *)
(* independent properties                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma wtt_tstep_alloc_value : forall t t' ad v T,
  well_typed_term t ->
  t --[EF_Alloc ad v T]--> t' ->
  well_typed_term v.
Proof.
  intros. induction_tstep; intros; inv_wtt; eauto.
Qed.

Lemma wtt_tstep_write_value : forall t t' ad v T,
  well_typed_term t ->
  t --[EF_Write ad v T]--> t' ->
  well_typed_term v.
Proof.
  intros. induction_tstep; intros; inv_wtt; eauto.
Qed.

