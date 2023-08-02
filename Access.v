From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.
From Elo Require Import AnyTerm.
From Elo Require Import ValidAddresses.


(*
  A term has access to an address if it refers to the address directly or 
  indirectly.
  
  Ignores <spawn> blocks.
*)
Reserved Notation " '(' m '|' t ')' 'has_access_to' ad "
  (at level 90, t custom elo_tm, no associativity).
Reserved Notation " '(' m '/' t ')' 'has_access_to' ad "
  (at level 90, no associativity).

Inductive access (m : mem) : addr -> tm -> Prop :=
  | acc_mem : forall ad ad' T,
    ad <> ad' ->
    (m /  m[ad'].tm) has_access_to ad ->
    (m | &ad' :: T) has_access_to ad

  | acc_ad : forall ad T,
    (m | &ad :: T) has_access_to ad

  | acc_new : forall T t ad,
    (m | t) has_access_to ad ->
    (m | new T t) has_access_to ad

  | acc_load : forall t ad,
    (m | t) has_access_to ad ->
    (m | *t) has_access_to ad

  | acc_asg1 : forall t1 t2 ad,
    (m | t1) has_access_to ad ->
    (m | t1 = t2) has_access_to ad

  | acc_asg2 : forall t1 t2 ad,
    (m | t2) has_access_to ad ->
    (m | t1 = t2) has_access_to ad

  | acc_fun : forall x Tx t ad,
    (m | t) has_access_to ad ->
    (m | fn x Tx t) has_access_to ad

  | acc_call1 : forall t1 t2 ad,
    (m | t1) has_access_to ad ->
    (m | call t1 t2) has_access_to ad

  | acc_call2 : forall t1 t2 ad,
    (m | t2) has_access_to ad ->
    (m | call t1 t2) has_access_to ad

  | acc_seq1 : forall t1 t2 ad,
    (m | t1) has_access_to ad ->
    (m | t1; t2) has_access_to ad

  | acc_seq2 : forall t1 t2 ad,
    (m | t2) has_access_to ad ->
    (m | t1; t2) has_access_to ad

  where " '(' m '|' t ')' 'has_access_to' ad " := (access m ad t),
        " '(' m '/' t ')' 'has_access_to' ad " := (access m ad t).

(*
  A term has valid accesses if all the addresses it has access to are within
  the bounds of the memory.
*)
Definition valid_accesses (m : mem) (t : tm) :=
  forall ad, (m | t) has_access_to ad -> ad < #m.

(* ------------------------------------------------------------------------- *)
(* hints                                                                     *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Extern 4 => unfold valid_accesses : vac.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_acc tactic :=
  match goal with
  | H : (_ | unit     ) has_access_to _ |- _ => tactic H
  | H : (_ | N _      ) has_access_to _ |- _ => tactic H
  | H : (_ | & _ :: _ ) has_access_to _ |- _ => tactic H
  | H : (_ | new _ _  ) has_access_to _ |- _ => tactic H
  | H : (_ | * _      ) has_access_to _ |- _ => tactic H
  | H : (_ | _ = _    ) has_access_to _ |- _ => tactic H
  | H : (_ | var _    ) has_access_to _ |- _ => tactic H
  | H : (_ | fn _ _ _ ) has_access_to _ |- _ => tactic H
  | H : (_ | call _ _ ) has_access_to _ |- _ => tactic H
  | H : (_ | _ ; _    ) has_access_to _ |- _ => tactic H
  | H : (_ | spawn _  ) has_access_to _ |- _ => tactic H
  end.

Ltac inv_acc := match_acc inv.

Ltac inv_clear_acc := match_acc inv_clear.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_vac_inversion := 
  intros; unfold valid_accesses in *; try split; eauto using access.

Local Lemma inv_vac_ad : forall m ad T,
  valid_accesses m <{ &ad :: T }> ->
  valid_accesses m m[ad].tm.
Proof.
  intros. intros ad'. destruct (Nat.eq_dec ad ad'); subst; eauto using access.
Qed.

Local Lemma inv_vac_new : forall m t T,
  valid_accesses m <{ new T t }> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_load : forall m t,
  valid_accesses m <{ *t }> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_asg : forall m t1 t2,
  valid_accesses m <{ t1 = t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_fun : forall m x Tx t,
  valid_accesses m <{ fn x Tx t }> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_call : forall m t1 t2,
  valid_accesses m <{ call t1 t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_seq : forall m t1 t2,
  valid_accesses m <{ t1; t2 }> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Ltac inv_vac :=
 match goal with
 | H : valid_accesses _ <{ &_ :: _  }> |- _ => eapply inv_vac_ad   in H as Hvac'
 | H : valid_accesses _ <{ new _ _  }> |- _ => eapply inv_vac_new  in H
 | H : valid_accesses _ <{ * _      }> |- _ => eapply inv_vac_load in H
 | H : valid_accesses _ <{ _ = _    }> |- _ => eapply inv_vac_asg  in H as [? ?]
 | H : valid_accesses _ <{ fn _ _ _ }> |- _ => eapply inv_vac_fun  in H
 | H : valid_accesses _ <{ call _ _ }> |- _ => eapply inv_vac_call in H as [? ?]
 | H : valid_accesses _ <{ _ ; _    }> |- _ => eapply inv_vac_seq  in H as [? ?]
 end.

(* ------------------------------------------------------------------------- *)
(* basic properties                                                          *)
(* ------------------------------------------------------------------------- *)

Theorem strong_acc_mem : forall m t ad ad',
  (m | t) has_access_to ad' ->
  (m | (m[ad'].tm)) has_access_to ad ->
  (m | t) has_access_to ad.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access;
  match goal with
  |- (_ | & ?ad' :: _) has_access_to ?ad =>
    destruct (nat_eq_dec ad ad'); subst
  end;
  eauto using access.
Qed.

Lemma acc_dec : forall m t ad,
  Decidable.decidable ((m | t) has_access_to ad).
Proof. eauto using classic_decidable. Qed.

(* length ------------------------------------------------------------------ *)

Lemma acc_length : forall m ad ad',
  (m | (m[ad'].tm)) has_access_to ad ->
  ad' < #m.
Proof.
  intros * Hacc. decompose sum (lt_eq_lt_dec ad' (#m)); subst;
  trivial; simpl_array; inversion Hacc.
Qed.

Lemma vac_nacc_length : forall m t,
  valid_accesses m t ->
  ~ ((m | t) has_access_to #m).
Proof.
  intros * Hvac Hacc. specialize (Hvac (#m) Hacc). lia.
Qed.

(*
TODO: remove

Lemma vac_length : forall m t ad,
  valid_accesses m t ->
  access m t ad ->
  ad < #m.
Proof. eauto. Qed.

Corollary vac_neq_length : forall m t ad,
  valid_accesses m t ->
  access m t ad ->
  ad <> #m.
Proof.
  intros. eauto using Nat.lt_neq.
Qed.
*)

(* ------------------------------------------------------------------------- *)
(* valid-accesses derives from valid-addresses                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma acc_then_hasad : forall m t ad,
  (m | t) has_access_to ad ->
  t has_address ad \/ (exists ad', m[ad'].tm has_address ad).
Proof.
  intros * Hacc. induction Hacc; try destruct IHHacc as [? | [? ?]];
  eauto using anyt, is_address.
Qed.

Lemma vad_nacc_length : forall m t,
  forall_memory m (valid_addresses m) ->
  valid_addresses m t ->
  ~ ((m | t) has_access_to #m).
Proof.
  intros * ? Hvad Hacc. remember (#m) as ad.
  induction Hacc; inversion_vad; eauto. lia.
Qed.

Theorem vad_then_vac : forall m t,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  valid_accesses m t.
Proof.
  intros * ? Hmvad ? Hacc. autounfold with vad in Hmvad.
  eapply acc_then_hasad in Hacc as [? | [? ?]]; eauto.
Qed.

Theorem vad_then_mvac : forall m t,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  forall_memory m (valid_accesses m).
Proof.
  intros * ? Hmvad ? ? Hacc. autounfold with vad in Hmvad.
  eapply acc_then_hasad in Hacc as [? | [? ?]]; eauto.
Qed.

Corollary forall_threads_vad_then_vac : forall m ths,
  forall_threads ths (valid_addresses m) ->
  forall_memory m (valid_addresses m) ->
  forall_threads ths (valid_accesses m).
Proof.
  intros. intros ?. eauto using vad_then_vac.
Qed.

(* ------------------------------------------------------------------------- *)
(* properties -- subst                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma subst_acc : forall m x Tx t t' ad,
  (m | ([x := t'] t)) has_access_to ad ->
  (m | call <{ fn x Tx t }> t') has_access_to ad.
Proof.
  intros. induction t; eauto using access; simpl in *;
  try (destruct String.string_dec; eauto using access);
  inv_clear_acc; auto_specialize; do 2 inv_acc; eauto using access.
Qed.

(* ------------------------------------------------------------------------- *)
(* properties -- memory -- add                                               *)
(* ------------------------------------------------------------------------- *)

(*
Lemma mem_add_acc : forall m t ad vTr,
  ~ access m t (#m) ->
  access (m +++ vTr) t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (m +++ vTr) as m'.
  induction Hacc; inversion Heqm'; subst; inversion_nacc Hnacc.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; try lia;
  simpl_array; eauto using access. simpl in *. inversion_acc.
Qed.

Lemma mem_add_nacc : forall m t ad vTr,
  ~ access m t (#m) ->
  ~ access m t ad ->
  ~ access (m +++ vTr) t ad.
Proof.
  intros * Hnacc1 Hnacc2 F. induction F; inversion_nacc Hnacc2.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array;
  inversion_nacc Hnacc1. eapply IHF; eapply nacc_iff; eauto using not_access.
Qed.
*)

(* ------------------------------------------------------------------------- *)
(* properties -- inheritance                                                 *)
(* ------------------------------------------------------------------------- *)

(*
Lemma mem_set_acc : forall m t ad ad' vTr,
  ~ access m t ad' ->
  access m[ad' <- vTr] t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc.  remember (m[ad' <- vTr]) as m'.
  induction Hacc; inversion_subst_clear Heqm'; inversion_nacc Hnacc;
  simpl_array; eauto using access.
Qed.

Local Lemma mem_set_acc' : forall m t ad ad' v Tr,
  ~ access m v ad ->
  access m[ad' <- (v, Tr)] t ad ->
  access m t ad.
Proof.
  intros * Hnacc Hacc. remember (m[ad' <- (v, Tr)]) as m'.
  induction Hacc; try rename IHHacc into IH;
  inversion_subst_clear Heqm'; eauto using access.
  match goal with |- access _ <{ & ?ad :: _ }> _ => rename ad into ad'' end.
  destruct (Nat.eq_dec ad' ad''); subst;
  try simpl_array; eauto using access;
  destruct (Nat.eq_dec ad'' ad); subst; eauto using access.
  auto_specialize. rewrite (get_set_eq memory_default) in IH. 1: contradiction.
  eapply not_le. intros Hlen. simpl_array. 
  eapply Nat.lt_eq_cases in Hlen as [? | ?]; subst;
  simpl_array; simpl in *; inversion_acc.
Qed.

Lemma mem_set_nacc1 : forall m t ad ad' vTr,
  ~ access m t ad' ->
  ~ access m t ad ->
  ~ access m[ad' <- vTr] t ad.
Proof.
  intros * Hnacc' Hnacc F. remember (m[ad' <- vTr]) as m'.
  induction F; inversion_nacc Hnacc'; inversion_nacc Hnacc.
  simpl_array. eauto.
Qed.

Lemma mem_set_nacc2 : forall m t ad ad' v Tr,
  ~ access m v ad ->
  ~ access m t ad ->
  ~ access m[ad' <- (v, Tr)] t ad.
Proof.
  assert (ge_iff_le : forall m n, m >= n <-> n <= m)
    by (intros; split; destruct n; eauto).
  assert (forall m ad ad' v,
    access m[ad' <- v] m[ad' <- v][ad'].tm ad ->
    ad' < length m). {
    intros * H. eapply not_ge. rewrite ge_iff_le. intros ?.
    rewrite (get_set_invalid memory_default) in H; trivial. inversion H.
  }
  (* main proof *)
  intros * ? ? Hacc. remember (m[ad' <- (v, Tr)]) as m'.
  induction Hacc; inversion_subst_clear Heqm'; eauto using access.
  match goal with _ : ~ access _ <{ & ?ad :: _ }> _ |- _ => 
    destruct (Nat.eq_dec ad' ad) as [? | Hneq]; subst;
    try (assert (ad < #m) by eauto)
  end;
  simpl_array; eauto using access.
Qed.
*)

(* ------------------------------------------------------------------------- *)
(* access properties -- inheritance                                          *)
(* ------------------------------------------------------------------------- *)

Lemma step_none_inherits_access : forall m t t' ad,
  (m | t') has_access_to ad ->
  t --[EF_None]--> t' ->
  (m | t) has_access_to ad.
Proof.
  intros. induction_step; try inv_acc; eauto using access, subst_acc.
Qed.

(*
Lemma step_alloc_inherits_acc : forall m t t' ad v Tr,
  valid_accesses m t ->
  ad <> #m ->
  access (m +++ (v, Tr)) t' ad ->
  t --[EF_Alloc (#m) v Tr]--> t' ->
  access m t ad.
Proof.
  intros. induction_step;
  inversion_vac; inversion_acc; eauto using access; try lia; try simpl_array;
  eauto using mem_add_acc, vac_nacc_length, access.
Qed.

Lemma step_read_inherits_acc : forall m t t' ad ad',
  access m t' ad ->
  t --[EF_Read ad' m[ad'].tm]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; try inversion_acc; eauto using access.
  destruct (Nat.eq_dec ad' ad); subst; eauto using access.
Qed.

Lemma step_write_inherits_acc : forall m t t' ad ad' v Tr,
  access m[ad' <- (v, Tr)] t' ad ->
  t --[EF_Write ad' v Tr]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; inversion_acc; eauto using access;
  destruct (acc_dec m v ad); eauto using mem_set_acc', access;
  assert (forall t t', t --[EF_Write ad' v Tr]--> t' -> access m t ad)
    by (intros; induction_step; eauto using access);
  eauto using access.
Qed.

Lemma step_spawn_inherits_acc : forall m t t' block ad,
  access m t' ad ->
  t --[EF_Spawn block]--> t' ->
  access m t ad.
Proof.
  intros. induction_step; inversion_acc; eauto using access.
Qed.
*)

(* ------------------------------------------------------------------------- *)
(* not-access properties -- preservation                                     *)
(* ------------------------------------------------------------------------- *)

(*



Corollary mstep_nacc_preservation : forall m m' t t' ad eff,
  ad < #m ->
  valid_accesses m t ->
  ~ access m t ad ->
  m / t ==[eff]==> m' / t' ->
  ~ access m' t' ad.
Proof.
Qed.

*)

