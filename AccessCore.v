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
Inductive access (ad : addr) (m : mem) : tm -> Prop :=
  | acc_mem : forall ad' T,
    ad <> ad' ->
    access ad m m[ad'].tm ->
    access ad m <{&ad' :: T}>

  | acc_ad : forall T,
    access ad m <{&ad :: T}>

  | acc_new : forall T t,
    access ad m t ->
    access ad m <{new T t}>

  | acc_load : forall t,
    access ad m t ->
    access ad m <{*t}>

  | acc_asg1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{t1 = t2}>

  | acc_asg2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{t1 = t2}>

  | acc_fun : forall x Tx t,
    access ad m t ->
    access ad m <{fn x Tx t}>

  | acc_call1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{call t1 t2}>

  | acc_call2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{call t1 t2}>

  | acc_seq1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{t1; t2}>

  | acc_seq2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{t1; t2}>
  .

Theorem strong_acc_mem : forall m t ad ad',
  access ad' m t ->
  access ad  m (m[ad'].tm) ->
  access ad  m t.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access;
  match goal with
  |- access ?ad _ <{& ?ad' :: _}> => destruct (nat_eq_dec ad ad'); subst
  end; eauto using access.
Qed.

(*
  A term has valid accesses if all the addresses it has access to are within
  the bounds of the memory.
*)
Definition valid_accesses (m : mem) (t : tm) :=
  forall ad, access ad m t -> ad < #m.

(* ------------------------------------------------------------------------- *)
(* hints                                                                     *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Unfold valid_accesses  : vac.

#[export] Hint Extern 4 => unfold valid_accesses : vac.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_acc tactic :=
  match goal with
  | H : access _ _ <{unit    }> |- _ => tactic H
  | H : access _ _ <{N _     }> |- _ => tactic H
  | H : access _ _ <{& _ :: _}> |- _ => tactic H
  | H : access _ _ <{new _ _ }> |- _ => tactic H
  | H : access _ _ <{* _     }> |- _ => tactic H
  | H : access _ _ <{_ = _   }> |- _ => tactic H
  | H : access _ _ <{var _   }> |- _ => tactic H
  | H : access _ _ <{fn _ _ _}> |- _ => tactic H
  | H : access _ _ <{call _ _}> |- _ => tactic H
  | H : access _ _ <{_ ; _   }> |- _ => tactic H
  | H : access _ _ <{spawn _ }> |- _ => tactic H
  end.

Ltac inv_acc := match_acc inv.

Ltac inv_clear_acc := match_acc inv_clear.

(* ------------------------------------------------------------------------- *)

Local Ltac solve_vac_inversion := 
  intros; unfold valid_accesses in *; try split; eauto using access.

Local Lemma inv_vac_ad : forall m ad T,
  valid_accesses m <{&ad :: T}> ->
  valid_accesses m m[ad].tm.
Proof.
  intros. intros ad'. destruct (nat_eq_dec ad ad'); subst; eauto using access.
Qed.

Local Lemma inv_vac_new : forall m t T,
  valid_accesses m <{new T t}> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_load : forall m t,
  valid_accesses m <{*t}> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_asg : forall m t1 t2,
  valid_accesses m <{t1 = t2}> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_fun : forall m x Tx t,
  valid_accesses m <{fn x Tx t}> ->
  valid_accesses m t.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_call : forall m t1 t2,
  valid_accesses m <{call t1 t2}> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Local Lemma inv_vac_seq : forall m t1 t2,
  valid_accesses m <{t1; t2}> ->
  valid_accesses m t1 /\ valid_accesses m t2.
Proof. solve_vac_inversion. Qed.

Ltac inv_vac :=
 match goal with
 | H : valid_accesses _ <{&_ :: _ }> |- _ => eapply inv_vac_ad   in H as Hvac'
 | H : valid_accesses _ <{new _ _ }> |- _ => eapply inv_vac_new  in H
 | H : valid_accesses _ <{* _     }> |- _ => eapply inv_vac_load in H
 | H : valid_accesses _ <{_ = _   }> |- _ => eapply inv_vac_asg  in H as [? ?]
 | H : valid_accesses _ <{fn _ _ _}> |- _ => eapply inv_vac_fun  in H
 | H : valid_accesses _ <{call _ _}> |- _ => eapply inv_vac_call in H as [? ?]
 | H : valid_accesses _ <{_ ; _   }> |- _ => eapply inv_vac_seq  in H as [? ?]
 end.

(* ------------------------------------------------------------------------- *)
(* dec                                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma acc_dec : forall m t ad,
  Decidable.decidable (access ad m t).
Proof. eauto using classic_decidable. Qed.

(* ------------------------------------------------------------------------- *)
(* valid-accesses derives from valid-addresses                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma acc_then_hasad : forall m t ad,
  access ad m t ->
  t has_address ad \/ (exists ad', m[ad'].tm has_address ad).
Proof.
  intros * Hacc. induction Hacc; try destruct IHHacc as [? | [? ?]];
  eauto using anyt, is_address.
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

(* TODO *)

Lemma vac_then_nacc : forall m t,
  valid_accesses m t ->
  ~ access (#m) m t.
Proof.
  intros * H F. eapply H in F; eauto. lia.
Qed.

