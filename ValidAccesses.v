From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import HasAddress.
From Elo Require Import ValidAddresses.
From Elo Require Import Access.

Definition valid_accesses (m : mem) (t : tm) :=
  forall ad, access m t ad -> ad < length m.

(* ------------------------------------------------------------------------- *)
(* properties                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma vac_length : forall m t ad,
  valid_accesses m t ->
  access m t ad ->
  ad < #m.
Proof.
  intros * Hvac Hacc.
  decompose sum (lt_eq_lt_dec ad (#m)); subst; trivial.
  - specialize (Hvac (#m) Hacc). lia.
  - specialize (Hvac ad Hacc). lia.
Qed.

Lemma vac_nacc_length : forall m t,
  valid_accesses m t ->
  ~ access m t (#m).
Proof.
  intros * ? F. eapply vac_length in F; eauto. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* inversion                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vac_inversion := 
  intros; unfold valid_accesses in *; try split; eauto using access.

Local Lemma inv_vac_ref : forall m ad T,
  valid_accesses m <{ &ad :: T }> ->
  valid_accesses m m[ad].tm.
Proof.
  intros; unfold valid_accesses in *; eauto using access.
  intros ad'. destruct (Nat.eq_dec ad ad'); subst; eauto using access.
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
  valid_accesses m <{ fn x Tx --> t }> ->
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

Ltac inversion_vac :=
  match goal with
  | H: valid_accesses _ <{ &_ :: _  }> |- _ => eapply inv_vac_ref  in H as Hwba'
  | H: valid_accesses _ <{ new _ _  }> |- _ => eapply inv_vac_new  in H
  | H: valid_accesses _ <{ * _      }> |- _ => eapply inv_vac_load in H
  | H: valid_accesses _ <{ _ = _    }> |- _ => eapply inv_vac_asg  in H as [? ?]
  | H: valid_accesses _ <{ fn _ _ --> _ }> |- _ => eapply inv_vac_fun in H
  | H: valid_accesses _ <{ call _ _ }> |- _ => eapply inv_vac_call in H as [? ?]
  | H: valid_accesses _ <{ _ ; _    }> |- _ => eapply inv_vac_seq  in H as [? ?]
  end.

(* ------------------------------------------------------------------------- *)
(* preservation derives from valid-addresses                                 *)
(* ------------------------------------------------------------------------- *)

Local Lemma acc_then_hasad : forall m t ad,
  access m t ad ->
  HasAddress ad t \/ (exists ad', HasAddress ad m[ad'].tm).
Proof.
  intros * Hacc.
  induction Hacc; try destruct IHHacc as [? | [? ?]]; eauto using HasAddress.
Qed.

Theorem vad_then_vac : forall m t,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  valid_accesses m t.
Proof.
  intros. intros ? ?. unfold forall_memory in *. unfold valid_addresses in *.
  assert (HasAddress ad t \/ (exists ad', HasAddress ad m[ad'].tm))
    as [? | [? ?]];
  eauto using acc_then_hasad.
Qed.

Theorem vad_then_mem_vac : forall m t,
  valid_addresses m t ->
  forall_memory m (valid_addresses m) ->
  forall_memory m (valid_accesses m).
Proof.
  intros. intros ad' ? ?.
  unfold forall_memory in *. unfold valid_addresses in *.
  assert (HasAddress ad m[ad'].tm \/ (exists ad'', HasAddress ad m[ad''].tm))
    as [? | [? ?]];
  eauto using acc_then_hasad.
Qed.

