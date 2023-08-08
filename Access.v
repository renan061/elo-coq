From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* access                                                                    *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* valid-accesses                                                            *)
(* ------------------------------------------------------------------------- *)

(*
  A term has valid accesses if all the addresses it has access to are within
  the bounds of the memory.
*)
Definition valid_accesses (m : mem) (t : tm) :=
  forall ad, access ad m t -> ad < #m.

(* ------------------------------------------------------------------------- *)
(* unfold hints                                                              *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Unfold valid_accesses : vac.

#[export] Hint Extern 4 => unfold valid_accesses : vac.

(* ------------------------------------------------------------------------- *)
(* access inversion                                                          *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_acc tactic :=
  match goal with
  | H : access _ _ thread_default |- _ => tactic H
  | H : access _ _ <{unit    }>   |- _ => tactic H
  | H : access _ _ <{N _     }>   |- _ => tactic H
  | H : access _ _ <{& _ :: _}>   |- _ => tactic H
  | H : access _ _ <{new _ _ }>   |- _ => tactic H
  | H : access _ _ <{* _     }>   |- _ => tactic H
  | H : access _ _ <{_ = _   }>   |- _ => tactic H
  | H : access _ _ <{var _   }>   |- _ => tactic H
  | H : access _ _ <{fn _ _ _}>   |- _ => tactic H
  | H : access _ _ <{call _ _}>   |- _ => tactic H
  | H : access _ _ <{_ ; _   }>   |- _ => tactic H
  | H : access _ _ <{spawn _ }>   |- _ => tactic H
  end.

Ltac inv_acc := match_acc inv.

Ltac inv_clear_acc := match_acc inv_clear.

(* ------------------------------------------------------------------------- *)
(* valid-accesses inversion                                                  *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vac_inversion := 
  intros; autounfold with vac in *; try split; eauto using access.

Local Lemma inv_vac_ad : forall m ad T,
  valid_accesses m <{&ad :: T}> ->
  ad < #m /\ valid_accesses m m[ad].tm.
Proof.
  solve_vac_inversion. intros ad'.
  destruct (nat_eq_dec ad ad'); subst; eauto using access.
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
  (* irrelevant for unit  *)
  (* irrelevant for num   *)
  | H : valid_accesses _ <{& _ :: _}> |- _ => eapply inv_vac_ad   in H as [? ?]
  | H : valid_accesses _ <{new _ _ }> |- _ => eapply inv_vac_new  in H
  | H : valid_accesses _ <{* _     }> |- _ => eapply inv_vac_load in H
  | H : valid_accesses _ <{_ = _   }> |- _ => eapply inv_vac_asg  in H as [? ?]
  (* irrelevant for var   *)                    
  | H : valid_accesses _ <{fn _ _ _}> |- _ => eapply inv_vac_fun  in H
  | H : valid_accesses _ <{call _ _}> |- _ => eapply inv_vac_call in H as [? ?]
  | H : valid_accesses _ <{_ ; _   }> |- _ => eapply inv_vac_seq  in H as [? ?]
  (* irrelevant for spawn *)                    
  end.

