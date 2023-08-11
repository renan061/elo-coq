From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.

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

Ltac invc_acc := match_acc invc.

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

(* ------------------------------------------------------------------------- *)
(* not-access constructors                                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_nacc_construction :=
  intros ** ?; invc_acc; contradiction.

Lemma nacc_unit : forall m ad,
  ~ access ad m <{unit}>.
Proof.
  intros ** ?. inv_acc.
Qed.

Lemma nacc_num : forall m ad n,
  ~ access ad m <{N n}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_ad : forall m ad ad' T,
  ad <> ad' ->
  ~ access ad m m[ad'].tm ->
  ~ access ad m <{&ad' :: T}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_new : forall m t ad T,
  ~ access ad m t ->
  ~ access ad m <{new T t}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_load : forall m t ad,
  ~ access ad m t ->
  ~ access ad m <{*t}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_asg : forall m t1 t2 ad,
  ~ access ad m t1 ->
  ~ access ad m t2 ->
  ~ access ad m <{t1 = t2}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_fun : forall m x Tx t ad,
  ~ access ad m t ->
  ~ access ad m <{fn x Tx t}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_call : forall m t1 t2 ad,
  ~ access ad m t1 ->
  ~ access ad m t2 ->
  ~ access ad m <{call t1 t2}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_seq : forall m t1 t2 ad,
  ~ access ad m t1 ->
  ~ access ad m t2 ->
  ~ access ad m <{t1; t2}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_spawn : forall m t ad,
  ~ access ad m <{spawn t}>.
Proof. solve_nacc_construction. Qed.

#[export] Hint Resolve
  nacc_unit nacc_num
  nacc_ad nacc_new nacc_load nacc_asg
  nacc_fun nacc_call
  nacc_seq
  nacc_spawn
  : acc.

(* ------------------------------------------------------------------------- *)
(* not-access inversion                                                      *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_nacc_inversion := 
  intros; try split; eauto using access.

Local Lemma inv_nacc_ad : forall m ad ad' T,
  ~ access ad m <{&ad' :: T}> ->
  ad <> ad' /\ ~ access ad m (m[ad'].tm).
Proof.
  intros. assert (ad <> ad') by (intros ?; subst; eauto using access).
  split; eauto using access.
Qed.

Local Lemma inv_nacc_new : forall m t ad T,
  ~ access ad m <{new T t}> ->
  ~ access ad m t.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_load : forall m t ad,
  ~ access ad m <{*t}> ->
  ~ access ad m t.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_asg : forall m t1 t2 ad,
  ~ access ad m <{t1 = t2}> ->
  ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_fun : forall m x Tx t ad,
  ~ access ad m <{fn x Tx t}> ->
  ~ access ad m t.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_call : forall m t1 t2 ad,
  ~ access ad m <{call t1 t2}> ->
  ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_seq : forall m t1 t2 ad,
  ~ access ad m <{t1; t2}> ->
  ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_nacc_inversion. Qed.

Ltac inv_nacc :=
  match goal with
  (* irrelevant for unit  *)
  (* irrelevant for num   *)
  | H : ~ access _ _ <{& _ :: _}> |- _ => eapply inv_nacc_ad   in H as [? ?]
  | H : ~ access _ _ <{new _ _ }> |- _ => eapply inv_nacc_new  in H
  | H : ~ access _ _ <{* _     }> |- _ => eapply inv_nacc_load in H
  | H : ~ access _ _ <{_ = _   }> |- _ => eapply inv_nacc_asg  in H as [? ?]
  (* irrelevant for var   *)                    
  | H : ~ access _ _ <{fn _ _ _}> |- _ => eapply inv_nacc_fun  in H
  | H : ~ access _ _ <{call _ _}> |- _ => eapply inv_nacc_call in H as [? ?]
  | H : ~ access _ _ <{_ ; _   }> |- _ => eapply inv_nacc_seq  in H as [? ?]
  (* irrelevant for spawn *)                    
  end.

(* ------------------------------------------------------------------------- *)
(* independent properties                                                    *)
(* ------------------------------------------------------------------------- *)

Corollary acc_dec : forall ad m t,
  Decidable.decidable (access ad m t).
Proof. eauto using classic_decidable. Qed.

Theorem acc_mem_strong : forall m t ad ad',
  access ad' m t ->
  access ad  m (m[ad'].tm) ->
  access ad  m t.
Proof.
  intros * Hacc ?. induction Hacc; eauto using access;
  match goal with
  |- access ?ad _ <{& ?ad' :: _}> => destruct (nat_eq_dec ad ad'); subst
  end;
  eauto using access.
Qed.

Lemma nacc_tstep_write_value : forall m t t' ad ad' v T,
  ~ access ad m t ->
  t --[EF_Write ad' v T]--> t' ->
  ~ access ad m v.
Proof.
  intros. induction_tstep; eauto using access.
Qed.

