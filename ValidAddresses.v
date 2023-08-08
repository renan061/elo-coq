From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import AnyTerm.

(* ------------------------------------------------------------------------- *)
(* is-address & has-address                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive is_address : addr -> tm -> Prop :=
  | is_address_constructor : forall ad T,
    is_address ad <{ &ad :: T}>
  .

Notation "t 'has_address' ad" := (anyt (is_address ad) t)
  (at level 80, no associativity).

(* ------------------------------------------------------------------------- *)
(* valid-addresses                                                           *)
(* ------------------------------------------------------------------------- *)

(* The addresses are valid if they are within the bounds of the memory. *)
Definition valid_addresses (m : mem) (t : tm) :=
  forall ad, t has_address ad -> ad < #m.

(* ------------------------------------------------------------------------- *)
(* unfold hints                                                              *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Unfold valid_addresses : vad.

#[export] Hint Extern 4 => unfold valid_addresses : vad.

(* ------------------------------------------------------------------------- *)
(* is-address & has-address inversion                                        *)
(* ------------------------------------------------------------------------- *)

Local Ltac inv_isad := 
  match goal with
  | H : is_address _ _ |- _ => inv_clear H
  end.

Local Ltac inv_hasad := 
  match goal with
  | H : _ has_address _ |- _ =>
      inv_clear H; try inv_isad
  end.

(* ------------------------------------------------------------------------- *)
(* valid-addresses inversion                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vad_inversion := 
  intros; try split; eauto using anyt, is_address with vad.

Local Lemma inv_vad_ref : forall m ad T,
  valid_addresses m <{&ad :: T}> ->
  ad < #m.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_new : forall m t T,
  valid_addresses m <{new T t}> ->
  valid_addresses m t.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_load : forall m t,
  valid_addresses m <{*t}> ->
  valid_addresses m t.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_asg : forall m t1 t2,
  valid_addresses m <{t1 = t2}> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_fun : forall m x Tx t,
  valid_addresses m <{fn x Tx t}> ->
  valid_addresses m t.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_call : forall m t1 t2,
  valid_addresses m <{call t1 t2}> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_seq : forall m t1 t2,
  valid_addresses m <{t1; t2}> ->
  valid_addresses m t1 /\ valid_addresses m t2.
Proof. solve_vad_inversion. Qed.

Local Lemma inv_vad_spawn : forall m t,
  valid_addresses m <{spawn t}> ->
  valid_addresses m t.
Proof. solve_vad_inversion. Qed.

Ltac inv_vad :=
 match goal with
 (* irrelevant for unit *)
 (* irrelevant for num  *)
 | H : valid_addresses _ <{& _ :: _}> |- _ => eapply inv_vad_ref   in H as ?
 | H : valid_addresses _ <{new _ _ }> |- _ => eapply inv_vad_new   in H
 | H : valid_addresses _ <{* _     }> |- _ => eapply inv_vad_load  in H
 | H : valid_addresses _ <{_ = _   }> |- _ => eapply inv_vad_asg   in H as [? ?]
 (* irrelevant for var  *)
 | H : valid_addresses _ <{fn _ _ _}> |- _ => eapply inv_vad_fun   in H
 | H : valid_addresses _ <{call _ _}> |- _ => eapply inv_vad_call  in H as [? ?]
 | H : valid_addresses _ <{_ ; _   }> |- _ => eapply inv_vad_seq   in H as [? ?]
 | H : valid_addresses _ <{spawn _ }> |- _ => eapply inv_vad_spawn in H
 end.

(* ------------------------------------------------------------------------- *)
(* valid-addresses construction                                              *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vad_construction := 
  intros ** ? ?; inv_hasad; eauto.

Local Lemma vad_unit : forall m,
  valid_addresses m <{unit}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_num : forall m n,
  valid_addresses m <{N n}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_ad : forall m ad T,
  ad < #m ->
  valid_addresses m <{&ad :: T}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_new : forall m t T,
  valid_addresses m t ->
  valid_addresses m <{new T t}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_load : forall m t,
  valid_addresses m t ->
  valid_addresses m <{*t}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_asg : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{t1 = t2}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_var : forall m x,
  valid_addresses m <{var x}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_fun : forall m x Tx t,
  valid_addresses m t ->
  valid_addresses m <{fn x Tx t}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_call : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{call t1 t2}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_seq : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{t1; t2}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_spawn : forall m t,
  valid_addresses m t ->
  valid_addresses m <{spawn t}>.
Proof. solve_vad_construction. Qed.

#[export] Hint Resolve
  vad_unit vad_num
  vad_ad vad_new vad_load vad_asg
  vad_var vad_fun vad_call vad_seq vad_spawn
  : vad.

