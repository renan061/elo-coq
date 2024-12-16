From Coq Require Import Lia.
From Coq Require Import List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import ConsistentRegions.

(* ------------------------------------------------------------------------- *)
(* consistent-regions                                                        *)
(* ------------------------------------------------------------------------- *)

Inductive consistent_stack (s : stack region) (R : region) : tm -> Prop :=
  | cstack_unit  :                   consistent_stack s R <{unit           }>
  | cstack_nat   : forall n,         consistent_stack s R <{nat n          }>
  | cstack_var   : forall x,         consistent_stack s R <{var x          }>
  | cstack_fun   : forall x Tx t,    consistent_stack s R t   ->
                                     consistent_stack s R <{fn x Tx t      }>
  | cstack_call  : forall t1 t2,     consistent_stack s R t1  ->
                                     consistent_stack s R t2  ->
                                     consistent_stack s R <{call t1 t2     }>
  | cstack_refR  : forall ad T,      consistent_stack s R <{&ad : r&T      }>
  | cstack_refX  : forall ad T,      consistent_stack s R <{&ad : x&T      }>
  | cstack_refW  : forall ad T,      consistent_stack s R <{&ad : w&T      }>
  | cstack_new   : forall t T,       consistent_stack s R t   ->
                                     consistent_stack s R <{new t : T      }>
  | cstack_initR : forall ad t T,    consistent_stack s R t   ->
                                     consistent_stack s R <{init ad t : r&T}>
  | cstack_initX : forall R' ad t T, R' = R_monitor ad        ->
                                     consistent_stack (push s R') R' t ->
                                     consistent_stack s R <{init ad t : x&T}>
  | cstack_initW : forall ad t T,    consistent_stack s R t   ->
                                     consistent_stack s R <{init ad t : w&T}>
  | cstack_load  : forall t,         consistent_stack s R t   ->
                                     consistent_stack s R <{*t             }>
  | cstack_asg   : forall t1 t2,     consistent_stack s R t1  ->
                                     consistent_stack s R t2  ->
                                     consistent_stack s R <{t1 := t2       }>
  | cstack_acq   : forall t1 x t2,   consistent_stack s R t1  ->
                                     consistent_stack s R t2  ->
                                     consistent_stack s R <{acq t1 x t2    }>
  | cstack_cr    : forall R' ad t,   R' = R_monitor ad        ->
                                     consistent_stack (push s R') R' t ->
                                     consistent_stack s R <{cr ad t        }>
  | cstack_spawn : forall t,         consistent_stack s R t   ->
                                     consistent_stack s R <{spawn t        }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _cstack tt :=
  match goal with
  | H : consistent_stack _ _ <{unit        }> |- _ => clear H
  | H : consistent_stack _ _ <{nat _       }> |- _ => clear H
  | H : consistent_stack _ _ <{var _       }> |- _ => clear H
  | H : consistent_stack _ _ <{fn _ _ _    }> |- _ => tt H
  | H : consistent_stack _ _ <{call _ _    }> |- _ => tt H
  | H : consistent_stack _ _ <{& _ : _     }> |- _ => tt H
  | H : consistent_stack _ _ <{new _ : _   }> |- _ => tt H
  | H : consistent_stack _ _ <{init _ _ : _}> |- _ => tt H
  | H : consistent_stack _ _ <{* _         }> |- _ => tt H
  | H : consistent_stack _ _ <{_ := _      }> |- _ => tt H
  | H : consistent_stack _ _ <{acq _ _ _   }> |- _ => tt H
  | H : consistent_stack _ _ <{cr _ _      }> |- _ => tt H
  | H : consistent_stack _ _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_cstack  := _cstack inv.
Ltac invc_cstack := _cstack invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma cstack_creg_relation : forall o s R1 R2 t,
  consistent_regions o R1 t -> 
  consistent_stack   s R2 t ->
  R1 = R2.
Proof.
  intros. gendep o. gendep s.
  induction t; intros;
  try solve [invc_creg; invc_cstack; eauto].
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - invc_creg. invc_cstack. eapply IHt.
    +
Qed.

